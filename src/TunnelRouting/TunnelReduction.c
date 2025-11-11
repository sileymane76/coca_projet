#include "TunnelReduction.h"
#include "Z3Tools.h"
#include "stdio.h"

/**
 * @brief Creates the variable "x_{node,pos,stack_height}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param node A node.
 * @param pos The path position.
 * @param stack_height The highest cell occupied of the stack at that position.
 * @return Z3_ast
 */
Z3_ast tn_path_variable(Z3_context ctx, int node, int pos, int stack_height)
{
    char name[60];
    snprintf(name, 60, "node %d,pos %d, height %d", node, pos, stack_height);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Creates the variable "y_{pos,height,4}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_4_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "4 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Creates the variable "y_{pos,height,6}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param pos The path position.
 * @param height The height of the cell described.
 * @return Z3_ast
 */
Z3_ast tn_6_variable(Z3_context ctx, int pos, int height)
{
    char name[60];
    snprintf(name, 60, "6 at height %d on pos %d", height, pos);
    return mk_bool_var(ctx, name);
}

/**
 * @brief Wrapper to have the correct size of the array representing the stack (correct cells of the stack will be from 0 to (get_stack_size(length)-1)).
 *
 * @param length The length of the sought path.
 * @return int
 */
int get_stack_size(int length)
{
    return length / 2 + 1;
}

Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length)
{
    int n = tn_get_num_nodes(network);
    int L = length;
    int H = get_stack_size(length); // Taille de la pile (ajoute cette ligne)

    // Vecteur de clauses
    Z3_ast clauses[10000];
    int clause_count = 0;

    // 1) Unicité : exactement un (node,height) choisi à chaque position i
    // 1) Unicité : exactement un (node,height) choisi à chaque position i
    for (int i = 0; i <= L; i++)
    {
        Z3_ast lits[256];
        int k = 0;
        for (int u = 0; u < n; u++)
        {
            for (int h = 0; h < H; h++) // <- H, pas L
            {
                lits[k++] = tn_path_variable(ctx, u, i, h);
            }
        }
        Z3_ast uniq = uniqueFormula(ctx, lits, k);
        clauses[clause_count++] = uniq;
    }

    // 2) Départ : nœud initial, hauteur 0, pile = [4]
    {
        int s = tn_get_initial(network);
        for (int u = 0; u < n; u++)
        {
            for (int h = 0; h < H; h++)

            {
                Z3_ast var = tn_path_variable(ctx, u, 0, h);
                if (u == s && h == 0)
                    clauses[clause_count++] = var;
                else
                    clauses[clause_count++] = Z3_mk_not(ctx, var);
            }
        }
        // pile = [4] et rien au-dessus
        clauses[clause_count++] = tn_4_variable(ctx, 0, 0);
        clauses[clause_count++] = Z3_mk_not(ctx, tn_6_variable(ctx, 0, 0));
        for (int h = 1; h < H; h++)

        {
            clauses[clause_count++] = Z3_mk_not(ctx, tn_4_variable(ctx, 0, h));
            clauses[clause_count++] = Z3_mk_not(ctx, tn_6_variable(ctx, 0, h));
        }
    }

    // 3) Arrivée : nœud final, hauteur 0
    {
        int d = tn_get_final(network);
        for (int u = 0; u < n; u++)
        {
            for (int h = 0; h < H; h++)

            {
                Z3_ast var = tn_path_variable(ctx, u, L, h);
                if (u == d && h == 0)
                    clauses[clause_count++] = var;
                else
                    clauses[clause_count++] = Z3_mk_not(ctx, var);
            }
        }
    }

    // 4) Adjacence : si (u à i) alors (v à i+1) est un successeur de u
    for (int i = 0; i < L; i++)
    {
        for (int u = 0; u < n; u++)
        {
            Z3_ast antecedent_list[L + 1];
            int a_count = 0;
            for (int h = 0; h < H; h++)

                antecedent_list[a_count++] = tn_path_variable(ctx, u, i, h);
            Z3_ast antecedent = Z3_mk_or(ctx, a_count, antecedent_list);

            Z3_ast consequent_list[L * n];
            int c_count = 0;
            for (int v = 0; v < n; v++)
            {
                if (tn_is_edge(network, u, v))
                {
                    for (int h = 0; h < H; h++)
                        consequent_list[c_count++] = tn_path_variable(ctx, v, i + 1, h);
                }
            }
            if (c_count > 0)
            {
                Z3_ast consequent = Z3_mk_or(ctx, c_count, consequent_list);
                Z3_ast impl = Z3_mk_implies(ctx, antecedent, consequent);
                clauses[clause_count++] = impl;
            }
        }
    }
    /* 5) Variables d'action : exactement une vraie à chaque position (0..L-1) */
    for (int i = 0; i < L; i++)
    {
        Z3_ast act_vars[NumActions];
        int k = 0;
        for (stack_action a = 0; a < NumActions; a++)
        {
            // nom lisible : A(i,a)
            char name[64];
            snprintf(name, 64, "A(i=%d,a=%d)", i, a);
            act_vars[k++] = mk_bool_var(ctx, name);
        }
        Z3_ast uniq = uniqueFormula(ctx, act_vars, k);
        clauses[clause_count++] = uniq;
    }

    /* 6) Compatibilité entre actions et nœuds */
    for (int i = 0; i < L; i++)
    {
        for (int u = 0; u < n; u++)
        {
            for (int h = 0; h < H; h++)

            {
                Z3_ast x_uih = tn_path_variable(ctx, u, i, h);

                // Construit la disjonction des actions que le nœud peut exécuter
                Z3_ast allowed_actions[NumActions];
                int count = 0;
                for (stack_action a = 0; a < NumActions; a++)
                {
                    if (tn_node_has_action(network, u, a))
                    {
                        char name[64];
                        snprintf(name, 64, "A(i=%d,a=%d)", i, a);
                        allowed_actions[count++] = mk_bool_var(ctx, name);
                    }
                }

                if (count > 0)
                {
                    Z3_ast disj = Z3_mk_or(ctx, count, allowed_actions);
                    // Si on est sur le nœud u à la position i, alors une action permise doit être vraie
                    Z3_ast implies = Z3_mk_implies(ctx, x_uih, disj);
                    clauses[clause_count++] = implies;
                }
            }
        }
    }
    /* 7) Cohérence des actions sur la pile */
    for (int i = 0; i < L; i++)
    {
        for (int h = 0; h < H; h++)

        {
            // Les actions push/pop/transmit agissent sur la hauteur h
            for (int b = 0; b < 2; b++)
            { // b = protocole (0=4, 1=6)
                for (int a = 0; a < 2; a++)
                {
                    // Sélection de l'action correspondante
                    stack_action push_act = (b == 0 && a == 0) ? push_4_4 : (b == 0 && a == 1) ? push_4_6
                                                                        : (b == 1 && a == 0)   ? push_6_4
                                                                                               : push_6_6;
                    stack_action pop_act = (b == 0 && a == 0) ? pop_4_4 : (b == 0 && a == 1) ? pop_4_6
                                                                      : (b == 1 && a == 0)   ? pop_6_4
                                                                                             : pop_6_6;

                    // Variables pour push
                    char push_name[64];
                    snprintf(push_name, 64, "A(i=%d,a=%d)", i, push_act);
                    Z3_ast push_var = mk_bool_var(ctx, push_name);
                    char pop_name[64];
                    snprintf(pop_name, 64, "A(i=%d,a=%d)", i, pop_act);
                    Z3_ast pop_var = mk_bool_var(ctx, pop_name);

                    // --- PUSH : si push_x_y, alors pile augmente de 1 et y devient sommet ---
                    if (h < H - 1)
                    {
                        Z3_ast top_before = (a == 0) ? tn_4_variable(ctx, i, h) : tn_6_variable(ctx, i, h);
                        Z3_ast top_after = (b == 0) ? tn_4_variable(ctx, i + 1, h + 1) : tn_6_variable(ctx, i + 1, h + 1);

                        // si push, alors sommet avant = a et nouveau sommet = b
                        Z3_ast conds[2] = {top_before, top_after};
                        Z3_ast rule = Z3_mk_implies(ctx, push_var, Z3_mk_and(ctx, 2, conds));
                        clauses[clause_count++] = rule;
                    }

                    // --- POP : si pop_x_y, alors pile diminue de 1 et y devient sommet ---
                    if (h > 0)
                    {
                        Z3_ast top_before = (a == 0) ? tn_4_variable(ctx, i, h) : tn_6_variable(ctx, i, h);
                        Z3_ast below_before = (b == 0) ? tn_4_variable(ctx, i, h - 1) : tn_6_variable(ctx, i, h - 1);
                        Z3_ast below_after = (b == 0) ? tn_4_variable(ctx, i + 1, h - 1) : tn_6_variable(ctx, i + 1, h - 1);

                        // si pop, alors sommet avant = a et après on retrouve b
                        Z3_ast conds[3] = {top_before, below_before, below_after};
                        Z3_ast rule = Z3_mk_implies(ctx, pop_var, Z3_mk_and(ctx, 3, conds));
                        clauses[clause_count++] = rule;
                    }
                }
            }

            // --- TRANSMIT 4 et 6 : même pile à i et i+1 ---
            for (int proto = 0; proto < 2; proto++)
            {
                stack_action act = (proto == 0) ? transmit_4 : transmit_6;
                char name[64];
                snprintf(name, 64, "A(i=%d,a=%d)", i, act);
                Z3_ast act_var = mk_bool_var(ctx, name);
                Z3_ast eq4 = Z3_mk_eq(ctx, tn_4_variable(ctx, i, h), tn_4_variable(ctx, i + 1, h));
                Z3_ast eq6 = Z3_mk_eq(ctx, tn_6_variable(ctx, i, h), tn_6_variable(ctx, i + 1, h));
                Z3_ast both[2] = {eq4, eq6};
                Z3_ast stable = Z3_mk_and(ctx, 2, both);
                clauses[clause_count++] = Z3_mk_implies(ctx, act_var, stable);
            }
        }
    }
    /* C) Cohérence hauteur / pile :
    - Si on effectue un push : la hauteur augmente de 1
    - Si on effectue un pop  : la hauteur diminue de 1
    - Si on effectue un transmit : la hauteur reste la même

    for (int i = 0; i < L; i++)
    {
        for (int u = 0; u < n; u++)
        {
            for (int h = 0; h < H; h++)
            {

                // --- Définition propre des variables d’action ---
                char name[64];

                snprintf(name, 64, "A(i=%d,a=%d)", i, push_4_4);
                Z3_ast a_push_4_4 = mk_bool_var(ctx, name);

                snprintf(name, 64, "A(i=%d,a=%d)", i, push_4_6);
                Z3_ast a_push_4_6 = mk_bool_var(ctx, name);

                snprintf(name, 64, "A(i=%d,a=%d)", i, push_6_4);
                Z3_ast a_push_6_4 = mk_bool_var(ctx, name);

                snprintf(name, 64, "A(i=%d,a=%d)", i, push_6_6);
                Z3_ast a_push_6_6 = mk_bool_var(ctx, name);

                snprintf(name, 64, "A(i=%d,a=%d)", i, pop_4_4);
                Z3_ast a_pop_4_4 = mk_bool_var(ctx, name);

                snprintf(name, 64, "A(i=%d,a=%d)", i, pop_4_6);
                Z3_ast a_pop_4_6 = mk_bool_var(ctx, name);

                snprintf(name, 64, "A(i=%d,a=%d)", i, pop_6_4);
                Z3_ast a_pop_6_4 = mk_bool_var(ctx, name);

                snprintf(name, 64, "A(i=%d,a=%d)", i, pop_6_6);
                Z3_ast a_pop_6_6 = mk_bool_var(ctx, name);

                snprintf(name, 64, "A(i=%d,a=%d)", i, transmit_4);
                Z3_ast a_trans_4 = mk_bool_var(ctx, name);

                snprintf(name, 64, "A(i=%d,a=%d)", i, transmit_6);
                Z3_ast a_trans_6 = mk_bool_var(ctx, name);

                Z3_ast cur = tn_path_variable(ctx, u, i, h);

                // --- PUSH : aller à hauteur h+1 ---
                if (h < H - 1)
                {
                    Z3_ast next = tn_path_variable(ctx, u, i + 1, h + 1);
                    Z3_ast push_actions[4] = {a_push_4_4, a_push_4_6, a_push_6_4, a_push_6_6};
                    Z3_ast push_cond = Z3_mk_or(ctx, 4, push_actions);
                    Z3_ast imply_parts[2] = {push_cond, next};
                    Z3_ast rule = Z3_mk_implies(ctx, cur, Z3_mk_and(ctx, 2, imply_parts));
                    clauses[clause_count++] = rule;
                }

                // --- POP : aller à hauteur h-1 ---
                if (h > 0)
                {
                    Z3_ast next = tn_path_variable(ctx, u, i + 1, h - 1);
                    Z3_ast pop_actions[4] = {a_pop_4_4, a_pop_4_6, a_pop_6_4, a_pop_6_6};
                    Z3_ast pop_cond = Z3_mk_or(ctx, 4, pop_actions);
                    Z3_ast imply_parts[2] = {pop_cond, next};
                    Z3_ast rule = Z3_mk_implies(ctx, cur, Z3_mk_and(ctx, 2, imply_parts));
                    clauses[clause_count++] = rule;
                }

                // --- TRANSMIT : même hauteur ---
                Z3_ast next_same = tn_path_variable(ctx, u, i + 1, h);
                Z3_ast trans_actions[2] = {a_trans_4, a_trans_6};
                Z3_ast trans_cond = Z3_mk_or(ctx, 2, trans_actions);
                Z3_ast imply_parts[2] = {trans_cond, next_same};
                Z3_ast rule = Z3_mk_implies(ctx, cur, Z3_mk_and(ctx, 2, imply_parts));
                clauses[clause_count++] = rule;
            }
        }
    }
    */
    // φ3 : Cohérence pile (une seule valeur 4 ou 6 par cellule)
    for (int i = 0; i <= L; i++)
    {
        for (int h = 0; h < H; h++)

        {
            Z3_ast v4 = tn_4_variable(ctx, i, h);
            Z3_ast v6 = tn_6_variable(ctx, i, h);
            // Interdiction des deux vrais simultanément
            Z3_ast not_both = Z3_mk_not(ctx, Z3_mk_and(ctx, 2, (Z3_ast[]){v4, v6}));
            clauses[clause_count++] = not_both;
        }
    }
    // φ4 : Au-dessus du sommet, la pile est vide
    for (int i = 0; i <= L; i++)
    {
        for (int h = 0; h < H - 1; h++)
        {
            // Si la cellule (h+1) est occupée par 4 ou 6, alors la cellule h doit l'être aussi
            Z3_ast has4_above = tn_4_variable(ctx, i, h + 1);
            Z3_ast has6_above = tn_6_variable(ctx, i, h + 1);
            Z3_ast has4_here = tn_4_variable(ctx, i, h);
            Z3_ast has6_here = tn_6_variable(ctx, i, h);

            // Interdit d'avoir un symbole au-dessus d'une cellule vide
            Z3_ast cond_above = Z3_mk_or(ctx, 2, (Z3_ast[]){has4_above, has6_above});
            Z3_ast cond_here = Z3_mk_or(ctx, 2, (Z3_ast[]){has4_here, has6_here});
            Z3_ast not_allowed = Z3_mk_implies(ctx, cond_above, cond_here);
            clauses[clause_count++] = not_allowed;
        }
    }

    // Combinaison finale
    Z3_ast formula = Z3_mk_and(ctx, clause_count, clauses);
    return formula;
}

void tn_get_path_from_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound, tn_step *path)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound; pos++)
    {
        int src = -1;
        int src_height = -1;
        int tgt = -1;
        int tgt_height = -1;
        for (int n = 0; n < num_nodes; n++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos, height)))
                {
                    src = n;
                    src_height = height;
                }
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, n, pos + 1, height)))
                {
                    tgt = n;
                    tgt_height = height;
                }
            }
        }
        int action = 0;
        if (src_height == tgt_height)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
                action = transmit_4;
            else
                action = transmit_6;
        }
        else if (src_height == tgt_height - 1)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = push_4_4;
                else
                    action = push_4_6;
            }
            else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                action = push_6_4;
            else
                action = push_6_6;
        }
        else if (src_height == tgt_height + 1)
        {
            {
                if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, src_height)))
                {
                    if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                        action = pop_4_4;
                    else
                        action = pop_6_4;
                }
                else if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos + 1, tgt_height)))
                    action = pop_4_6;
                else
                    action = pop_6_6;
            }
        }
        path[pos] = tn_step_create(action, src, tgt);
    }
}

void tn_print_model(Z3_context ctx, Z3_model model, TunnelNetwork network, int bound)
{
    int num_nodes = tn_get_num_nodes(network);
    int stack_size = get_stack_size(bound);
    for (int pos = 0; pos < bound + 1; pos++)
    {
        printf("At pos %d:\nState: ", pos);
        int num_seen = 0;
        for (int node = 0; node < num_nodes; node++)
        {
            for (int height = 0; height < stack_size; height++)
            {
                if (value_of_var_in_model(ctx, model, tn_path_variable(ctx, node, pos, height)))
                {
                    printf("(%s,%d) ", tn_get_node_name(network, node), height);
                    num_seen++;
                }
            }
        }
        if (num_seen == 0)
            printf("No node at that position !\n");
        else
            printf("\n");
        if (num_seen > 1)
            printf("Several pair node,height!\n");
        printf("Stack: ");
        bool misdefined = false;
        bool above_top = false;
        for (int height = 0; height < stack_size; height++)
        {
            if (value_of_var_in_model(ctx, model, tn_4_variable(ctx, pos, height)))
            {
                if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
                {
                    printf("|X");
                    misdefined = true;
                }
                else
                {
                    printf("|4");
                    if (above_top)
                        misdefined = true;
                }
            }
            else if (value_of_var_in_model(ctx, model, tn_6_variable(ctx, pos, height)))
            {
                printf("|6");
                if (above_top)
                    misdefined = true;
            }
            else
            {
                printf("| ");
                above_top = true;
            }
        }
        printf("\n");
        if (misdefined)
            printf("Warning: ill-defined stack\n");
    }
    return;
}