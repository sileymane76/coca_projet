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
    int N = tn_get_num_nodes(network);
    int H = get_stack_size(length);

    /* Un très grand tableau pour accumuler les contraintes */
    Z3_ast C[300000];
    int k = 0;

    /* Tableau temporaire pour fabriquer des OR/AND */
    Z3_ast tmp[20000];

    /* ===========================================================
     * φ_unicity : unicité du couple (node,height) à chaque position
     * =========================================================== */

    for (int pos = 0; pos <= length; pos++)
    {
        /* ---------------------------
         * (1) Au moins un état possible
         * --------------------------- */
        int a = 0;
        for (int u = 0; u < N; u++)
            for (int h = 0; h < H; h++)
                tmp[a++] = tn_path_variable(ctx, u, pos, h);

        C[k++] = Z3_mk_or(ctx, a, tmp);

        /* ---------------------------
         * (2) Au plus un : on interdit deux états simultanés
         * --------------------------- */
        for (int u1 = 0; u1 < N; u1++)
            for (int h1 = 0; h1 < H; h1++)
                for (int u2 = 0; u2 < N; u2++)
                    for (int h2 = 0; h2 < H; h2++)
                    {
                        if (u1 == u2 && h1 == h2)
                            continue;

                        Z3_ast forbid_args[2] = {
                            Z3_mk_not(ctx, tn_path_variable(ctx, u1, pos, h1)),
                            Z3_mk_not(ctx, tn_path_variable(ctx, u2, pos, h2))};
                        C[k++] = Z3_mk_or(ctx, 2, forbid_args);
                    }
    }
    /* ===========================================================
     * φ_stack_validity : la pile est bien formée
     * =========================================================== */

    for (int pos = 0; pos <= length; pos++)
    {
        for (int h = 0; h < H; h++)
        {
            /* Interdit : y4(pos,h) ET y6(pos,h) */
            Z3_ast both[2] = {
                tn_4_variable(ctx, pos, h),
                tn_6_variable(ctx, pos, h)};
            Z3_ast and_both = Z3_mk_and(ctx, 2, both);

            C[k++] = Z3_mk_not(ctx, and_both);
        }

        /* Pas de trou : si une case est vide, tout au-dessus est vide */
        for (int h = 0; h < H; h++)
        {
            Z3_ast empty_h_args[2] = {
                Z3_mk_not(ctx, tn_4_variable(ctx, pos, h)),
                Z3_mk_not(ctx, tn_6_variable(ctx, pos, h))};
            Z3_ast empty_h = Z3_mk_and(ctx, 2, empty_h_args);

            for (int h2 = h + 1; h2 < H; h2++)
            {
                Z3_ast filled_above = Z3_mk_or(ctx, 2,
                                               (Z3_ast[]){
                                                   tn_4_variable(ctx, pos, h2),
                                                   tn_6_variable(ctx, pos, h2)});

                Z3_ast not_filled = Z3_mk_not(ctx, filled_above);
                C[k++] = Z3_mk_implies(ctx, empty_h, not_filled);
            }
        }
    }

    /* ===========================================================
     * φ_init : état initial + pile initiale
     * =========================================================== */

    int s = tn_get_initial(network);

    /* Le premier état est (s,0) */
    C[k++] = tn_path_variable(ctx, s, 0, 0);

    /* Pile initiale = un 4 en bas, vide au-dessus */
    C[k++] = tn_4_variable(ctx, 0, 0);
    C[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, 0, 0));

    for (int h = 1; h < H; h++)
    {
        C[k++] = Z3_mk_not(ctx, tn_4_variable(ctx, 0, h));
        C[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, 0, h));
    }

    /* ===========================================================
     * φ_final : état final + pile finale
     * =========================================================== */

    int t = tn_get_final(network);

    /* Dernier état = (t,0) */
    C[k++] = tn_path_variable(ctx, t, length, 0);

    /* Pile finale = 4 en bas, vide au-dessus */
    C[k++] = tn_4_variable(ctx, length, 0);
    C[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, length, 0));

    for (int h = 1; h < H; h++)
    {
        C[k++] = Z3_mk_not(ctx, tn_4_variable(ctx, length, h));
        C[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, length, h));
    }
    /* ===========================================================
     * φ_edges : on interdit les transitions (u → v) inexistantes
     * =========================================================== */

    for (int pos = 0; pos < length; pos++)
    {
        for (int u = 0; u < N; u++)
        {
            for (int v = 0; v < N; v++)
            {
                if (!tn_is_edge(network, u, v))
                {
                    /* Interdire : (u,pos,h1) & (v,pos+1,h2) */
                    for (int h1 = 0; h1 < H; h1++)
                    {
                        for (int h2 = 0; h2 < H; h2++)
                        {
                            Z3_ast forbid_args[2] = {
                                Z3_mk_not(ctx, tn_path_variable(ctx, u, pos, h1)),
                                Z3_mk_not(ctx, tn_path_variable(ctx, v, pos + 1, h2))};
                            C[k++] = Z3_mk_or(ctx, 2, forbid_args);
                        }
                    }
                }
            }
        }
    }

    /* ===========================================================
     * φ_simple : un chemin simple (un même nœud ne peut être visité
     *            à deux positions différentes)
     * =========================================================== */

    for (int u = 0; u < N; u++)
    {
        for (int pos1 = 0; pos1 <= length; pos1++)
        {
            for (int pos2 = pos1 + 1; pos2 <= length; pos2++)
            {
                for (int h1 = 0; h1 < H; h1++)
                {
                    for (int h2 = 0; h2 < H; h2++)
                    {
                        /* interdit : (u,pos1,h1) et (u,pos2,h2) */
                        Z3_ast forbid_args[2] = {
                            Z3_mk_not(ctx, tn_path_variable(ctx, u, pos1, h1)),
                            Z3_mk_not(ctx, tn_path_variable(ctx, u, pos2, h2))};
                        C[k++] = Z3_mk_or(ctx, 2, forbid_args);
                    }
                }
            }
        }
    }
    /* ===========================================================
     * φ_transitions — VERSION CORRIGÉE
     * =========================================================== */

    for (int pos = 0; pos < length; pos++)
    {
        for (int u = 0; u < N; u++)
        {
            for (int hs = 0; hs < H; hs++)
            {
                Z3_ast xu = tn_path_variable(ctx, u, pos, hs);

                Z3_ast actions[2000];
                int ac = 0;

                /* ==========================================
                 * TRANSMIT 4
                 * ========================================== */
                if (tn_node_has_action(network, u, transmit_4))
                {
                    if (hs < H)
                    {
                        Z3_ast conds[1000];
                        int c = 0;

                        /* sommet = 4 */
                        conds[c++] = tn_4_variable(ctx, pos, hs);

                        /* même hauteur, edge(u,v) */
                        int a = 0;
                        for (int v = 0; v < N; v++)
                            if (tn_is_edge(network, u, v))
                                tmp[a++] = tn_path_variable(ctx, v, pos + 1, hs);

                        conds[c++] = Z3_mk_or(ctx, a, tmp);

                        /* pile identique */
                        for (int h = 0; h < H; h++)
                        {
                            Z3_ast eq4 = Z3_mk_iff(ctx,
                                                   tn_4_variable(ctx, pos, h),
                                                   tn_4_variable(ctx, pos + 1, h));

                            Z3_ast eq6 = Z3_mk_iff(ctx,
                                                   tn_6_variable(ctx, pos, h),
                                                   tn_6_variable(ctx, pos + 1, h));

                            Z3_ast both[2] = {eq4, eq6};
                            conds[c++] = Z3_mk_and(ctx, 2, both);
                        }

                        actions[ac++] = Z3_mk_and(ctx, c, conds);
                    }
                }

                /* ==========================================
                 * TRANSMIT 6
                 * ========================================== */
                if (tn_node_has_action(network, u, transmit_6))
                {
                    if (hs < H)
                    {
                        Z3_ast conds[1000];
                        int c = 0;

                        conds[c++] = tn_6_variable(ctx, pos, hs);

                        int a = 0;
                        for (int v = 0; v < N; v++)
                            if (tn_is_edge(network, u, v))
                                tmp[a++] = tn_path_variable(ctx, v, pos + 1, hs);

                        conds[c++] = Z3_mk_or(ctx, a, tmp);

                        for (int h = 0; h < H; h++)
                        {
                            Z3_ast eq4 = Z3_mk_iff(ctx,
                                                   tn_4_variable(ctx, pos, h),
                                                   tn_4_variable(ctx, pos + 1, h));
                            Z3_ast eq6 = Z3_mk_iff(ctx,
                                                   tn_6_variable(ctx, pos, h),
                                                   tn_6_variable(ctx, pos + 1, h));

                            Z3_ast both[2] = {eq4, eq6};
                            conds[c++] = Z3_mk_and(ctx, 2, both);
                        }

                        actions[ac++] = Z3_mk_and(ctx, c, conds);
                    }
                }

                /* ==========================================
                 * PUSH
                 * ========================================== */
                for (stack_action act = push_4_4; act <= push_6_6; act++)
                {
                    if (!tn_node_has_action(network, u, act))
                        continue;

                    if (hs + 1 < H)
                    {
                        int hs2 = hs + 1;

                        bool topWas4 = (act == push_4_4 || act == push_4_6);
                        bool pushedIs4 = (act == push_4_4 || act == push_6_4);

                        Z3_ast conds[1000];
                        int c = 0;

                        /* sommet avant push */
                        conds[c++] = topWas4 ? tn_4_variable(ctx, pos, hs) : tn_6_variable(ctx, pos, hs);

                        /* edge(u,v) et (v,pos+1,hs2) */
                        int a = 0;
                        for (int v = 0; v < N; v++)
                            if (tn_is_edge(network, u, v))
                                tmp[a++] = tn_path_variable(ctx, v, pos + 1, hs2);

                        conds[c++] = Z3_mk_or(ctx, a, tmp);

                        /* nouvelle case ajoutée */
                        if (pushedIs4)
                        {
                            conds[c++] = tn_4_variable(ctx, pos + 1, hs2);
                            conds[c++] = Z3_mk_not(ctx, tn_6_variable(ctx, pos + 1, hs2));
                        }
                        else
                        {
                            conds[c++] = tn_6_variable(ctx, pos + 1, hs2);
                            conds[c++] = Z3_mk_not(ctx, tn_4_variable(ctx, pos + 1, hs2));
                        }

                        /* pile inchangée en-dessous */
                        for (int h = 0; h <= hs; h++)
                        {
                            Z3_ast eq4 = Z3_mk_iff(ctx,
                                                   tn_4_variable(ctx, pos, h),
                                                   tn_4_variable(ctx, pos + 1, h));
                            Z3_ast eq6 = Z3_mk_iff(ctx,
                                                   tn_6_variable(ctx, pos, h),
                                                   tn_6_variable(ctx, pos + 1, h));

                            Z3_ast both[2] = {eq4, eq6};
                            conds[c++] = Z3_mk_and(ctx, 2, both);
                        }

                        /* cases au-dessus vides */
                        for (int h = hs2 + 1; h < H; h++)
                        {
                            conds[c++] = Z3_mk_not(ctx, tn_4_variable(ctx, pos + 1, h));
                            conds[c++] = Z3_mk_not(ctx, tn_6_variable(ctx, pos + 1, h));
                        }

                        actions[ac++] = Z3_mk_and(ctx, c, conds);
                    }
                }

                /* ==========================================
                 * POP
                 * ========================================== */
                for (stack_action act = pop_4_4; act <= pop_6_6; act++)
                {
                    if (!tn_node_has_action(network, u, act))
                        continue;
                    if (hs == 0)
                        continue;

                    int hs2 = hs - 1;

                    bool removedWas4 = (act == pop_4_4 || act == pop_6_4);
                    bool newTopIs4 = (act == pop_4_4 || act == pop_4_6);

                    Z3_ast conds[1000];
                    int c = 0;

                    /* sommet avant pop */
                    conds[c++] = removedWas4 ? tn_4_variable(ctx, pos, hs) : tn_6_variable(ctx, pos, hs);

                    /* edge(u,v) */
                    int a = 0;
                    for (int v = 0; v < N; v++)
                        if (tn_is_edge(network, u, v))
                            tmp[a++] = tn_path_variable(ctx, v, pos + 1, hs2);

                    conds[c++] = Z3_mk_or(ctx, a, tmp);

                    /* nouveau sommet après pop */
                    if (newTopIs4)
                    {
                        conds[c++] = tn_4_variable(ctx, pos + 1, hs2);
                        conds[c++] = Z3_mk_not(ctx, tn_6_variable(ctx, pos + 1, hs2));
                    }
                    else
                    {
                        conds[c++] = tn_6_variable(ctx, pos + 1, hs2);
                        conds[c++] = Z3_mk_not(ctx, tn_4_variable(ctx, pos + 1, hs2));
                    }

                    /* pile en-dessous identique */
                    for (int h = 0; h < hs2; h++)
                    {
                        Z3_ast eq4 = Z3_mk_iff(ctx,
                                               tn_4_variable(ctx, pos, h),
                                               tn_4_variable(ctx, pos + 1, h));
                        Z3_ast eq6 = Z3_mk_iff(ctx,
                                               tn_6_variable(ctx, pos, h),
                                               tn_6_variable(ctx, pos + 1, h));

                        Z3_ast both[2] = {eq4, eq6};
                        conds[c++] = Z3_mk_and(ctx, 2, both);
                    }

                    /* cases au-dessus doivent être vides */
                    for (int h = hs2 + 1; h < H; h++)
                    {
                        conds[c++] = Z3_mk_not(ctx, tn_4_variable(ctx, pos + 1, h));
                        conds[c++] = Z3_mk_not(ctx, tn_6_variable(ctx, pos + 1, h));
                    }

                    actions[ac++] = Z3_mk_and(ctx, c, conds);
                }

                /* ==========================================
                 * si x(u,pos,hs) alors OR(actions)
                 * ========================================== */
                if (ac > 0)
                {
                    Z3_ast or_actions = Z3_mk_or(ctx, ac, actions);
                    C[k++] = Z3_mk_implies(ctx, xu, or_actions);
                }
            }
        }
    }

    /* ===========================================================
     * Return : conjonction de toutes les contraintes
     * =========================================================== */

    return Z3_mk_and(ctx, k, C);
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