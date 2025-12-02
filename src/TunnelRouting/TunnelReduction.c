#include "TunnelReduction.h"
#include "Z3Tools.h"
#include "stdio.h"
#include <getopt.h>

/**
 * @brief Creates the variable "x_{node,pos,stack_height}" of the reduction (described in the subject).
 *
 * @param ctx The solver context.
 * @param node A node.
 * @param pos The path position.
 * @param stack_height The highest cell occupied of the stack at that position.
 * @return Z3_ast
 * Cette variable correspond à une phrase logique du type :

« À la position pos du chemin, on se trouve sur le nœud node, avec une pile dont le sommet est à la hauteur stack_height. »

Pour cela, la fonction fabrique d’abord un nom lisible pour la variable, par exemple :

"node 3, pos 5, height 2"

Ce nom permet d’identifier clairement la variable dans les sorties de Z3.

Ensuite, la fonction demande à Z3 de créer une variable booléenne portant ce nom.
Cette variable pourra être vraie ou fausse selon ce que Z3 trouve comme solution.

En résumé :

Cette fonction définit une possibilité d’état du système.

Chaque variable créée indique : « je suis sur tel nœud, à telle position, avec telle hauteur de pile ».

Z3 utilise ensuite toutes ces variables pour construire et résoudre les contraintes.
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
 * Détermine la taille maximale de la pile en fonction de la longueur du chemin.
 *
 * Dans ce problème, les actions push et pop modifient la hauteur de la pile,
 * mais on ne peut pas faire plus d’un push toutes les deux étapes (push puis
 * pop ou transition). La hauteur maximale atteignable est donc limitée.
 *
 * La formule "length / 2 + 1" donne une borne supérieure sur la hauteur de la pile :
 *   - "length / 2" correspond au nombre maximal de push possibles dans un chemin,
 *   - on ajoute 1 pour prendre en compte la hauteur initiale (la pile commence à hauteur 0).
 *
 * Cette fonction permet donc d’allouer le bon nombre de cases pour représenter
 * la pile à chaque position, sans gaspillage et sans risque de dépassement.
 */
int get_stack_size(int length)
{
    return length / 2 + 1;
}
/**
 * @brief Construit toute la formule SAT décrivant un chemin valide.
 *
 * Cette fonction regroupe TOUTES les contraintes du sujet :
 *  - φ_unicity : unicité du couple (node,height) à chaque position
 *  - φ_stack_validity : stack cohérente et sans trous
 *  - φ_init : contraintes d’état initial + pile initiale
 *  - φ_final : contraintes d’état final + pile finale
 *  - φ_edges : respecter les arêtes du graphe
 *  - φ_simple : chemin simple (pas de nœud répété)
 *  - φ_transitions : correspondance exacte avec les règles push/pop/transmit
 *
 * Le résultat est une  conjonction (AND) de toutes ces contraintes.
 *
 * @param ctx      Contexte Z3.
 * @param network  Le TunnelNetwork analysé.
 * @param length   Longueur exacte du chemin cherché.
 *
 * @return La formule Z3 (conjonction de toutes les contraintes).
 */

Z3_ast tn_reduction(Z3_context ctx, const TunnelNetwork network, int length)
{
    /**
     * On détermine :
     * - N : le nombre total de nœuds dans le réseau.
     * - H : la hauteur maximale possible de la pile pour un chemin de cette longueur.
     */

    /*
     * Ce tableau C va contenir TOUTES les contraintes de la formule finale Z3.
     * On le fait très grand (300000 cases) pour pouvoir accumuler sans risque
     * toutes les clauses logiques (AND, OR, implications, etc.) que l’on va générer.
     *
     * Chaque entrée C[k] est un Z3_ast représentant une sous-formule logique.
     * À la fin du processus, elles seront combinées dans un énorme AND global.
     * * Tableau temporaire utilisé pour construire des expressions logiques
     * du type OR(...) ou AND(...).
     *
     * Exemple :
     *    tmp[0] = x1;
     *    tmp[1] = x2;
     *    tmp[2] = x3;
     *    Z3_mk_or(ctx, 3, tmp);
     *
     * On évite ainsi de réallouer un tableau à chaque fois.
     */
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
        /**---------------------------

     * --------------------------------------------------------------------
     * (1) CONTRAINTE "AU MOINS UN"
     * --------------------------------------------------------------------
     * À chaque position du chemin (pos), on doit choisir AU MOINS UN état
     * composé :
     *     - d’un nœud u
     *     - d’une hauteur de pile h
     *
     * On liste donc toutes les variables x[u, pos, h], et on fait un OR dessus.
     *
     * Cela exprime logiquement :
     *     (x[u1,pos,h1] OR x[u2,pos,h2] OR ... OR x[uN,pos,hH]) = TRUE
     *
     * → Donc Z3 doit rendre vrai au moins un de ces états.
     */
        int a = 0;
        for (int u = 0; u < N; u++)
            for (int h = 0; h < H; h++)
                tmp[a++] = tn_path_variable(ctx, u, pos, h);

        C[k++] = Z3_mk_or(ctx, a, tmp);

        /**
         * --------------------------------------------------------------------
         * (2) CONTRAINTE "AU PLUS UN"
         * --------------------------------------------------------------------
         * On interdit que DEUX états différents soient vrais en même temps
         * pour une même position pos.
         *
         * Pour cela, on parcourt toutes les paires distinctes :
         *      (u1, h1) ≠ (u2, h2)
         *
         * Et pour chaque paire on ajoute la contrainte :
         *      ¬x[u1,pos,h1] OR ¬x[u2,pos,h2]
         *
         * Cette clause interdit à Z3 de rendre "vraies" deux variables
         * représentant deux états différents au même moment.
         *
         * En logique :
         *      (xA → ¬xB) et (xB → ¬xA)
         *
         * Au final :
         *      → il y aura EXACTEMENT UN état par position.
         *         (car on a déjà "au moins un" au-dessus)
         */
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
        /**********************************************************************
         * (1) COHÉRENCE DES CELLULES DE LA PILE : UNE CASE = AU MAXIMUM UN SYMBOLE
         **********************************************************************
         * Pour chaque position 'pos' et pour chaque hauteur 'h' de la pile :
         *    - on interdit que les deux variables y4(pos,h) et y6(pos,h)
         *      soient vraies en même temps.
         *
         * Autrement dit :
         *      PAS ( y4(pos,h) ET y6(pos,h) )
         *
         * Cela garantit qu'une cellule de la pile ne peut contenir
         * qu'un seul symbole : soit 4, soit 6, soit rien.
         **********************************************************************/
        for (int h = 0; h < H; h++)
        {

            Z3_ast both[2] = {
                tn_4_variable(ctx, pos, h),
                tn_6_variable(ctx, pos, h)};
            Z3_ast and_both = Z3_mk_and(ctx, 2, both);

            C[k++] = Z3_mk_not(ctx, and_both);
        }

        /**********************************************************************
         * (2) STRUCTURE DE PILE SANS TROU
         **********************************************************************
         * Une pile correcte doit être "compacte" :
         *
         *     si une cellule à la hauteur h est vide,
         *     alors TOUTES les cellules au-dessus (h+1, h+2, ...) doivent être vides.
         *
         * En logique :
         *     empty(pos,h)  →  empty(pos,h+1)
         *     empty(pos,h)  →  empty(pos,h+2)
         *     empty(pos,h)  →  ...
         *
         * où :
         *     empty(pos,h) = (¬y4(pos,h) ET ¬y6(pos,h))
         *
         * Cela empêche des formes du type :
         *       |   ← vide
         *       | 4 ← rempli (INTERDIT)
         **********************************************************************/
        for (int h = 0; h < H; h++)
        {
            /* Définir "empty(pos, h)" = la case h est vide */
            Z3_ast empty_h_args[2] = {
                Z3_mk_not(ctx, tn_4_variable(ctx, pos, h)),
                Z3_mk_not(ctx, tn_6_variable(ctx, pos, h))};
            Z3_ast empty_h = Z3_mk_and(ctx, 2, empty_h_args);
            /* Pour chaque case située AU-DESSUS (h2 > h) */
            for (int h2 = h + 1; h2 < H; h2++)
            {
                /* filled_above = y4(pos,h2) OR y6(pos,h2)
                 * Signifie : "la case h2 contient un symbole"
                 */
                Z3_ast filled_above = Z3_mk_or(ctx, 2,
                                               (Z3_ast[]){
                                                   tn_4_variable(ctx, pos, h2),
                                                   tn_6_variable(ctx, pos, h2)});
                /* NOT filled_above = la case h2 est vide */
                Z3_ast not_filled = Z3_mk_not(ctx, filled_above);
                /* Clause : empty(pos,h) → empty(pos,h2)
                 *          (si h est vide, alors h2 doit être vide)
                 */
                C[k++] = Z3_mk_implies(ctx, empty_h, not_filled);
            }
        }
    }

    /* ===========================================================
     * φ_init : état initial + pile initiale
     * =========================================================== */

    /* ----------------------------------------------------------
     * (1) Condition d’état initial :
     *     On impose que le chemin commence au nœud initial s,
     *     avec une hauteur de pile égale à 0.
     * ---------------------------------------------------------- */
    int s = tn_get_initial(network);

    /* Le premier état est (s,0) */
    C[k++] = tn_path_variable(ctx, s, 0, 0);

    /* Pile initiale = un 4 en bas, vide au-dessus */
    /* ----------------------------------------------------------
     * (2) Contenu initial de la pile :
     *     - La case 0 contient le symbole 4
     *     - Elle ne contient PAS le symbole 6
     * ---------------------------------------------------------- */
    C[k++] = tn_4_variable(ctx, 0, 0);
    C[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, 0, 0));

    /* ----------------------------------------------------------
     * (3) Toutes les autres cases de la pile (1..H-1) sont vides.
     *     Cela crée une pile bien définie au départ :
     *          hauteur = 0
     *          contenu = [4]
     * ---------------------------------------------------------- */
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
    /* ----------------------------------------------------------
     * (1) Condition d’état final :
     *     On impose que le chemin se termine au nœud final t,
     *     et que la hauteur de la pile soit exactement 0.
     * ---------------------------------------------------------- */
    C[k++] = tn_path_variable(ctx, t, length, 0);

    /* Pile finale = 4 en bas, vide au-dessus */
    /* ----------------------------------------------------------
     * (2) Pile finale :
     *     - La case 0 contient le symbole 4
     *     - Elle ne contient PAS le symbole 6
     *
     *     On impose ainsi que la pile se termine exactement
     *     comme elle a commencé.
     * ---------------------------------------------------------- */
    C[k++] = tn_4_variable(ctx, length, 0);
    C[k++] = Z3_mk_not(ctx, tn_6_variable(ctx, length, 0));

    /* ----------------------------------------------------------
     * (3) Toutes les cases au-dessus (1..H-1) doivent être vides.
     *     Cela signifie que la hauteur finale est bien 0
     *     et qu’aucun élément résiduel ne reste dans la pile.
     * ---------------------------------------------------------- */
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
            /* Si le graphe n’a PAS d’arête u → v,
               alors il est interdit de passer de u à v
               entre les positions pos et pos+1. */
            for (int v = 0; v < N; v++)
            {
                if (!tn_is_edge(network, u, v))
                {
                    /* Interdire : (u,pos,h1) & (v,pos+1,h2) */
                    /* On interdit toutes les combinaisons de hauteurs possibles :
                x(u,pos,h1) AND x(v,pos+1,h2) est impossible. */
                    for (int h1 = 0; h1 < H; h1++)
                    {
                        for (int h2 = 0; h2 < H; h2++)
                        {
                            /* Clause : ¬x(u,pos,h1) OR ¬x(v,pos+1,h2)
                           (interdit que les deux soient vrais simultanément) */
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
                        /* Clause : ¬x(u,pos,h1) OR ¬x(v,pos+1,h2)
                           (interdit que les deux soient vrais simultanément) */
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
                /* ------------------------------------------------------------
                 * Variable représentant l’état courant :
                 *   xu = "à la position pos, je suis sur le nœud u,
                 *         avec une pile de hauteur hs".
                 * ------------------------------------------------------------ */
                Z3_ast xu = tn_path_variable(ctx, u, pos, hs);

                /* ------------------------------------------------------------
                 * Tableau des actions autorisées pour ce nœud u.
                 * On va ajouter dans 'actions' toutes les actions que
                 * le nœud u est capable d’exécuter (push, pop ou transmit).
                 * ------------------------------------------------------------ */

                Z3_ast actions[2000];
                int ac = 0;

                /* ==========================================
                 * TRANSMIT 4
                 * ========================================== */

                /* ------------------------------------------------------------
                 * Conditions nécessaires pour effectuer l’action transmit_4
                 * ------------------------------------------------------------ */
                if (tn_node_has_action(network, u, transmit_4))
                {
                    if (hs < H)
                    {
                        Z3_ast conds[1000];
                        int c = 0;

                        /* sommet = 4 */
                        /* 1) Le sommet de la pile doit être un 4 */
                        conds[c++] = tn_4_variable(ctx, pos, hs);

                        /* même hauteur, edge(u,v) */
                        /* 2) L’état suivant doit être un successeur de u,
                             à la même hauteur hs */
                        int a = 0;
                        for (int v = 0; v < N; v++)
                            if (tn_is_edge(network, u, v))
                                tmp[a++] = tn_path_variable(ctx, v, pos + 1, hs);

                        conds[c++] = Z3_mk_or(ctx, a, tmp);
                        /* 3) La pile reste strictement identique entre pos et pos+1 */
                        /* pile identique */
                        for (int h = 0; h < H; h++)
                        {
                            /* Égalité du bit "4" à la case h */
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
                        /* Ajout de la formule complète de transmit_4
                         * dans la liste des actions possibles à cette position. */

                        actions[ac++] = Z3_mk_and(ctx, c, conds);
                    }
                }

                /* ==========================================
                 * PUSH
                 * ========================================== */
                for (stack_action act = push_4_4; act <= push_6_6; act++)
                {
                    /* Si l’action push n’est pas disponible sur ce nœud, on ignore */
                    if (!tn_node_has_action(network, u, act))
                        continue;
                    /* Un push augmente la hauteur : on vérifie que hs+1 reste dans la pile */
                    if (hs + 1 < H)
                    {
                        int hs2 = hs + 1;
                        /* Détermination du symbole du sommet avant push,
                             et du symbole ajouté après push */
                        /* Détermine la valeur du sommet AVANT le push.
                         * Pour push_4_4 et push_4_6, le sommet doit être un 4.
                         * Pour push_6_4 et push_6_6, le sommet doit être un 6.
                         */

                        bool topWas4 = (act == push_4_4 || act == push_4_6);
                        /* Détermine la valeur du symbole AJOUTÉ dans la nouvelle case.
                         * Pour push_4_4 et push_6_4, on pousse un 4.
                         * Pour push_4_6 et push_6_6, on pousse un 6.
                         */
                        bool pushedIs4 = (act == push_4_4 || act == push_6_4);

                        Z3_ast conds[1000];
                        int c = 0;

                        /* sommet avant push */
                        /* 1) Le sommet AVANT push doit avoir la bonne valeur * Condition sur le sommet AVANT le push :
                         *    - si l’action push nécessite que le sommet soit 4 (topWas4 == true),
                         *      alors on impose y4(pos, hs) = vrai.
                         *    - sinon, le sommet doit être 6, donc y6(pos, hs) = vrai.
                         *
                         * Cela encode la sémantique de push_x_y :
                         *      push_4_4, push_4_6  → sommet avant = 4
                         *      push_6_4, push_6_6  → sommet avant = 6*/
                        conds[c++] = topWas4 ? tn_4_variable(ctx, pos, hs) : tn_6_variable(ctx, pos, hs);

                        /* edge(u,v) et (v,pos+1,hs2) */
                        /* -------------------------------------------------------------
                         * (2) Après le push, le chemin doit aller vers un successeur v
                         *     du nœud u dans le réseau, à la nouvelle hauteur hs2.
                         *
                         * On construit donc :
                         *      OR  {  x(v, pos+1, hs2)  |  u → v est une arête  }
                         *
                         * Ce OR garantit qu’à pos+1, l’état choisi se trouve bien
                         * sur l’un des voisins accessibles depuis u.
                         * ------------------------------------------------------------- */
                        int a = 0;
                        for (int v = 0; v < N; v++)
                            if (tn_is_edge(network, u, v))
                                tmp[a++] = tn_path_variable(ctx, v, pos + 1, hs2);

                        conds[c++] = Z3_mk_or(ctx, a, tmp);

                        /* nouvelle case ajoutée */
                        /* -----------------------------------------------------------
                         * (3) Contenu de la nouvelle case créée par le push.
                         *
                         * pushedIs4 indique si l’action push ajoute un 4 ou un 6 :
                         *   - si pushedIs4 == true  → la nouvelle case doit contenir 4
                         *   - sinon                  → elle doit contenir 6
                         *
                         * Ici, cas où pushedIs4 == true :
                         *     la cellule (pos+1, hs2) doit valoir 4,
                         *     et ne doit PAS valoir 6.
                         * ----------------------------------------------------------- */
                        if (pushedIs4)
                        {
                            /* La nouvelle case contient un 4 */
                            conds[c++] = tn_4_variable(ctx, pos + 1, hs2);
                            /* Elle ne doit pas contenir un 6 */
                            conds[c++] = Z3_mk_not(ctx, tn_6_variable(ctx, pos + 1, hs2));
                        }
                        else
                        {
                            conds[c++] = tn_6_variable(ctx, pos + 1, hs2);
                            conds[c++] = Z3_mk_not(ctx, tn_4_variable(ctx, pos + 1, hs2));
                        }

                        /* pile inchangée en-dessous */
                        /* -----------------------------------------------------------
                         * (4) Toutes les cases en-dessous du nouvel élément (0..hs)
                         *     doivent rester strictement identiques après le push.
                         *
                         * Pour chaque hauteur h ≤ hs, on impose :
                         *
                         *     y4(pos,h) ↔ y4(pos+1,h)
                         *     y6(pos,h) ↔ y6(pos+1,h)
                         *
                         * Autrement dit, la valeur de la cellule h ne change PAS.
                         * ----------------------------------------------------------- */
                        for (int h = 0; h <= hs; h++)
                        {
                            /* Égalité du bit "4" entre pos et pos+1 */
                            Z3_ast eq4 = Z3_mk_iff(ctx,
                                                   tn_4_variable(ctx, pos, h),
                                                   tn_4_variable(ctx, pos + 1, h));
                            Z3_ast eq6 = Z3_mk_iff(ctx,
                                                   tn_6_variable(ctx, pos, h),
                                                   tn_6_variable(ctx, pos + 1, h));
                            /* Les deux contraintes doivent être vraies */

                            Z3_ast both[2] = {eq4, eq6};
                            conds[c++] = Z3_mk_and(ctx, 2, both);
                        }

                        /* cases au-dessus vides */
                        /* -----------------------------------------------------------
                         * (5) Toutes les cases au-dessus de la nouvelle hauteur hs2
                         *     doivent être vides.
                         *
                         * En effet, après un push, la pile a exactement hs2+1 cases
                         * valides : de 0 à hs2.
                         *
                         * Pour toute hauteur h > hs2 :
                         *      - la case ne doit PAS contenir 4
                         *      - la case ne doit PAS contenir 6
                         * ----------------------------------------------------------- */

                        for (int h = hs2 + 1; h < H; h++)
                        {
                            /* Case h : interdit d'avoir un 4 */
                            conds[c++] = Z3_mk_not(ctx, tn_4_variable(ctx, pos + 1, h));
                            /* Case h : interdit d'avoir un 6 */
                            conds[c++] = Z3_mk_not(ctx, tn_6_variable(ctx, pos + 1, h));
                        }

                        actions[ac++] = Z3_mk_and(ctx, c, conds);
                    }
                }

                /* ==========================================
                 * POP
                 * ========================================== */
                /* -------------------------------------------------------------
                 * Parcours de toutes les actions pop possibles :
                 *     pop_4_4, pop_4_6, pop_6_4, pop_6_6
                 * ------------------------------------------------------------- */
                for (stack_action act = pop_4_4; act <= pop_6_6; act++)
                {
                    /* Si ce nœud n’autorise pas ce pop, on passe au suivant */
                    if (!tn_node_has_action(network, u, act))
                        continue;
                    /* Impossible de pop si la pile est déjà de hauteur 0 */
                    if (hs == 0)
                        continue;
                    /* Hauteur après pop */

                    int hs2 = hs - 1;
                    /* Détermine le symbole supprimé au sommet avant pop :
                           pop_4_x → on enlève un 4
                           pop_6_x → on enlève un 6
                         */
                    bool removedWas4 = (act == pop_4_4 || act == pop_6_4);
                    /* Détermine le symbole qui devient le nouveau sommet :
                     pop_x_4 → le nouveau sommet est 4
                     pop_x_6 → le nouveau sommet est 6
                     */
                    bool newTopIs4 = (act == pop_4_4 || act == pop_4_6);
                    /* Liste des contraintes de cette action pop */

                    Z3_ast conds[1000];
                    int c = 0;

                    /* sommet avant pop */
                    /* ---------------------------------------------------------------
                     * (1) Condition sur le sommet AVANT le pop :
                     *     removedWas4 indique si l’action retire un 4 ou un 6.
                     *     On impose donc :
                     *         - si removedWas4 == true  → sommet = 4
                     *         - sinon                   → sommet = 6
                     * --------------------------------------------------------------- */
                    conds[c++] = removedWas4 ? tn_4_variable(ctx, pos, hs) : tn_6_variable(ctx, pos, hs);

                    /* edge(u,v) */
                    /* ---------------------------------------------------------------
                     * (2) Déplacement dans le graphe :
                     *     Après un pop sur u, le chemin doit aller vers un successeur v.
                     *     On construit donc un OR de toutes les variables
                     *         x(v, pos+1, hs2)
                     *     pour chaque v tel que u → v est une arête du graphe.
                     * --------------------------------------------------------------- */
                    int a = 0;
                    for (int v = 0; v < N; v++)
                        if (tn_is_edge(network, u, v))
                            tmp[a++] = tn_path_variable(ctx, v, pos + 1, hs2);
                    /* Au moins un successeur doit être choisi */

                    conds[c++] = Z3_mk_or(ctx, a, tmp);

                    /* nouveau sommet après pop */
                    /* ---------------------------------------------------------------
                     * (3) Définition du nouveau sommet après le pop.
                     *
                     * newTopIs4 indique le symbole qui doit devenir le sommet
                     * une fois que la case hs a été retirée.
                     *
                     * Si newTopIs4 == true :
                     *      la case (pos+1, hs2) contient 4 et pas 6.
                     *
                     * Sinon :
                     *      la case (pos+1, hs2) contient 6 et pas 4.
                     * --------------------------------------------------------------- */
                    if (newTopIs4)
                    {
                        /* Nouveau sommet = 4 */
                        conds[c++] = tn_4_variable(ctx, pos + 1, hs2);
                        conds[c++] = Z3_mk_not(ctx, tn_6_variable(ctx, pos + 1, hs2));
                    }
                    else
                    {
                        /* Nouveau sommet = 6 */
                        conds[c++] = tn_6_variable(ctx, pos + 1, hs2);
                        conds[c++] = Z3_mk_not(ctx, tn_4_variable(ctx, pos + 1, hs2));
                    }

                    /* pile en-dessous identique */
                    /* -------------------------------------------------------------
                     * (4) Les cases situées sous le nouveau sommet (0..hs2-1)
                     *     doivent rester parfaitement identiques après le pop.
                     *
                     * Pour chaque hauteur h < hs2, on impose :
                     *
                     *     y4(pos,h) ↔ y4(pos+1,h)
                     *     y6(pos,h) ↔ y6(pos+1,h)
                     *
                     * Ainsi, le pop ne modifie que la case du sommet et n'affecte
                     * en rien la partie inférieure de la pile.
                     * ------------------------------------------------------------- */
                    for (int h = 0; h < hs2; h++)
                    { /* Égalité des valeurs concernant le 4 à la case h */
                        Z3_ast eq4 = Z3_mk_iff(ctx,
                                               tn_4_variable(ctx, pos, h),
                                               tn_4_variable(ctx, pos + 1, h));
                        /* Égalité des valeurs concernant le 6 à la case h */
                        Z3_ast eq6 = Z3_mk_iff(ctx,
                                               tn_6_variable(ctx, pos, h),
                                               tn_6_variable(ctx, pos + 1, h));
                        /* Les deux conditions doivent être satisfaites */

                        Z3_ast both[2] = {eq4, eq6};
                        conds[c++] = Z3_mk_and(ctx, 2, both);
                    }

                    /* cases au-dessus doivent être vides */
                    /* ---------------------------------------------------------------
                     * (5) Toutes les cases situées au-dessus du nouveau sommet hs2
                     *     doivent être vides après le pop.
                     *
                     * Un pop réduit la hauteur de 1 :
                     *     avant : hauteurs valides = 0..hs
                     *     après : hauteurs valides = 0..hs2 (où hs2 = hs - 1)
                     *
                     * Donc toute case h > hs2 doit être vide :
                     *     - pas de 4
                     *     - pas de 6
                     * --------------------------------------------------------------- */
                    for (int h = hs2 + 1; h < H; h++)
                    {
                        /* Interdit que la case contienne un 4 */
                        conds[c++] = Z3_mk_not(ctx, tn_4_variable(ctx, pos + 1, h));
                        /* Interdit que la case contienne un 6 */
                        conds[c++] = Z3_mk_not(ctx, tn_6_variable(ctx, pos + 1, h));
                    }
                    /* ---------------------------------------------------------------
                     * Ajout de l’action pop complète (conjonction de toutes les
                     * contraintes) dans la liste des actions possibles à pos.
                     * --------------------------------------------------------------- */

                    actions[ac++] = Z3_mk_and(ctx, c, conds);
                }

                /* ==========================================
                 * si x(u,pos,hs) alors OR(actions)

                 * ========================================== */
                /* ---------------------------------------------------------------
                 * Si au moins une action est compatible avec l’état (u,pos,hs),
                 * alors on crée la disjonction de toutes ces actions.
                 *
                 * Puis on impose :
                 *
                 *         x(u,pos,hs)  →  (action1 ∨ action2 ∨ ... ∨ action_ac)
                 *
                 * Cette implication garantit que chaque état choisi dans le
                 * modèle s’accompagne d’au moins une action conforme à la
                 * sémantique du nœud et de la pile.
                 * --------------------------------------------------------------- */
                if (ac > 0)
                {
                    /* OR de toutes les actions possibles */
                    Z3_ast or_actions = Z3_mk_or(ctx, ac, actions);
                    /* Implication : si l’état est vrai → une action doit être prise */
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
/**
 * @brief Reconstruit le chemin depuis un modèle satisfaisable.
 *
 * Cette fonction lit les variables x(u,pos,h) et y(pos,h,val) du modèle Z3
 * pour déterminer :
 *   - à chaque position pos, le nœud courant,
 *   - la hauteur de pile courante,
 *   - l'action appliquée pour aller à la position suivante.
 *
 * Le chemin ainsi reconstruit est stocké dans le tableau 'path'.
 *
 * @param ctx Contexte Z3.
 * @param model Modèle retourné par Z3.
 * @param network Réseau Tunnel.
 * @param bound Longueur du chemin.
 * @param path Tableau dans lequel enregistrer le chemin.
 */

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
/**
 * @brief Affiche le modèle SAT sous une forme lisible.
 *
 * Cette fonction affiche :
 *   - à chaque position pos : le couple (node,height),
 *   - la pile complète (cases 4 / 6 / vides),
 *   - des avertissements en cas de pile incohérente.
 *
 * Utile uniquement pour le débogage et lorsque l’option -M est activée.
 *
 * @param ctx Contexte Z3.
 * @param model Modèle retourné par Z3.
 * @param network Réseau Tunnel.
 * @param bound Longueur du chemin.
 */
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