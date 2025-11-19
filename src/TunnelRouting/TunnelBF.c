#include "TunnelBF.h"
#include <stdlib.h>
#include <stdio.h>

/**
 * @brief Applique une action sur la pile courante.
 *
 * Cette fonction modélise exactement les règles définies dans l'épisode I :
 *  - @b transmit_a : le sommet doit être égal à a, la pile reste identique.
 *  - @b push_b_a   : le sommet doit être égal à a, on ajoute b au sommet.
 *  - @b pop_b_a    : la hauteur doit être >= 1, le sommet doit être b et l'élément en dessous doit être a.
 *
 * @param act        L'action à appliquer (transmit, push ou pop).
 * @param height     Hauteur actuelle de la pile.
 * @param stack      Pile courante.
 * @param new_height Hauteur après l'action (sortie).
 * @param next_stack Copie modifiée de la pile après l'action (sortie).
 *
 * @return 1 si l'action est applicable, 0 sinon.
 */
static int apply_action(stack_action act,
                        int height,
                        int *stack,
                        int *new_height,
                        int *next_stack)
{
    int top = stack[height];

    // Copier la pile courante dans next_stack
    for (int i = 0; i <= height; i++)
        next_stack[i] = stack[i];

    *new_height = height;

    switch (act)
    {
    /* ---------- TRANSMIT ---------- */
    case transmit_4:
        if (top != 4)
            return 0;
        return 1;

    case transmit_6:
        if (top != 6)
            return 0;
        return 1;

    /* ------------ PUSH ------------ */
    case push_4_4:
        if (top != 4)
            return 0;
        *new_height = height + 1;
        next_stack[*new_height] = 4;
        return 1;

    case push_4_6:
        if (top != 4)
            return 0;
        *new_height = height + 1;
        next_stack[*new_height] = 6;
        return 1;

    case push_6_4:
        if (top != 6)
            return 0;
        *new_height = height + 1;
        next_stack[*new_height] = 4;
        return 1;

    case push_6_6:
        if (top != 6)
            return 0;
        *new_height = height + 1;
        next_stack[*new_height] = 6;
        return 1;

    /* ------------ POP ------------ */
    case pop_4_4:
        if (height < 1)
            return 0;
        if (stack[height] != 4 || stack[height - 1] != 4)
            return 0;
        *new_height = height - 1;
        return 1;

    case pop_4_6:
        if (height < 1)
            return 0;
        if (stack[height] != 6 || stack[height - 1] != 4)
            return 0;
        *new_height = height - 1;
        return 1;

    case pop_6_4:
        if (height < 1)
            return 0;
        if (stack[height] != 4 || stack[height - 1] != 6)
            return 0;
        *new_height = height - 1;
        return 1;

    case pop_6_6:
        if (height < 1)
            return 0;
        if (stack[height] != 6 || stack[height - 1] != 6)
            return 0;
        *new_height = height - 1;
        return 1;
    }

    return 0;
}

/**
 * @brief Recherche récursive (DFS) d’un chemin simple valide.
 *
 * Cette fonction explore le réseau tunnel pour trouver un chemin simple
 * satisfaisant les règles de manipulation de pile,
 * pour une longueur maximale donnée.
 *
 * @param net         Le TunnelNetwork.
 * @param node        Noeud courant.
 * @param pos         Profondeur actuelle (nombre d'arêtes déjà parcourues).
 * @param max_length  Longueur maximale autorisée du chemin.
 * @param height      Hauteur actuelle de la pile.
 * @param stack       Pile courante.
 * @param visited     Tableau indiquant quels noeuds ont déjà été visités.
 * @param path        Tableau dans lequel stocker le chemin trouvé.
 *
 * @return 0 si aucun chemin n’est trouvé, sinon la longueur du chemin trouvé.
 */
static int dfs(TunnelNetwork net,
               int node,
               int pos,
               int max_length,
               int height,
               int *stack,
               int *visited,
               tn_step *path)
{
    if (node == tn_get_final(net) && height == 0 && stack[0] == 4)
        return pos;

    if (pos == max_length)
        return 0;

    visited[node] = 1;

    int N = tn_get_num_nodes(net);

    for (int next = 0; next < N; next++)
    {
        if (!tn_is_edge(net, node, next))
            continue;

        if (visited[next])
            continue;

        for (stack_action act = 0; act < NumActions; act++)
        {
            if (!tn_node_has_action(net, node, act))
                continue;

            int next_height;
            int next_stack[256];

            if (!apply_action(act, height, stack, &next_height, next_stack))
                continue;

            path[pos] = tn_step_create(act, node, next);

            int res = dfs(net, next, pos + 1, max_length, next_height, next_stack, visited, path);
            if (res > 0)
            {
                visited[node] = 0;
                return res;
            }
        }
    }

    visited[node] = 0;
    return 0;
}

/**
 * @brief Brute force cherchant le plus court chemin simple valide.
 *
 * Cette version correspond au BONUS 2 :
 * elle teste successivement toutes les longueurs de 1 à @p length
 * et retourne le plus court chemin valable.
 *
 * @param network Le TunnelNetwork.
 * @param length  Longueur maximale à tester.
 * @param path    Tableau dans lequel stocker le chemin trouvé.
 *
 * @return Longueur du plus court chemin trouvé, ou 0 si aucun n’existe.
 */
int tn_brute_force(TunnelNetwork network, int length, tn_step *path)
{
    int visited[256];
    int stack[256];

    int start = tn_get_initial(network);

    for (int L = 1; L <= length; L++)
    {
        stack[0] = 4;

        for (int i = 0; i < 256; i++)
            visited[i] = 0;

        tn_step temp[L];

        int res = dfs(network, start, 0, L, 0, stack, visited, temp);

        if (res == L)
        {
            for (int i = 0; i < L; i++)
                path[i] = temp[i];

            return L;
        }
    }

    return 0;
}
