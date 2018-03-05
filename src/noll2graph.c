/**************************************************************************
 *
 *  SPEN decision procedure
 *
 *  you can redistribute it and/or modify it under the terms of the GNU
 *  Lesser General Public License as published by the Free Software
 *  Foundation, version 3.
 *
 *  It is distributed in the hope that it will be useful,
 *  but WITHOUT ANY WARRANTY; without even the implied warranty of
 *  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *  GNU Lesser General Public License for more details.
 *
 *  See the GNU Lesser General Public License version 3.
 *  for more details (enclosed in the file LICENSE).
 *
 **************************************************************************/

/**
 * Translation of formulas to graphs.
 */

#include "noll2graph.h"
#include "noll2bool.h"

/**
 * @brief Compute the number of nodes from the pure formula.
 * 
 * @param phi input formula
 * @param vars array of size locs_array, giving the labeling of variables
 * @return number of nodes = number of equivalence classes
 */
uint_t
noll_nodes_of_form (noll_form_t * phi, uint_t * vars)
{
  uint_t nodes_size = 0;
  if (phi->pure)
    {
      for (uint_t i = 0; i < phi->pure->size; i++)
        {
          // search the first variable equal to this one
          uint_t min = 0;
          for (min = 0; min < i; min++)
            if (phi->pure->m[min][i - min] == NOLL_PURE_EQ)
              break;
          if (min == i)
            {
              // set node in the locs_vars
              vars[i] = nodes_size;
              nodes_size++;
            }
          else
            vars[i] = vars[min];
        }
    }
  else
    {
      // there are no equalities, set to number of variables
      nodes_size = noll_vector_size (phi->lvars);
      // each variable is associated to a node
      for (uint_t i = 0; i < noll_vector_size (phi->lvars); i++)
        vars[i] = i;
    }
  return nodes_size;
}

/**
 * @brief Counts the number of atoms of kind @p op in @p phi.
 * 
 * Loops are counted in @p nloop as two edges 
 * only if @p isMatrix is true and @p op is NOLL_SPACE_LS.
 * 
 * @param phi      Formula analysed
 * @param isMatrix True if @p phi is a predicate matrix
 * @param op       Kind of formula to be counted
 * @param nloop    Number of loops of list segments
 */
uint_t
noll_atom_of_form (noll_space_t * phi, bool isMatrix,
                   noll_space_op_t op, uint_t * nloop)
{
  uint_t res = 0;
  if (!phi)
    return res;
  if (op == NOLL_SPACE_PTO && phi->kind == op)
    return noll_vector_size (phi->m.pto.fields);
  if (op == NOLL_SPACE_PTO &&
      phi->kind == NOLL_SPACE_LS && phi->m.ls.is_loop == true)
    return (isMatrix == false) ? 1 : 0;
  if (op == NOLL_SPACE_LS && phi->kind == op)
    {
      if (phi->m.ls.is_loop == true)
        {
          /// increment @p nloop if @p not isMatrix
          assert (NULL != nloop);
          *nloop = *nloop + ((isMatrix == false) ? 1 : 0);
          /// always 1 list segment
          return 1;
        }
      else if (strncmp (noll_pred_name (phi->m.ls.pid), "dll", 3) == 0)
        {
          assert (noll_vector_size (phi->m.ls.args) >= 4);
          uint_t fst = noll_vector_at (phi->m.ls.args, 0);
          uint_t bk = noll_vector_at (phi->m.ls.args, 1);
          uint_t prv = noll_vector_at (phi->m.ls.args, 2);
          uint_t nxt = noll_vector_at (phi->m.ls.args, 3);
          /// remove ls edges between equal variables
          /// because only acyclic predicates are allowed
          return ((fst == nxt) && (bk == prv)) ? 0 : 1;
        }
      else
        {
          /// remove ls edges between equal variables
          /// because only acyclic predicates are allowed
    	  uint_t src = noll_vector_at (phi->m.ls.args, 0);
          uint_t dst = noll_vector_at (phi->m.ls.args, 1);
          return (src == dst) ? 0 : 1;
        }
    }
  if (phi->kind != NOLL_SPACE_WSEP && phi->kind != NOLL_SPACE_SSEP)
    return res;
  // else recursive call over separated formula
  if (phi->m.sep)
    {
      for (uint_t i = 0; i < noll_vector_size (phi->m.sep); i++)
        res +=
          noll_atom_of_form (noll_vector_at (phi->m.sep, i), isMatrix, op,
                             nloop);
    }
  return res;
}

/**
 * @brief Compute the edges and the strong separation information.
 * 
 * @param phi    formulas to be translated
 * @param g      graph to be filled
 * @param nedge  start id to be assigned to edges in this formula
 * @param lnode  last auxiliary node used (for loops encoding)
 * @return array of identifiers of edges generated from phi
 */
noll_uid_array *
noll_graph_of_space (noll_space_t * phi, bool isMatrix,
                     noll_graph_t * g, uint_t nedges, uint_t * lnode)
{
  noll_uid_array *res = NULL;
  if (!phi)
    return res;

  switch (phi->kind)
    {
    case NOLL_SPACE_EMP:
    case NOLL_SPACE_JUNK:
      {
        res = noll_uid_array_new ();
        break;
      }
    case NOLL_SPACE_PTO:
      {
        res = noll_uid_array_new ();
        noll_uid_array_reserve (res, noll_vector_size (phi->m.pto.fields));
        /// source node
        uint_t nsrc = g->var2node[phi->m.pto.sid];
        /// to each pto formula correspond several edges
        for (uint_t i = 0; i < noll_vector_size (phi->m.pto.fields); i++)
          {
            uint_t fi = noll_vector_at (phi->m.pto.fields, i);
            uint_t ndst = g->var2node[noll_vector_at (phi->m.pto.dest, i)];
            assert (ndst < g->nodes_size);
            // build the edge
            noll_edge_t *e = noll_edge_alloc (NOLL_EDGE_PTO, nsrc, ndst, fi);
            e->id = nedges + i;
            // push edge in graph
            noll_edge_array_push (g->edges, e);
            // push its identifier in the result
            noll_uid_array_push (res, e->id);
            // push the edge id in the matrix at entry nsrc
            noll_uid_array *src_edges = g->mat[nsrc];
            if (src_edges == NULL)
              {
                src_edges = g->mat[nsrc] = noll_uid_array_new ();
              }
            noll_uid_array_push (src_edges, e->id);
            // push the edge id in the reverse matrix at entry ndst
            noll_uid_array *dst_edges = g->rmat[ndst];
            if (dst_edges == NULL)
              {
                dst_edges = g->rmat[ndst] = noll_uid_array_new ();
              }
            noll_uid_array_push (dst_edges, e->id);
          }
        break;
      }
    case NOLL_SPACE_LS:
      {
        /// resulting array of edge identifiers
        res = noll_uid_array_new ();
        noll_uid_array_reserve (res, noll_vector_size (phi->m.ls.args));
        /// source node
        uint_t nsrc = g->var2node[noll_vector_at (phi->m.ls.args, 0)];
        assert (nsrc < g->nodes_size);
        /// destination node, if any otherwise 'nil'
        uint_t ndst = (noll_pred_isUnaryLoc (phi->m.ls.pid) == true) ?
          g->var2node[0] : g->var2node[noll_vector_at (phi->m.ls.args, 1)];
        assert (ndst < g->nodes_size);
        bool isDLL =
          (strncmp (noll_pred_name (phi->m.ls.pid), "dll", 3) ==
           0) ? true : false;
        /// one direction list segments
        if (!isDLL && (nsrc == ndst))
          {
            /// simple case, no loop
            if (phi->m.ls.is_loop == false)
              {
                /// empty list segment, 
                /// see the base rules of this predicate 
                /// to push the data constraint
                const noll_pred_t *pred = noll_pred_getpred (phi->m.ls.pid);
                assert (noll_vector_size (phi->m.ls.args) ==
                        pred->def->fargs);
                noll_pred_rule_array *base_rules = pred->def->base_rules;
                assert (base_rules != NULL);
                if (noll_vector_size (base_rules) != 1)
                  {
                    fprintf (stdout,
                             "\nEmpty predicate segment with several base rules: Not yet implemented!\nquit.\n");
                    assert (0);
                  }
#ifndef NDEBUG
                fprintf (stdout,
                         "\nnoll_graph_of_space: empty pred edge, add basic rule constraints\n");
#endif
                noll_pred_rule_t *rule = noll_vector_at (base_rules, 0);
                if ((rule->pure != NULL) &&
                    (rule->pure->data != NULL) &&
                    (noll_vector_size (rule->pure->data) > 0))
                  {
                    /// build the mapping of args to g nodes
                    noll_uid_array *args2 = noll_uid_array_new ();
                    noll_uid_array_reserve (args2, pred->def->fargs);
                    noll_uid_array_push (args2, 0);
                    for (uint_t i = 0; i < pred->def->fargs; i++)
                      {
                        uint_t avi = noll_vector_at (phi->m.ls.args, i);
                        assert (avi < noll_vector_size (g->lvars));
                        noll_uid_array_push (args2, avi);
#ifndef NDEBUG
                        fprintf (stdout,
                                 "\nnoll_graph_of_space: args[%d] = %d\n",
                                 i + 1, avi);
#endif
                      }
                    /// compute the data constraints from the rule
                    noll_dform_array *df =
                      noll_dform_array_apply (rule->pure->data, args2);
                    /// push the data constraints in g
                    if (g->data == NULL)
                      g->data = df;
                    else
                      {
                        noll_dform_array_cup_all (g->data, df);
                        noll_dform_array_delete (df);
                      }
#ifndef NDEBUG
                    fprintf (stdout,
                             "\nnoll_graph_of_space: added constraint\n");
                    noll_dform_array_fprint (stdout, g->lvars, g->data);
#endif
                  }
                return res;     /// no edge is built
              }
            else if (isMatrix == false)
              {
                /// shall copy the matrix of the called predicate 
                fprintf (stdout,
                         "Loop in formula: Not yet implemented!\nquit.\n");
                assert (0);
              }
            /// else, continue like for an ls edge
          }
        else if (isDLL == true)
          {
            assert (noll_vector_size (phi->m.ls.args) >= 4);
            uint_t fst = noll_vector_at (phi->m.ls.args, 0);
            uint_t bk = noll_vector_at (phi->m.ls.args, 1);
            uint_t prv = noll_vector_at (phi->m.ls.args, 2);
            uint_t nxt = noll_vector_at (phi->m.ls.args, 3);
            if ((fst == nxt) && (bk == prv))
              return res;       /// no edge is built
            /// else, continue like for an ls edge
          }

        /// build the edge
        noll_edge_t *e =
          noll_edge_alloc (NOLL_EDGE_PRED, nsrc, ndst, phi->m.ls.pid);
        uint_t i = (noll_pred_isUnaryLoc (phi->m.ls.pid) == true) ? 1 : 2;
        for (; i < noll_vector_size (phi->m.ls.args); i++)
          noll_uid_array_push (e->args,
                               g->var2node[noll_vector_at
                                           (phi->m.ls.args, i)]);
        e->id = nedges;
        // put the edge in graph
        noll_edge_array_push (g->edges, e);
        // push its identifier in the result
        noll_uid_array_push (res, e->id);
        // push the edgeid in the matrix at entry nsrc
        noll_uid_array *src_edges = g->mat[nsrc];
        if (src_edges == NULL)
          {
            src_edges = g->mat[nsrc] = noll_uid_array_new ();
          }
        noll_uid_array_push (src_edges, e->id);
        // push the edgeid in the reverse matrix at entry ndst
        noll_uid_array *dst_edges = g->rmat[ndst];
        if (dst_edges == NULL)
          {
            dst_edges = g->rmat[ndst] = noll_uid_array_new ();
          }
        noll_uid_array_push (dst_edges, e->id);
        // fill the bounded sloc variable
        e->bound_svar = phi->m.ls.sid;

        break;
      }
    case NOLL_SPACE_WSEP:
    case NOLL_SPACE_SSEP:
      {
        // allocate the result
        res = noll_uid_array_new ();
        noll_uid_array_reserve (res, noll_vector_size (phi->m.sep));
        // collect edges from each sub-formula and update the nedges
        uint_t new_nedges = nedges;
        for (uint_t i = 0; i < noll_vector_size (phi->m.sep); i++)
          {
            noll_uid_array *ri =
              noll_graph_of_space (noll_vector_at (phi->m.sep, i), isMatrix,
                                   g, new_nedges, lnode);
            // update the number of edges
            new_nedges += (ri) ? noll_vector_size (ri) : 0;
            // update the separation constraints
            if (ri && phi->kind == NOLL_SPACE_SSEP)
              {
                // add the separation constraints
                // between the collected edges and the new edges
                for (uint_t j = 0; j < noll_vector_size (res); j++)
                  {
                    uint_t ej = noll_vector_at (res, j);
                    noll_edge_t *edge_j = noll_vector_at (g->edges, ej);
                    for (uint_t k = 0; k < noll_vector_size (ri); k++)
                      {
                        uint_t ek = noll_vector_at (ri, k);
                        noll_edge_t *edge_k = noll_vector_at (g->edges, ek);
                        noll_uid_array_push (edge_j->ssep, ek);
                        noll_uid_array_push (edge_k->ssep, ej);
                      }
                  }
              }
            // update the result vector
            if (ri)
              {
                for (uint_t k = 0; k < noll_vector_size (ri); k++)
                  noll_uid_array_push (res, noll_vector_at (ri, k));
                // free the intermediate result
                noll_uid_array_delete (ri);
              }
          }
        break;
      }
    default:
      break;
    }
  return res;
}

/**
 * @brief Fill with the inequality edges the adj matrix of g.
 * 
 * @param phi
 * @param g
 */
void
noll_graph_of_pure (noll_pure_t * phi, noll_graph_t * g)
{
  assert (phi);
  assert (g);
  for (uint_t i = 0; i < phi->size; i++)
    {
      uint_t ni = g->var2node[i];
      for (uint_t j = i + 1; j < phi->size; j++)
        {
          uint_t nj = g->var2node[j];
          if (phi->m[i][j - i] == NOLL_PURE_NEQ)
            {
              if (ni <= nj)
                g->diff[nj][ni] = true;
              else
                g->diff[ni][nj] = true;
            }

        }
    }
  if (g->data == NULL)
    g->data = phi->data;
  else
    noll_dform_array_cup_all (g->data, phi->data);
}

noll_graph_t *
noll_graph_of_form (noll_form_t * phi, bool isMatrix)
{
  if (!phi)
    {
#ifndef NDEBUG
      fprintf (stdout, "noll_graph_of_form: NULL formula\n");
#endif
      // emp formula, build empty graph
      return noll_graph_alloc (NULL, NULL, 0, 0, NULL);
    }

  if (phi->kind == NOLL_FORM_UNSAT)
    return NULL;

  /// the result graph
  noll_graph_t *res = NULL;

  /// compute the number of nodes from the pure part
  uint_t *vars = (uint_t *) malloc (noll_vector_size (phi->lvars)
                                    * sizeof (uint_t));
  uint_t nsize = noll_nodes_of_form (phi, vars);
  /// this number of node is exact if isMatrix, 
  /// otherwise new nodes are added if not isMatrix and loop subformula

  /// count edges pto and pred
  uint_t max_pto =
    noll_atom_of_form (phi->space, isMatrix, NOLL_SPACE_PTO, NULL);
  uint_t nloop = 0;
  uint_t max_ls =
    noll_atom_of_form (phi->space, isMatrix, NOLL_SPACE_LS, &nloop);
  nsize += nloop;
  res = noll_graph_alloc (phi->lvars, phi->svars, nsize, max_pto + max_ls,
                          vars);

  /// go through the space formula,
  ///   assign identifiers to edges, and
  ///   fill information in the graph
  if (phi->space == NULL)
    {
      // emp formula
      res->is_precise = true;
    }
  else
    {
      res->is_precise = phi->space->is_precise;
      uint_t lnode_aux = nsize - nloop; /// used to encode loops if needed
      noll_uid_array *r =
        noll_graph_of_space (phi->space, isMatrix, res, 0, &lnode_aux);
      if (r == NULL)
        {
#ifndef NDEBUG
          fprintf (stdout,
                   "noll_graph_of_form: error in building space formula\n");
#endif // error
          noll_graph_free (res);
          return NULL;
        }
      else
        noll_uid_array_delete (r);
    }

  /// go through pure constraints to obtain distinct edges
  noll_graph_of_pure (phi->pure, res);

  /// aliasing of sharing constraints in the graph
  noll_share_array_copy (res->share, phi->share);

  // TODO: sort variables and
  // TODO: apply permutation obtained on
  //       - edges (for list segments indexed by svars)
  //       - sharing constraints
  return res;
}
