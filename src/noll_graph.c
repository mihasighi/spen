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
 * Graph representation of NOLL formulas.
 */

#include "noll_types.h"
#include "noll_form.h"
#include "noll_graph.h"

NOLL_VECTOR_DEFINE (noll_edge_array, noll_edge_t *);

NOLL_VECTOR_DEFINE (noll_graph_array, noll_graph_t *);

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

noll_edge_t *
noll_edge_alloc (noll_edge_e kind, uint_t src, uint_t dst, uint_t label)
{
  noll_edge_t *e = (noll_edge_t *) malloc (sizeof (noll_edge_t));
  e->kind = kind;
  e->label = label;
  e->args = noll_uid_array_new ();
  noll_uid_array_push (e->args, src);
  noll_uid_array_push (e->args, dst);
  e->id = UNDEFINED_ID;
  e->bound_svar = UNDEFINED_ID;
  ;                             // index of the set variable in slocs_array bounded to the edge, or UNDEFINED_ID
  e->impl = NULL;
  e->ssep = noll_uid_array_new ();
  return e;
}

void
noll_edge_free (noll_edge_t * e)
{
  if (e == NULL)
    return;
  if (e->args != NULL)
    {
      noll_uid_array_delete (e->args);
      e->args = NULL;
    }
  if (e->impl != NULL)
    {
      noll_uid_array_delete (e->impl);
      e->impl = NULL;
    }
  if (e->ssep != NULL)
    {
      noll_uid_array_delete (e->ssep);
      e->ssep = NULL;
    }
  free (e);
}

noll_edge_t *
noll_edge_copy (noll_edge_t * e)
{
  /* pre-conditions */
  assert (e != NULL);

  uint_t src = noll_vector_at (e->args, 0);
  uint_t dst = noll_vector_at (e->args, 1);
  noll_edge_t *re = noll_edge_alloc (e->kind, src, dst, e->label);
  /* push the other arguments if there exists */
  for (uint_t i = 2; i < noll_vector_size (e->args); i++)
    noll_uid_array_push (re->args, noll_vector_at (e->args, i));
  /* TODO: fill the informations for overlapping */

  return re;
}

/**
 * Allocate a graph using the informations about the formula.
 * If nodes==0 or edges==0, return the  empty graph, i.e.,
 * only nil node.
 */
noll_graph_t *
noll_graph_alloc (noll_var_array * lvars, noll_var_array * svars,
                  uint_t nodes, uint_t edges, uint_t * vars)
{

  noll_graph_t *res = (noll_graph_t *) malloc (sizeof (noll_graph_t));
#ifndef NDEBUG
  noll_var_array_fprint (stdout, lvars, "Vars of the graph: ");
#endif
  res->lvars = noll_var_array_new ();
  noll_var_array_copy (res->lvars, lvars);
  res->svars = noll_var_array_new ();
  noll_var_array_copy (res->svars, svars);
  // size of the adj matrices
  res->nodes_size = nodes;
  /*
   * labeling of nodes by variables: fill mapping var2nodes
   */
  if (!vars)
    {
      res->var2node = (uint_t *) malloc (noll_vector_size (lvars)
                                         * sizeof (uint_t));
      for (uint_t i = 0; i < noll_vector_size (lvars); i++)
        res->var2node[i] = UNDEFINED_ID;
    }
  else
    res->var2node = vars;
  /*
   * allocate the array of edges
   */
  res->edges = noll_edge_array_new ();
  if (edges > 0)
    noll_edge_array_reserve (res->edges, edges);

  /*
   * allocate the adjacency matrices
   */
  res->mat = (noll_uid_array **) malloc (res->nodes_size
                                         * sizeof (noll_uid_array *));
  res->rmat = (noll_uid_array **) malloc (res->nodes_size
                                          * sizeof (noll_uid_array *));
  for (uint_t i = 0; i < res->nodes_size; i++)
    {
      res->mat[i] = NULL;
      res->rmat[i] = NULL;
    }

  /*
   * allocate the difference edges, a low-diagonal matrix
   */
  res->diff = (bool **) malloc (res->nodes_size * sizeof (bool *));
  for (uint_t i = 0; i < res->nodes_size; i++)
    {
      res->diff[i] = (bool *) malloc ((i + 1) * sizeof (bool));
      for (uint_t j = 0; j <= i; j++)
        res->diff[i][j] = false;
    }
  res->data = NULL;
  res->isDataComplete = false;
  /*
   *  allocate the mapping of set variables to edges
   */
  res->sloc2edge =
    (uint_t *) malloc (noll_vector_size (svars) * sizeof (uint_t));
  for (uint_t i = 0; i < noll_vector_size (svars); i++)
    {
      res->sloc2edge[i] = UNDEFINED_ID;
    }
  // allocate the sharing array
  res->share = noll_share_array_new ();

  res->isComplete = false;
  return res;
}

void
noll_graph_free (noll_graph_t * g)
{

  noll_var_array_delete (g->lvars);
  g->lvars = NULL;
  noll_var_array_delete (g->svars);
  g->svars = NULL;
  if (g->var2node != NULL)
    free (g->var2node);
  for (uint_t i = 0; i < g->nodes_size; i++)
    {
      if (g->mat[i] != NULL)
        noll_uid_array_delete (g->mat[i]);
      if (g->rmat[i] != NULL)
        noll_uid_array_delete (g->rmat[i]);
    }
  free (g->mat);
  free (g->rmat);
  noll_edge_array_delete (g->edges);
  if (g->diff != NULL)
    for (uint_t i = 0; i < g->nodes_size; i++)
      {
        free (g->diff[i]);
      }
  free (g->diff);
  /// g->data freed in formulas
  if (g->sloc2edge != NULL)
    free (g->sloc2edge);
  if (g->share != NULL)
    noll_share_array_delete (g->share);
  free (g);
}

/**
 * Copy only node informations.
 */
noll_graph_t *
noll_graph_copy_nodes (noll_graph_t * g)
{
  if (g == NULL)
    return NULL;

  uint_t v_sz = noll_vector_size (g->lvars);
  uint_t e_sz = noll_vector_size (g->edges);

  noll_graph_t *rg = noll_graph_alloc (g->lvars, g->svars, g->nodes_size,
                                       e_sz, NULL);

  /* copy var2nodes */
  uint_t *v2n = (uint_t *) malloc (sizeof (uint_t) * v_sz);
  for (uint_t i = 0; i < v_sz; i++)
    rg->var2node[i] = g->var2node[i];

  rg->isComplete = g->isComplete;
  rg->is_precise = g->is_precise;

  return rg;
}


/* ====================================================================== */
/* Getters/setters */
/* ====================================================================== */

uint_t
noll_graph_get_var (const noll_graph_t * g, uint_t n)
{
  for (uint_t vi = 0; vi < noll_vector_size (g->lvars); vi++)
    if (g->var2node[vi] == n)
      return vi;
  return UNDEFINED_ID;
}

noll_typ_t
noll_graph_get_node_type (noll_graph_t * g, uint_t n)
{
  assert (g != NULL);
  if (n >= g->nodes_size)
    return false;
  uint_t vid = noll_graph_get_var (g, n);
  if (vid == UNDEFINED_ID)
    return NOLL_TYP_OTHER;
  noll_type_t *ty_vid = noll_var_type (g->lvars, vid);
  return ty_vid->kind;
}

/**
 * Return the edge of @p g2 having label @p label between nodes @p args.
 * 
 * @param args [inout] contains the mapping of arguments of the edge 
 *                     on nodes of @p g or UNDEFINED_ID
 * @param df   [inout] collect the equality constraints between data 
 *                     required by the mapping found
 * @return the identifier of the edge matched or UNDEFINED_ID
 */
uint_t
noll_graph_get_edge (noll_graph_t * g, noll_edge_e kind, uint_t label,
                     noll_uid_array * args, noll_dform_array * df)
{
  // store of edge identifier matching the searched edge 
  uint_t uid_res = UNDEFINED_ID;
  // source and destination nodes for edge searched
  uint_t nroot = noll_vector_at (args, 0);
  // a new intermediary node
  uint_t nend = noll_vector_at (args, 1);
  uint_t fargs = noll_vector_size (args);
  uint_t shift_j = 0;
  if (noll_pred_isUnaryLoc (label) == true)
    {
      nend = 0;
      fargs++;
      shift_j++;
    }
#ifndef NDEBUG
  fprintf (stdout,
           "\n---- Search for edge n%d---(kind=%d, label=%d)-->n%d:\n",
           nroot, kind, label, nend);
#endif

  if (g->mat[nroot] != NULL)
    {
      for (uint_t i = 0;
           (i < noll_vector_size (g->mat[nroot])) &&
           (uid_res == UNDEFINED_ID); i++)
        {
          uint_t ei = noll_vector_at (g->mat[nroot], i);
          noll_edge_t *edge_i = noll_vector_at (g->edges, ei);
          if ((edge_i->kind == kind) && (edge_i->label == label)
              && (noll_vector_size (edge_i->args) == fargs))
            {
#ifndef NDEBUG
              fprintf (stdout, "\t found e%d, same kind, label and root\n",
                       ei);
#endif
              // edge found with the same kind, label and root,
              // check the other arguments than source are equal
              bool ishom = true;
              for (uint_t j = 1;
                   j < noll_vector_size (args) && (ishom == true); j++)
                {
                  uint_t naj = noll_vector_at (args, j);
                  uint_t nej = noll_vector_at (edge_i->args, j + shift_j);
                  if (naj == UNDEFINED_ID)
                    {
#ifndef NDEBUG
                      fprintf (stdout, "\t\t update arg %d to n%d\n", j, nej);
#endif
                      noll_uid_array_set (args, j, nej);
                    }
                  else if (naj != nej)
                    {
                      noll_typ_t ty = noll_graph_get_node_type (g, naj);
                      if ((ty == NOLL_TYP_INT) || (ty == NOLL_TYP_BAGINT))
                        {
                          // generate an equality constraint 
                          uid_t vaj = noll_graph_get_var (g, naj);
                          uid_t vej = noll_graph_get_var (g, naj);
                          noll_dform_t *df_eq =
                            noll_dform_new_eq (noll_dterm_new_var (vaj, ty),
                                               noll_dterm_new_var (vej, ty));
                          noll_dform_array_push (df, df_eq);
                        }
                      else
                        {
                          // if it is a location node, then error
#ifndef NDEBUG
                          fprintf (stdout,
                                   "\t\t but different arg %d (n%d != n%d)\n",
                                   j, naj, nej);
#endif
                          ishom = false;
                        }
                    }
                }
              if (ishom == true)
                {
#ifndef NDEBUG
                  fprintf (stdout, "\t\t , the same args, and the df = ");
                  noll_dform_array_fprint (stdout, g->lvars, df);
#endif
                  uid_res = ei;
                }
            }
        }
    }

#ifndef NDEBUG
  fprintf (stdout, "\t edge-%d matches!\n", uid_res);
#endif
  if (uid_res == UNDEFINED_ID)
    noll_dform_array_clear (df);        // TODO: free also the pointers inside
  return uid_res;
}

/**
 * @brief Update the data constraints in @g with eq constraints.
 * 
 * The (in-)equality constraints on data are pushed.
 */
void
noll_graph_sat_dform (noll_graph_t * g)
{
  assert (g != NULL);

  if (g->data == NULL)
    g->data = noll_dform_array_new ();
  noll_dform_array *res = g->data;
  // go through all equality constraints and push them for data
  for (uint_t vi = 1;           // ignore 'nil' 
       vi < noll_vector_size (g->lvars); vi++)
    {
      noll_type_t *ty_vi = noll_var_type (g->lvars, vi);
      if (ty_vi->kind == NOLL_TYP_RECORD)
        continue;
      // it is a data variable
      // see relation of vi with all other data variables vj
      for (uint_t vj = vi + 1;  // ignore 'nil' 
           vj < noll_vector_size (g->lvars); vj++)
        {
          noll_type_t *ty_vj = noll_var_type (g->lvars, vj);
          if ((ty_vj->kind == NOLL_TYP_RECORD)
              || (ty_vi->kind != ty_vj->kind))
            continue;
          uint_t ni = g->var2node[vi];
          uint_t nj = g->var2node[vj];
          assert (ni < g->nodes_size);
          assert (nj < g->nodes_size);
          if (ni == nj)
            {
              noll_dform_t *df =
                noll_dform_new_eq (noll_dterm_new_var (vi, ty_vi->kind),
                                   noll_dterm_new_var (vj,
                                                       ty_vj->kind));
              noll_dform_array_push (res, df);
            }
          // no difference constraints in the logic of msets
          if ((ty_vi->kind == NOLL_TYP_INT)
              && (noll_graph_is_diff (g, ni, nj) == true))
            {
              noll_dform_t *df =
                noll_dform_new_eq (noll_dterm_new_var (vi, ty_vi->kind),
                                   noll_dterm_new_var (vj,
                                                       ty_vj->kind));
              df->kind = NOLL_DATA_NEQ;
              noll_dform_array_push (res, df);
            }
        }
    }
  g->isDataComplete = true;
}


/**
 * @brief Return true if difference edge between nodes.
 */
bool
noll_graph_is_diff (noll_graph_t * g, uint_t n1, uint_t n2)
{
  assert (n1 < g->nodes_size);
  assert (n2 < g->nodes_size);
  if (n1 == n2)
    return false;
  uint_t nmin = (n1 < n2) ? n1 : n2;
  uint_t nmax = (n1 < n2) ? n2 : n1;
  return g->diff[nmax][nmin];
}

/**
 * @brief Return true if @p n is a node represeting some data var 
 */
bool
noll_graph_is_node_data (noll_graph_t * g, uint_t n)
{
  noll_typ_t ty = noll_graph_get_node_type (g, n);
  return (ty == NOLL_TYP_RECORD) ? false : true;
}

/**
 * @brief Return true if @p n is the source of a pto edge
 */
bool
noll_graph_is_ptosrc (noll_graph_t * g, uint_t n)
{
  assert (g != NULL);
  assert (n < g->nodes_size);

  noll_uid_array *n_edges = g->mat[n];
  if (n_edges == NULL)
    return false;
  for (uint_t i = 0; i < noll_vector_size (n_edges); i++)
    {
      uid_t eid = noll_vector_at (n_edges, i);
      noll_edge_t *ei = noll_vector_at (g->edges, eid);
      assert (ei != NULL);
      if (ei->kind == NOLL_EDGE_PTO)
        return true;
    }
  return false;
}

/** 
 * Test if the edge @p e has its label in the set of labels 
 * of the predicate @p pid. 
 * @param e     edge to be tested
 * @param pid   index of a predicate in preds_array
 * @return      1 if test successful, 0 otherwise
 */
int
noll_edge_in_label (noll_edge_t * e, uint_t pid)
{
  /* pre-conditions */
  assert (e != NULL);
  assert (pid < noll_vector_size (preds_array));
  /* the fields of label are defined in its binding */
  const noll_pred_t *pred = noll_pred_getpred (pid);
  noll_pred_typing_t *pdef = pred->typ;
  int res = 0;
  if (e->kind == NOLL_EDGE_PTO)
    {
      if (noll_pred_is_field (pid, e->label, NOLL_PFLD_DATA))
        res = 1;
    }
  else
    {
      /* it is a predicate edge */
      if (pid == e->label)
        {                       /* it is the same predicate */
          res = 1;
        }
      else
        {
          /* it is an inner predicate */
          if (pdef->ppreds != NULL)
            {
              for (uint_t i = 0;
                   (res == 0) && i < noll_vector_size (pdef->ppreds); i++)
                {
                  uint_t pi = noll_vector_at (pdef->ppreds, i);
                  if (pi == e->label)
                    res = 1;
                }
            }
          if (res == 1)
            return res;
          /// it is a called predicate
          /* the fields of label are defined in its binding */
          const noll_pred_t *pred_e = noll_pred_getpred (e->label);
          noll_pred_typing_t *pdef_e = pred_e->typ;
          if (pdef_e->ppreds != NULL)
            {
              for (uint_t i = 0;
                   (res == 0) && i < noll_vector_size (pdef_e->ppreds); i++)
                {
                  uint_t pi = noll_vector_at (pdef_e->ppreds, i);
                  if (pi == pid)
                    res = 1;
                }
            }
          if (res == 1)
            return res;
          else
            {
#ifndef NDEBUG
              fprintf (stderr,
                       "noll_edge_in_label: predcate edge not in ppreds null\n");
#endif
              res = 0;
            }
        }
    }
  return res;
}

/* ====================================================================== */
/* Others */
/* ====================================================================== */

/**
 * @brief Add explicit edges for dll rd.
 * 
 * For the dll edges (labeled by @p pid) in the graph @p g,
 * add a next edge between the target of the edge and the forward argument.
 */
void
noll_graph_dll (noll_graph_t * g, uid_t pid)
{
  assert (NULL != g);
  // get the fields fid_nxt and fid_prv
  uid_t fid_next = UNDEFINED_ID;
  uid_t fid_prev = UNDEFINED_ID;
  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  assert (NULL != pred);
  assert (NULL != pred->typ);
  assert (NULL != pred->typ->pfields);
  for (uint_t fi = 0;
       (fi < noll_vector_size (fields_array))
       && (fid_next == UNDEFINED_ID || fid_prev == UNDEFINED_ID); fi++)
    {
      if (noll_vector_at (pred->typ->pfields, fi) == NOLL_PFLD_BCKBONE)
        fid_next = fi;
      else if (noll_vector_at (pred->typ->pfields, fi) == NOLL_PFLD_BORDER)
        fid_prev = fi;
    }

  // array of added edges
  noll_edge_array *e1_en = noll_edge_array_new ();
  // the first valid identifier for the added edges
  uint_t lst_eid = noll_vector_size (g->edges);
  for (uint_t ei = 0; ei < noll_vector_size (g->edges); ei++)
    {
      noll_edge_t *e = noll_vector_at (g->edges, ei);
      if (e->kind != NOLL_EDGE_PRED)
        continue;
      uint_t nfst = noll_vector_at (e->args, 0);
      uint_t nlst = noll_vector_at (e->args, 1);
      uint_t nprv = noll_vector_at (e->args, 2);
      uint_t nfwd = noll_vector_at (e->args, 3);
      /* edge nlst --next-->nfwd */
      noll_edge_t *enext = noll_edge_alloc (NOLL_EDGE_PTO, nlst, nfwd,
                                            fid_next);
      enext->id = lst_eid;
      lst_eid++;
      noll_edge_array_push (e1_en, enext);
      // update matrices of g
      // push the edge enext in the matrix at entry nlst
      noll_uid_array *lst_edges = g->mat[nlst];
      if (lst_edges == NULL)
        {
          lst_edges = g->mat[nlst] = noll_uid_array_new ();
        }
      noll_uid_array_push (lst_edges, enext->id);
      // push the edge enext in the reverse matrix at entry nfwd
      noll_uid_array *fwd_edges = g->rmat[nfwd];
      if (fwd_edges == NULL)
        {
          fwd_edges = g->rmat[nfwd] = noll_uid_array_new ();
        }
      noll_uid_array_push (fwd_edges, enext->id);
      /* edge nfst --prev-->nprev */
      noll_edge_t *eprev = noll_edge_alloc (NOLL_EDGE_PTO, nfst, nprv,
                                            fid_prev);
      eprev->id = lst_eid;
      lst_eid++;
      noll_edge_array_push (e1_en, eprev);
      // push the edge eprev in the matrix at entry nfst
      noll_uid_array *fst_edges = g->mat[nfst];
      if (fst_edges == NULL)
        {
          fst_edges = g->mat[nfst] = noll_uid_array_new ();
        }
      noll_uid_array_push (fst_edges, eprev->id);
      // push the edge eprev in the reverse matrix at entry nprv
      noll_uid_array *prv_edges = g->rmat[nprv];
      if (prv_edges == NULL)
        {
          prv_edges = g->rmat[nprv] = noll_uid_array_new ();
        }
      noll_uid_array_push (prv_edges, eprev->id);
    }
  // push all the added edges in g
  for (uint_t ei = 0; ei < noll_vector_size (e1_en); ei++)
    {
      noll_edge_t *e = noll_vector_at (e1_en, ei);
      noll_edge_array_push (g->edges, e);
      noll_vector_at (e1_en, ei) = NULL;
    }
  noll_edge_array_delete (e1_en);
}

/* ====================================================================== */
/* Printing */
/* ====================================================================== */

void
noll_edge_fprint (FILE * f, noll_var_array * svars, noll_edge_t * e)
{
  assert (f);
  assert (e);
  assert (e->args);
  switch (e->kind)
    {
    case NOLL_EDGE_PTO:
      {
        fprintf (f, "%d: n%d.f%d==n%d", e->id,
                 noll_vector_at (e->args, 0), e->label,
                 noll_vector_at (e->args, 1));
        break;
      }
    case NOLL_EDGE_PRED:
      {
        char *svarname =
          (e->bound_svar < noll_vector_size (svars)) ? noll_vector_at (svars,
                                                                       e->
                                                                       bound_svar)->vname
          : "";
        fprintf (f, "%d: %s_%s(n%d,n%d", e->id, noll_pred_name (e->label),
                 svarname, noll_vector_at (e->args, 0),
                 noll_vector_at (e->args, 1));
        if (e && e->args)
          for (uint_t i = 2; i < noll_vector_size (e->args); i++)
            fprintf (f, ",n%d", noll_vector_at (e->args, i));
        fprintf (f, ")");
        break;
      }
    default:
      {
        fprintf (f, "%d: error", e->id);
        break;
      }
    }
}

void
noll_edge_fprint_dot (FILE * f, noll_var_array * svars, noll_edge_t * e)
{
  assert (f);
  assert (e);
  assert (e->args);
  fprintf (f, "n%d -> n%d [label=\"",
           noll_vector_at (e->args, 0), noll_vector_at (e->args, 1));
  noll_edge_fprint (f, svars, e);
  fprintf (f, "\"];\n");
}

void
noll_share_fprint_dot (FILE * f,
                       noll_var_array * lvars,
                       noll_var_array * svars, noll_share_array * phi)
{
  if (!phi)
    {
      fprintf (f, "null");
      return;
    }
  for (uint_t i = 0; i < noll_vector_size (phi); i++)
    {
      noll_share_atom_fprint (f, lvars, svars, noll_vector_at (phi, i));
      fprintf (f, " | ");
    }
  fprintf (f, " true");;
}

void
noll_graph_fprint (FILE * f, noll_graph_t * g)
{
  assert (f);
  if (!g)
    {
      fprintf (f, "\tnull graph\n");
      return;
    }
  fprintf (f, "Graph nodes size: %d\n", g->nodes_size);
  fprintf (f, "Graph nodes labels:\n");
  for (uint_t i = 0; i < noll_vector_size (g->lvars); i++)
    fprintf (f, "%s(n%d),",
             noll_var_name (g->lvars, i, NOLL_TYP_RECORD), g->var2node[i]);
  fprintf (f, "\n");
  fprintf (f, "Graph difference edges: \n");
  assert (g->diff != NULL);
  // low-diagonal matrix
  for (uint_t i = 0; i < g->nodes_size; i++)
    for (uint_t j = 0; j <= i; j++)
      if (g->diff[i][j] == true)
        fprintf (f, "\t\tn%d != n%d\n", i, j);
  fprintf (f, "Graph edges: \n");
  assert (g->edges);
  for (uint_t eid = 0; eid < noll_vector_size (g->edges); eid++)
    {
      noll_edge_fprint (f, g->svars, noll_vector_at (g->edges, eid));
      fprintf (f, "\n");
    }
#ifndef NDEBUG
  fprintf (f, "Matrices: mat = [");
  for (uint_t vi = 0; vi < g->nodes_size; vi++)
    {
      if (g->mat[vi] != NULL)
        {
          fprintf (f, "\n\tn%d --> ", vi);
          for (uint_t i = 0; i < noll_vector_size (g->mat[vi]); i++)
            fprintf (f, "e%d, ", noll_vector_at (g->mat[vi], i));
        }
      if (g->rmat[vi] != NULL)
        {
          fprintf (f, "\n\tn%d <-- ", vi);
          for (uint_t i = 0; i < noll_vector_size (g->rmat[vi]); i++)
            fprintf (f, "e%d, ", noll_vector_at (g->rmat[vi], i));
        }
    }
  fprintf (f, "\n");
#endif
  fprintf (f, "Graph sharing constraints: \n");
  if (g->share)
    {
      noll_share_fprint (f, g->lvars, g->svars, g->share);
    }
  else
    fprintf (f, "\t\tnull\n");
}

void
noll_graph_fprint_dot (char *fname, noll_graph_t * g)
{
  assert (fname);
  if (!g)
    {
      fprintf (stderr, "null graph");
      return;
    }
  FILE *f = fopen (fname, "w");
  if (!f)
    {
      fprintf (stderr, "File %s not found! quit.", fname);
      return;
    }
  fprintf (f, "digraph SLGraph {\nnode [shape=record];\n");
  // print nodes
  for (uint_t n = 0; n < g->nodes_size; n++)
    {
      // print node n with its labels
      fprintf (f, "\tn%d [label=\"{n%d|", n, n);
      for (uint_t v = 0; v < noll_vector_size (g->lvars); v++)
        if (g->var2node[v] == n)
          fprintf (f, "%s ", noll_var_name (g->lvars, v, NOLL_TYP_RECORD));
      fprintf (f, "}\"];\n");
    }
  // print edges

  // fprintf(f, "Graph difference edges: \n");
  assert (g->diff != NULL);
  // low-diagonal matrix
  for (uint_t i = 0; i < g->nodes_size; i++)
    for (uint_t j = 0; j <= i; j++)
      if (g->diff[i][j] == true)
        fprintf (f, "n%d -> n%d [style=dotted];\n", i, j);
  //fprintf(f, "Graph edges: \n");
  assert (g->edges);
  for (uint_t eid = 0; eid < noll_vector_size (g->edges); eid++)
    {
      noll_edge_fprint_dot (f, g->svars, noll_vector_at (g->edges, eid));
      fprintf (f, "\n");
    }

  /* NYI
     fprintf (f, "\tshare [label=\"{share|");
     if (g->share)
     {
     noll_share_fprint_dot (f, g->lvars, g->svars, g->share);
     }
     else
     fprintf (f, "\t\tnull\n");
     fprintf (f, "}\"];\n");
   */

  fprintf (f, "\n}\n");
  fflush (f);
  fclose (f);
  return;
}

void
noll_graph_fprint_sl (char *fname, noll_graph_t * g)
{
  assert (fname);
  if (!g)
    {
      fprintf (stderr, "null graph");
      return;
    }
  FILE *f = fopen (fname, "w");
  if (!f)
    {
      fprintf (stderr, "File %s not found! quit.", fname);
      return;
    }

  /*
   * Print the pure part as (dis-)equalities of labels for nodes
   */
  char **node2var = (char **) malloc (g->nodes_size * sizeof (char *));
  for (uint_t i = 0; i < g->nodes_size; i++)
    node2var[i] = NULL;
  bool isempty = true;
  // fprintf(f, "Pure equality atoms: \n");
  for (uint_t n = 0; n < g->nodes_size; n++)
    {
      for (uint_t v = 0; v < noll_vector_size (g->lvars); v++)
        if (g->var2node[v] == n)
          {
            if (node2var[n] == NULL)
              node2var[n] = noll_var_name (g->lvars, v, NOLL_TYP_RECORD);
            else
              {
                fprintf (f, "%s=%s and ", node2var[n],
                         noll_var_name (g->lvars, v, NOLL_TYP_RECORD));
                isempty = false;
              }
          }
    }

  // fprintf(f, "Pure difference atoms: \n");
  assert (g->diff != NULL);
  // low-diagonal matrix
  for (uint_t i = 0; i < g->nodes_size; i++)
    for (uint_t j = 0; j <= i; j++)
      if (g->diff[i][j] == true)
        {
          fprintf (f, "%s <> %s and ", node2var[i], node2var[j]);
          isempty = false;
        }

  //fprintf(f, "Spatial atoms: \n");
  assert (g->edges);
  // print edges sourcing each node
  for (uint_t n = 0; n < g->nodes_size; n++)
    {
      char *vname = node2var[n];
      if (g->mat[n] == NULL)
        continue;
      /// print all edges, if any
      /// notice that there is no predicate + pto edge from the same node
      bool isempty_pto = true;
      for (uint_t ei = 0; ei < noll_vector_size (g->mat[n]); ei++)
        {
          noll_edge_t *e = noll_vector_at (g->edges,
                                           noll_vector_at (g->mat[n],
                                                           ei));
          assert (e != NULL);
          if (e->kind == NOLL_EDGE_PTO)
            {
              if (isempty_pto == true)
                {
                  isempty_pto = isempty = false;
                  fprintf (f, "%s -> {", vname);
                }
              else
                fprintf (f, ",");
              fprintf (f, "(f%d,%s)", e->label,
                       node2var[noll_vector_at (e->args, 1)]);
            }
          else
            {
              fprintf (f, "%s(%s,%s",
                       noll_pred_name (e->label), vname,
                       node2var[noll_vector_at (e->args, 1)]);
              for (uint_t i = 2; i < noll_vector_size (e->args); i++)
                fprintf (f, ",%s", node2var[noll_vector_at (e->args, i)]);
              fprintf (f, ") * ");
            }
        }
      if (isempty_pto == false)
        fprintf (f, "} * ");
    }
  fprintf (f, "emp\n");
  // free allocated memory 
  for (uint_t i = 0; i < g->nodes_size; i++)
    node2var[i] = NULL;
  free (node2var);
  fflush (f);
  fclose (f);
  return;
}
