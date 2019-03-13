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
 * Defines the problem for the decision procedure.
 */

#include <sys/time.h>
#include <stdio.h>

#include "noll.h"
#include "noll_option.h"
#include "noll_form.h"
#include "noll_entl.h"
#include "noll2bool.h"          // for old normalization call
#include "noll_sat.h"
#include "noll2graph.h"
#include "noll_hom.h"
#include "noll_pred2ta.h"

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

noll_entl_t *noll_prob;         // problem of entailment in noll

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

/* Initialization/Deallocation of problem */
void
noll_entl_init (void)
{
  noll_prob = (noll_entl_t *) malloc (sizeof (noll_entl_t));
  // init file name
  noll_prob->smt_fname = NULL;
  noll_prob->output_fname = NULL;

  // init positive formula
  noll_prob->pform = noll_form_new ();

  // init negative formulae array
  noll_prob->nform = noll_form_array_new ();
  // if empty aray, then SAT problem, else ENTAILMENT problem

  // init command
  noll_prob->cmd = NOLL_FORM_SAT;       // by default value

  // boolean abstraction and graphs to NULL
  noll_prob->pabstr = NULL;
  noll_prob->pgraph = NULL;
  noll_prob->nabstr = NULL;
  noll_prob->ngraph = NULL;

}

/**
 * Free memory allocated for entailment checking
 */
void
noll_entl_free_aux (void)
{

  assert (noll_prob != NULL);
  if (noll_prob->pabstr != NULL)
    {
      noll_sat_free (noll_prob->pabstr);
      noll_prob->pabstr = NULL;
    }
  if (noll_prob->nabstr != NULL)
    {
      noll_sat_array_delete (noll_prob->nabstr);
      noll_prob->nabstr = NULL;
    }
  if (noll_prob->pgraph != NULL)
    {
      noll_graph_free (noll_prob->pgraph);
      noll_prob->pgraph = NULL;
    }
  if (noll_prob->ngraph != NULL)
    {
      noll_graph_array_delete (noll_prob->ngraph);
      noll_prob->ngraph = NULL;
    }
}

void
noll_entl_free (void)
{
  assert (noll_prob != NULL);
  // this procedure shall be called only once
  if (noll_prob->smt_fname != NULL)
    {
      free (noll_prob->smt_fname);
      noll_prob->smt_fname = NULL;
    }
  if (noll_prob->pform != NULL)
    {
      noll_form_free (noll_prob->pform);
      noll_prob->pform = NULL;
    }
  if (noll_prob->nform != NULL)
    {
      noll_form_array_delete (noll_prob->nform);
      noll_prob->nform = NULL;
    }
  noll_entl_free_aux ();
  free (noll_prob);
}

/* ====================================================================== */
/* Getters */
/* ====================================================================== */

noll_form_t *
noll_entl_get_pform ()
{
  assert (noll_prob != NULL);
  return noll_prob->pform;
}

noll_form_t *
noll_entl_get_nform_last ()
{
  assert (noll_prob != NULL);
  assert (noll_prob->nform != NULL);
  if (noll_vector_empty (noll_prob->nform))
    noll_form_array_push (noll_prob->nform, noll_form_new ());

  return noll_vector_last (noll_prob->nform);
}

noll_form_array *
noll_entl_get_nform ()
{
  assert (noll_prob != NULL);
  return noll_prob->nform;
}

/* ====================================================================== */
/* Setters */
/* ====================================================================== */

void
noll_entl_set_fname (char *fname)
{
  assert (noll_prob->smt_fname == NULL);
  noll_prob->smt_fname = strdup (fname);
}

void
noll_entl_set_foutput (char *fname)
{
  assert (noll_prob->output_fname == NULL);
  noll_prob->output_fname = strdup (fname);
}

void
noll_entl_set_cmd (noll_form_kind_t pb)
{
  noll_prob->cmd = pb;
}


/* ====================================================================== */
/* Predicates */
/* ====================================================================== */
int
noll_entl_is_sat (void)
{
  assert (noll_prob != NULL);

  if (noll_prob->nform == NULL || noll_vector_empty (noll_prob->nform))
    return 1;
  return 0;
}


/* ====================================================================== */
/* Printers */
/* ====================================================================== */

void
noll_entl_fprint (FILE * f)
{
  assert (f != NULL);

  if (noll_prob == NULL)
    {
      fprintf (f, "*** (entailment) null\n");
      return;
    }

  fprintf (f, "*** (source %s) check-%s on:\n", noll_prob->smt_fname,
           (noll_prob->cmd == NOLL_FORM_SAT) ? "sat" : "unsat");

  noll_records_array_fprint (f, "records:");
  noll_fields_array_fprint (f, "fields:");
  noll_pred_array_fprint (f, preds_array, "predicates:");

  fprintf (f, "\nFormula 1: ");
  noll_form_fprint (f, noll_prob->pform);
  fflush (f);
  fprintf (f, "\nFormulae 0: ");
  for (size_t i = 0; i < noll_vector_size (noll_prob->nform); i++)
    {
      fprintf (f, "\n\\/ (0-%zu): ", i);
      noll_form_fprint (f, noll_vector_at (noll_prob->nform, i));
    }
  fflush (stdout);
}

/* ====================================================================== */
/* Solver */
/* ====================================================================== */

int
noll_share_check_euf_decl (noll_var_array * lvars, noll_var_array * svars,
                           char *fname)
{
  FILE *out_decl = fopen (fname, "a");
  fprintf (out_decl, "(set-logic UFNIA)\n");
  fprintf (out_decl, "(declare-sort addr 0)\n");

  for (uint_t iterator = 0; iterator < noll_vector_size (svars); iterator++)
    {
      fprintf (out_decl, "(declare-fun %s (addr) Bool)\n",
               noll_vector_at (svars, iterator)->vname);
      /* some part of the extension to alpha(R)
         for (uint_t it = 0; it < noll_vector_size (records_array); it++)
         {
         printf("in loop on exterior: type %s in %s\n",noll_vector_at(records_array,it)->name, noll_vector_at(slocs_array,iterator)->vname);
         if (type_in_predicate_of_svar(it,iterator) == 1)
         {
         fprintf(out_decl,"(declare-fun %s_of_%s (addr) Bool)\n",noll_vector_at(slocs_array,iterator)->vname,noll_vector_at(records_array,it)->name);
         }
         } */
    }

  for (uint_t iterator = 0; iterator < noll_vector_size (lvars); iterator++)
    {
      fprintf (out_decl, "(declare-fun %s () addr)\n",
               noll_vector_at (lvars, iterator)->vname);
    }
  fclose (out_decl);
  return 1;
}

int
noll_share_check_euf_asserts (noll_var_array * lvars, noll_var_array * svars,
                              noll_share_array * share, char *fname, int sign)
{
  if (share == NULL)
    return 0;

  FILE *out_decl = fopen (fname, "a");

  for (uint_t iterator = 0; iterator < noll_vector_size (share); iterator++)
    {
      //printf("#@$#@$@#$@#$\n");
      noll_atom_share_t *atom = noll_vector_at (share, iterator);
      switch (atom->kind)
        {
        case NOLL_SHARE_IN:
          {
            //printf("Member case\n");
            if (noll_vector_size (atom->t_right) == 1)
              {
                if (noll_vector_at (atom->t_right, 0)->kind ==
                    NOLL_STERM_SVAR)
                  {
                    fprintf (out_decl, "(assert ");
                    if (!sign)
                      fprintf (out_decl, "(not ");
                    fprintf (out_decl, " (%s %s) ", noll_vector_at (svars,
                                                                    noll_vector_at
                                                                    (atom->t_right,
                                                                     0)->svar)->vname,
                             noll_vector_at (lvars,
                                             atom->t_left->lvar)->vname);
                    if (!sign)
                      fprintf (out_decl, ")");
                    fprintf (out_decl, ")\n");
                  }
                else
                  {             //this case shouldn't arrive .. it is not handled in the boolean abstraction...it is equivalent to an equality
                    fprintf (out_decl, "(assert ");
                    if (!sign)
                      fprintf (out_decl, "(not ");
                    fprintf (out_decl, " (= (%s %s)) ",
                             noll_vector_at (lvars,
                                             atom->t_left->lvar)->vname,
                             noll_vector_at (lvars,
                                             noll_vector_at (atom->t_right,
                                                             0)->
                                             lvar)->vname);
                    if (!sign)
                      fprintf (out_decl, ")");
                    fprintf (out_decl, ")\n");
                  }
              }
            else
              {
                fprintf (out_decl, "(assert ");
                if (!sign)
                  fprintf (out_decl, "(not ");
                fprintf (out_decl, "(or ");
                for (uint_t i = 0; i < noll_vector_size (atom->t_right); i++)
                  {
                    if (noll_vector_at (atom->t_right, i)->kind
                        == NOLL_STERM_SVAR)
                      {
                        fprintf (out_decl, " (%s %s) ", noll_vector_at (svars,
                                                                        noll_vector_at
                                                                        (atom->t_right,
                                                                         i)->svar)->vname,
                                 noll_vector_at (lvars,
                                                 atom->t_left->lvar)->vname);
                      }
                    else
                      {
                        fprintf (out_decl, " (= (%s %s)) ",
                                 noll_vector_at (lvars,
                                                 atom->t_left->lvar)->vname,
                                 noll_vector_at (lvars,
                                                 noll_vector_at
                                                 (atom->t_right,
                                                  i)->lvar)->vname);
                      }
                  }
                fprintf (out_decl, ")");
                if (!sign)
                  fprintf (out_decl, ")");
                fprintf (out_decl, ")\n");
              }
            break;
          }
        case NOLL_SHARE_NI:
          {
            //printf("Non-Member case\n");
            if (noll_vector_size (atom->t_right) == 1)
              {
                if (noll_vector_at (atom->t_right, 0)->kind ==
                    NOLL_STERM_SVAR)
                  {
                    fprintf (out_decl, "(assert ");
                    if (!sign)
                      fprintf (out_decl, "(not ");
                    fprintf (out_decl, " (not (%s %s)) ",
                             noll_vector_at (svars,
                                             noll_vector_at (atom->t_right,
                                                             0)->svar)->vname,
                             noll_vector_at (lvars,
                                             atom->t_left->lvar)->vname);
                    if (!sign)
                      fprintf (out_decl, ")");
                    fprintf (out_decl, ")\n");
                  }
                else
                  {             //this case shouldn't arrive .. it is not handled in the boolean abstraction...it is equivalent to an equality
                    fprintf (out_decl, "(assert ");
                    if (!sign)
                      fprintf (out_decl, "(not ");
                    fprintf (out_decl, " (not (= (%s %s))) ",
                             noll_vector_at (lvars,
                                             atom->t_left->lvar)->vname,
                             noll_vector_at (lvars,
                                             noll_vector_at (atom->t_right,
                                                             0)->
                                             lvar)->vname);
                    if (!sign)
                      fprintf (out_decl, ")");
                    fprintf (out_decl, ")\n");
                  }
              }
            else
              {
                fprintf (out_decl, "(assert ");
                if (!sign)
                  fprintf (out_decl, "(not ");
                fprintf (out_decl, "(and ");
                for (uint_t i = 0; i < noll_vector_size (atom->t_right); i++)
                  {
                    if (noll_vector_at (atom->t_right, i)->kind
                        == NOLL_STERM_SVAR)
                      {
                        fprintf (out_decl, " (not (%s %s)) ",
                                 noll_vector_at (svars,
                                                 noll_vector_at
                                                 (atom->t_right,
                                                  i)->svar)->vname,
                                 noll_vector_at (lvars,
                                                 atom->t_left->lvar)->vname);
                      }
                    else
                      {
                        fprintf (out_decl, " (not (= (%s %s))) ",
                                 noll_vector_at (lvars,
                                                 atom->t_left->lvar)->vname,
                                 noll_vector_at (lvars,
                                                 noll_vector_at
                                                 (atom->t_right,
                                                  i)->lvar)->vname);
                      }
                  }
                fprintf (out_decl, ")");
                if (!sign)
                  fprintf (out_decl, ")");
                fprintf (out_decl, ")\n");
              }
            break;
          }
        case NOLL_SHARE_SUBSET:
          {
            if (noll_vector_size (atom->t_right) == 1)
              {
                fprintf (out_decl, "(assert ");
                if (!sign)
                  fprintf (out_decl, "(not ");
                if (noll_vector_at (atom->t_right, 0)->kind ==
                    NOLL_STERM_SVAR)
                  fprintf (out_decl,
                           "(forall ((?e addr)) (=> (%s ?e) (%s ?e)))",
                           noll_vector_at (svars, atom->t_left->svar)->vname,
                           noll_vector_at (svars,
                                           noll_vector_at (atom->t_right,
                                                           0)->svar)->vname);
                else
                  fprintf (out_decl,
                           "(forall ((?e addr)) (=> (%s ?e) (= %s ?e)))",
                           noll_vector_at (svars, atom->t_left->svar)->vname,
                           noll_vector_at (lvars,
                                           noll_vector_at (atom->t_right,
                                                           0)->lvar)->vname);
                if (!sign)
                  fprintf (out_decl, ")");
                fprintf (out_decl, ")\n");
              }
            else
              {
                fprintf (out_decl, "(assert ");
                if (!sign)
                  fprintf (out_decl, "(not ");
                fprintf (out_decl, "(forall ((?e addr)) (=> (%s ?e) (or ",
                         noll_vector_at (svars, atom->t_left->svar)->vname);
                for (uint_t i = 0; i < noll_vector_size (atom->t_right); i++)
                  {
                    if (noll_vector_at (atom->t_right, 0)->kind
                        == NOLL_STERM_SVAR)
                      fprintf (out_decl, " (%s ?e) ", noll_vector_at (svars,
                                                                      noll_vector_at
                                                                      (atom->t_right,
                                                                       i)->svar)->vname);
                    else
                      fprintf (out_decl, " (= %s ?e) ", noll_vector_at (lvars,
                                                                        noll_vector_at
                                                                        (atom->t_right,
                                                                         i)->lvar)->vname);
                  }
                fprintf (out_decl, ") ) )");
                if (!sign)
                  fprintf (out_decl, ")");
                fprintf (out_decl, ")\n");

              }
            break;
          }
        default:
          {
            break;
          }
        }
    }
  fclose (out_decl);
  return 1;
}

int
noll_share_check (noll_var_array * lvars, noll_var_array * svars,
                  noll_share_array * pos_share, noll_share_array * neg_share)
{
  int isvalid = 0;
  FILE *out = fopen ("sharing.smt", "w");
  fprintf (out, "\n");
  fclose (out);
  noll_share_check_euf_decl (lvars, svars, "sharing.smt");
  noll_share_check_euf_asserts (lvars, svars, pos_share, "sharing.smt", 1);
  noll_share_check_euf_asserts (lvars, svars, neg_share, "sharing.smt", 0);
  out = fopen ("sharing.smt", "a");
  fprintf (out, "(check-sat)\n");
  fclose (out);

  char *command = (char *) malloc (100 * sizeof (char));
  memset (command, 0, 100 * sizeof (char));
  sprintf (command, "z3 -smt2 sharing.smt 1> smt.log");

  //call z3
  if (system (command) != -1)
    {
      FILE *res = fopen ("smt.log", "r");
      char s[10];
      s[9] = '\0';
      fgets (s, 10, res);
      fclose (res);
      if (strcmp (s, "unsat\n") == 0)
        {
          printf ("*******************UNSAT*******************\n");
          isvalid = 1;
        }
      else
        printf ("*******************SAT*******************\n");
    }
  free (command);
  return isvalid;
}

/**
 * Type the predicates, fields, formulas in noll_prob.
 * @return 1 if typing is ok
 */
int
noll_entl_type ()
{
  /*
   * Type predicate definitions,
   * it has side effects on the typing infos on preds_array 
   */
  if (noll_pred_type () == 0)
    return 0;

  /*
   * Order fields,
   * it has side effects on the fields_array, adds oredeing infos
   */
  if (noll_field_order () == 0)
    return 0;

  /*
   * Type formulas inside the problem.
   */
  if (noll_form_type (noll_prob->pform) == 0)
    return 0;

  for (uint_t i = 0; i < noll_vector_size (noll_prob->nform); i++)
    if (noll_form_type (noll_vector_at (noll_prob->nform, i)) == 0)
      {
#ifndef NDEBUG
        fprintf (stdout, "*** noll_entl_type: type error in %d nform.\n", i);
        fflush (stdout);
#endif
        return 0;
      }

  return 1;
}

/**
 * Normalize the formulae.
 * @return 1 if ok, 0 otherwise
 */
int
noll_entl_normalize ()
{

  noll_form_t *pform = noll_entl_get_pform ();
  noll_form_array *nform = noll_entl_get_nform ();

  if (pform)
    {
      if (noll_option_get_verb () > 0)
        fprintf (stdout, "    o normalize positive formula\n");
#ifndef NDEBUG
      NOLL_DEBUG ("\nnoll_entl_normalize: before ");
      noll_form_fprint (stdout, pform);
#endif
      noll_prob->pabstr = NULL;
      if (noll_option_is_tosat (0) == true)
        normalize_incremental (pform, "p-out.txt");
      else
        noll_prob->pabstr = noll_normalize (pform, "p-out.txt", true, false);
    }
  if (noll_option_is_diag () == true)
    {
      FILE *f_norm = fopen ("form-pos-norm.txt", "w");
      noll_form_fprint (f_norm, noll_prob->pform);
      fclose (f_norm);
      if (noll_option_get_verb () > 0)
        fprintf (stdout,
                 "      normalized positive formula: form-pos-norm.txt\n");
    }

  if (nform)
    {
      // store the computed boolean abstractions
      noll_prob->nabstr = noll_sat_array_new ();
      noll_sat_array_resize (noll_prob->nabstr, noll_vector_size (nform));
      // go through negative formulae
      for (size_t i = 0; i < noll_vector_size (nform); i++)
        {
          noll_form_t *nform_i = noll_vector_at (nform, i);
          noll_sat_t *nform_i_abstr = NULL;
          if (noll_option_get_verb () > 0)
            fprintf (stdout, "    o normalize negative formula %zu\n", i);

          if (noll_option_is_tosat (0) == true)
            normalize_incremental (nform_i, "n-out.txt");
          else
            nform_i_abstr = noll_normalize (nform_i, "n-out.txt", true,
                                            false);
          if (noll_option_is_diag () == true)
            {
              FILE *f_norm = fopen ("form-neg-norm.txt", "w");
              noll_form_fprint (f_norm, noll_prob->pform);
              fclose (f_norm);
              if (noll_option_get_verb () > 0)
                fprintf (stdout,
                         "      normalized negative formula: form-neg-norm.txt\n");
            }
          noll_vector_at (nform, i) = nform_i;
          noll_vector_at (noll_prob->nabstr, i) = nform_i_abstr;
        }
    }

#ifndef NDEBUG
  fprintf (stdout, "*** check-sat: END normalized formulae \n");
  noll_entl_fprint (stdout);
  fflush (stdout);
#endif
  return 1;
}

/**
 * Translate to graph representation all formulas in entailment
 * @return 1 if ok, 0 otherwise
 */
int
noll_entl_to_graph (void)
{

  noll_form_t *pform = noll_prob->pform;
  noll_form_array *nform = noll_entl_get_nform ();

#ifndef NDEBUG
  fprintf (stdout, "*** check-sat: translate to graphs ...\n");
  for (uint_t i = 0; i < pform->pure->size; i++)
    for (uint_t j = i + 1; j < pform->pure->size; j++)
      if (noll_pure_matrix_at (pform->pure, i, j) == NOLL_PURE_EQ)
        printf ("Variable %s equals %s\n",
                noll_vector_at (pform->lvars, i)->vname,
                noll_vector_at (pform->lvars, j)->vname);
#endif

  if (noll_option_get_verb () > 0)
    fprintf (stdout, "    o graph of the positive formula: ...\n");
  noll_prob->pgraph = noll_graph_of_form (pform, false);

  if (noll_option_is_diag () == true)
    {
      noll_graph_fprint_dot ("graph-p.dot", noll_prob->pgraph);
      if (noll_option_get_verb () > 0)
        {
          fprintf (stdout,
                   "      file graph-p.dot: (%d nodes, %d spatial edges)\n",
                   noll_prob->pgraph->nodes_size,
                   noll_vector_size (noll_prob->pgraph->edges));
        }
    }

  if (nform)
    {
      // store the computed boolean abstractions
      noll_prob->ngraph = noll_graph_array_new ();
      noll_graph_array_resize (noll_prob->ngraph, noll_vector_size (nform));
      // go through negative formulae
      for (size_t i = 0; i < noll_vector_size (nform); i++)
        {
          noll_form_t *nform_i = noll_vector_at (nform, i);
          if (noll_option_get_verb () > 0)
            fprintf (stdout, "    o graph of the negative formula %zu: ...\n",
                     i);
          noll_graph_t *nform_i_graph = noll_graph_of_form (nform_i, false);
          noll_vector_at (noll_prob->ngraph, i) = nform_i_graph;

          if (noll_option_is_diag () == true)
            {
              char fname[20] = "\0";
              sprintf (fname, "graph-n%zu.dot", i);
              noll_graph_fprint_dot (fname, nform_i_graph);
              if (noll_option_get_verb () > 0)
                {
                  fprintf (stdout,
                           "      file graph-n%zu.dot: (%d nodes, %d spatial edges)\n",
                           i, nform_i_graph->nodes_size,
                           noll_vector_size (nform_i_graph->edges));
                }
            }
        }
    }
  return 1;
}

/**
 *  Build the graph homeomorphism for this entailment problem
 *  @return 1 if map exists, 0 otherwise
 */
int
noll_entl_to_hom (void)
{

  int res = 1;

  res = noll_hom_build ();
  if (noll_option_get_verb () > 0)
    fprintf (stdout, "    homeomorphism found\n");
  if (noll_option_is_diag () == true)
    {
      if (noll_option_get_verb () > 0)
        fprintf (stdout, "    see file graph-hom.txt\n");
      FILE *f_hom = fopen ("graph-hom.txt", "w");
      noll_hom_fprint (f_hom, noll_prob->hom);
      fflush (f_hom);
      fclose (f_hom);
    }

  /*
   * Check sharing constraints entailment for the found homeomorphism
   */
#ifndef NDEBUG
  //fprintf (stdout, "*** check-sat: test sharing:\n");
  //fprintf (stdout, "\n*****pos_graph: file graph-p-co.dot\n");
  //noll_graph_fprint (stdout, noll_prob->pgraph);
  //noll_graph_fprint_dot ("graph-p-co.dot", noll_prob->pgraph);
  //fprintf (stdout, "\n*****neg_graph: file graph-n-co.dot\n");
  //noll_graph_fprint_dot ("graph-n0-co.dot", noll_vector_at(nol_prob->ngraph,0));
  //fflush (stdout);
#endif
// TODO: when updated share constraints in graphs
// do union of variables
// check_entl_sharing(pos_graph->lvars, pos_graph->svars,
// pos_graph->share,neg_graph->share);

  return res;
}

/**
 * Check special cases for satisfiability of 
 *        pform /\ ! nform.
 * @param isSyn if true, check syntactic special case, 
 *              otherwise, check semantic
 * @return 1 if satisfiable, 0 if unsat, -1 if not known
 */
int
noll_entl_solve_special (bool isSyn)
{
  /* unsat = unsat(pform) */
  if (noll_prob->pform == NULL)
    {
      if (noll_option_get_verb () > 0)
        fprintf (stdout, "    special case: empty (null) positive formula\n");
      return 0;
    }

  assert (NULL != noll_prob->pform);
  /* unsat = unsat(pform) */
  if (noll_form_is_unsat (noll_prob->pform))
    {
      if (noll_option_get_verb () > 0)
        fprintf (stdout, "    special case: unsat positive formula\n");
      return 0;
    }

  assert (NULL != noll_prob->nform);
  if (noll_form_array_is_valid (noll_prob->nform))
    {
      if (noll_option_get_verb () > 0)
        fprintf (stdout, "    special case: valid negative formula\n");
      return 1;
    }

  /* only the previous checks can be done before normalization */
  if (isSyn)
    return -1;

  /* after normalization, more tests can be done */
  if ((noll_prob->nform == NULL)
      || noll_form_array_is_unsat (noll_prob->nform))
    {
      if (noll_option_get_verb () > 0)
        fprintf (stdout,
                 "    special case: sat positive and unsat negative formulas\n");
      return 1;
    }
  return -1;
}

/**
 * Return status of the noll_prob->cmd for the formula
 *    pform /\ not(\/ nform_i)
 * by looking at the entailment
 *    pform ==> \/ nform_i
 *
 * @return 1 if satisfiable, (i.e. invalid entailment)
 *         0 if not satisfiable (i.e., valid entailment)
 *         
 */
int
noll_entl_solve (void)
{
  int res = 0;

#ifndef NDEBUG
  noll_entl_fprint (stdout);
  fflush (stdout);
#endif

  /*
   * Special case of sat solving, when no negative formula
   */
  if (noll_entl_is_sat ())
    return noll_sat_solve (noll_prob->pform);

  /*
   * Test special (syntactic) cases of entailment, 
   * before normalizing the formulas
   */
  if (noll_option_get_verb () > 0)
    fprintf (stdout, "  > check special cases\n");

  res = noll_entl_solve_special (true);
  if (res != -1)
    return res;

  if (noll_option_get_verb () > 0)
    {
      fprintf (stdout, "    not a special case for check-%ssat!\n",
               (noll_prob->cmd == NOLL_FORM_SAT) ? "" : "un");
      fflush (stdout);
    }

  struct timeval tvBegin, tvEnd, tvDiff;

  gettimeofday (&tvBegin, NULL);

  /*
   * Compute typing infos
   */
  if (noll_option_get_verb () > 0)
    fprintf (stdout, "  > typing formulas\n");

  noll_entl_type ();

#ifndef NDEBUG
  fprintf (stdout, "\n*** noll_entl_solve: after typing:\n");
  noll_records_array_fprint (stdout, "records:");
  noll_fields_array_fprint (stdout, "fields:");
  noll_pred_array_fprint (stdout, preds_array, "predicates:");
  fflush (stdout);
#endif

  /*
   * Normalize both formulas (which also test satisfiability)
   */
  if (noll_option_get_verb () > 0)
    fprintf (stdout, "  > normalizing formulas\n");

  noll_entl_normalize ();

  /*
   * Test the satisfiability of pform /\ not(\/_i nform)
   */
  /*
   * Special cases, not covered by graph homeomorphism
   */
  res = noll_entl_solve_special (false);
  if (res != -1)
    goto check_end;

  /*
   * If both formulas are not empty,
   * translate formulas to graphs.
   */
  if (noll_option_get_verb () > 0)
    fprintf (stdout, "  > translation to graphs\n");

  res = noll_entl_to_graph ();
  if (res == 0)
    {
      // entailment invalid, so sat problem
      res = 1;
      goto check_end;
    }

  /*
   * Check graph homeomorphism
   */
  if (noll_option_get_verb () > 0)
    fprintf (stdout, "  > check graph homeomorphism\n");
  /* build homeomorphism from right to left */
  res = noll_entl_to_hom ();
  /* sharing constraints in pos_graph are updated and tested! */
  switch (res)
    {
    case 0:
      {
        // homeomorphism not found, 
        // so entailment invalid, 
        // so sat problem
        res = 1;
        break;
      }
    case 1:
      {
        // homeomorphism found
        // so entailment valid
        // so unsat problem
        res = 0;
        break;
      }
    default:
      assert (res == -1);
      break;
    }

  /*
   * FIN
   */
check_end:

  gettimeofday (&tvEnd, NULL);
  time_difference (&tvDiff, &tvEnd, &tvBegin);
  printf ("\nTotal time (sec): %ld.%06ld\n\n", (long int) tvDiff.tv_sec,
          (long int) tvDiff.tv_usec);
  /*
   * Free the allocated memory
   * (only graphs, formulas will be deallocated at the end)
   */
  noll_entl_free_aux ();

  return res;
}
