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

/*
 * Normalization of formulas
 */

#include "noll_norm.h"
#include "noll_option.h"

/**
 * Test incrementally the implied (in)equalities and
 * update fsat->form
 */
void
noll_normalize_incr (noll_sat_t * fsat)
{

  assert (fsat != NULL);
  assert (fsat->form != NULL);
  assert (fsat->fname != NULL);
  assert (fsat->var_pure != NULL);

  if (fsat->form->kind == NOLL_FORM_UNSAT)
    /* nothing to do */
    return;

  if (fsat->file != NULL)
    fclose (fsat->file);

  size_t fname_len = strlen (fsat->fname);

  /*
   * Initialize file including the list of (in)equalities queried
   */
  char *fname_inc = (char *) malloc ((fname_len + 20) * sizeof (char));
  memset (fname_inc, 0, (fname_len + 20) * sizeof (char));
  sprintf (fname_inc, "inc_%s", fsat->fname);
  FILE *finc = fopen (fname_inc, "w");

  /*
   * Iterate over unknown (in)equalities between used variables and
   *  - generate atomic formula to recover the result
   *  - print the query in the finc
   */
  noll_sat_pure_array *atoms = noll_sat_pure_array_new ();
  for (uint_t i = 0; i < noll_vector_size (fsat->form->lvars); i++)
    if (fsat->finfo->used_lvar[i] == true)
      {
        for (uint_t j = i + 1; j < noll_vector_size (fsat->form->lvars); j++)
          if (fsat->finfo->used_lvar[j] == true)
            {
#ifndef NDEBUG
              fprintf (stdout, "Iteration %d %d\n", i, j);
              fflush (stdout);
#endif
              if (noll_pure_matrix_at (fsat->form->pure, i, j)
                  == NOLL_PURE_OTHER)
                {
                  // not known (in)equality
                  // check first their types
                  uint_t type_i = noll_var_record (fsat->form->lvars, i);
                  uint_t type_j = noll_var_record (fsat->form->lvars, j);
                  assert (type_i != UNDEFINED_ID);
                  assert (type_j != UNDEFINED_ID);
                  if ((type_i != NOLL_TYP_VOID) &&
                      (type_j != NOLL_TYP_VOID) && (type_i != type_j))
                    {
                      //variables of different types
                      noll_pure_matrix_at (fsat->form->pure, i, j) =
                        NOLL_PURE_NEQ;
                    }
                  else
                    {
                      //variables of the same type or void
#ifndef NDEBUG
                      fprintf (stdout, "**************TESTING %s and %s\n",
                               noll_vector_at (fsat->form->lvars, i)->vname,
                               noll_vector_at (fsat->form->lvars, j)->vname);
                      fflush (stdout);
#endif

                      uid_t bvar_eq_i_j = noll2sat_get_bvar_eq (fsat, i,
                                                                j);
                      assert (bvar_eq_i_j != 0);
                      // Encode equality
                      fprintf (finc, "a -%d 0\n", bvar_eq_i_j);
                      // Encode inequality
                      fprintf (finc, "a %d 0\n", bvar_eq_i_j);

                      // add atom tested
                      noll_sat_pure_t *atom_eq =
                        (noll_sat_pure_t *) malloc (sizeof (noll_sat_pure_t));
                      atom_eq->op = NOLL_PURE_OTHER;
                      atom_eq->x = i;
                      atom_eq->y = j;
                      noll_sat_pure_array_push (atoms, atom_eq);
                    }
                }
            }
      }
  fclose (finc);
  free (fname_inc);

  // print prefix for minisat file
  char *fname_pre = (char *) malloc ((fname_len + 5) * sizeof (char));
  memset (fname_pre, 0, (fname_len + 5) * sizeof (char));
  sprintf (fname_pre, "pre_%s", fsat->fname);
  FILE *out = fopen (fname_pre, "w");
  fprintf (out, "p inccnf\n");
  fclose (out);
  free (fname_pre);

  // build the final file for sat using cat
  char *command = (char *) calloc ((100 + 4 * fname_len), sizeof (char));
  memset (command, 0, (100 + 4 * fname_len) * sizeof (char));
  sprintf (command,
           "cat pre_%s %s inc_%s 1> full_%s", fsat->fname, fsat->fname,
           fsat->fname, fsat->fname);
  if (system (command) == -1)
    assert (0);

  // print the minisat command
  memset (command, 0, (100 + 4 * fname_len) * sizeof (char));
  sprintf (command,
           "minisat_inc -verb=0 full_%s results_%s 1> /dev/null", fsat->fname,
           fsat->fname);
  if (system (command) == -1)
    assert (0);
  free (command);

  // read the result
  char *fname_res = (char *) malloc ((fname_len + 20) * sizeof (char));
  memset (fname_res, 0, (fname_len + 20) * sizeof (char));
  sprintf (fname_res, "results_%s", fsat->fname);
  FILE *fres = fopen (fname_res, "r");
  char *res = NULL;
  size_t lres = 0;

  for (uint_t k = 0; k < noll_vector_size (atoms); k++)
    {
      noll_sat_pure_t *atom = noll_vector_at (atoms, k);
      if (getline (&res, &lres, fres) != -1)
        {
          if (strncmp (res, "UNSAT", 5) == 0)
            {
#ifndef NDEBUG
              fprintf (stdout, "New eq between %s and %s\n",
                       noll_var_name (fsat->form->lvars, atom->x,
                                      NOLL_TYP_RECORD),
                       noll_var_name (fsat->form->lvars, atom->y,
                                      NOLL_TYP_RECORD));
#endif
              noll_form_add_eq (fsat->form, atom->x, atom->y);
              if (fsat->form->kind == NOLL_FORM_UNSAT)
                goto return_norm_incr;
            }
          else
            {
#ifndef NDEBUG
              fprintf (stdout, "Testing eq between %s and %s gives %s\n",
                       noll_var_name (fsat->form->lvars, atom->x,
                                      NOLL_TYP_RECORD),
                       noll_var_name (fsat->form->lvars, atom->y,
                                      NOLL_TYP_RECORD), res);
#endif
            }
        }
      else
        {
#ifndef NDEBUG
          fprintf (stdout, "---- inc: Passed\n");
#endif
          continue;
        }

      // second line for inequality query
      if (getline (&res, &lres, fres) != -1)
        {
          if (strncmp (res, "UNSAT", 5) == 0)
            {
#ifndef NDEBUG
              fprintf (stdout, "New ineq between %s and %s\n",
                       noll_var_name (fsat->form->lvars, atom->x,
                                      NOLL_TYP_RECORD),
                       noll_var_name (fsat->form->lvars, atom->y,
                                      NOLL_TYP_RECORD));
#endif
              noll_form_add_neq (fsat->form, atom->x, atom->y);
              if (fsat->form->kind == NOLL_FORM_UNSAT)
                goto return_norm_incr;
            }
          else
            {
#ifndef NDEBUG
              fprintf (stdout, "Testing ineq between %s and %s gives %s\n",
                       noll_var_name (fsat->form->lvars, atom->x,
                                      NOLL_TYP_RECORD),
                       noll_var_name (fsat->form->lvars, atom->y,
                                      NOLL_TYP_RECORD), res);
#endif
            }
        }
      else
        {
#ifndef NDEBUG
          fprintf (stdout, "---- inc: Passed\n");
#endif
          continue;
        }
    }
return_norm_incr:
  if (res != NULL)
    free (res);
  free (fname_res);
  fclose (fres);
  noll_sat_pure_array_delete (atoms);
}

/**
 * Test iteratively the implied (in)equalities and
 * update fsat->form
 */
void
noll_normalize_iter (noll_sat_t * fsat)
{

  assert (fsat != NULL);
  assert (fsat->form != NULL);
  assert (fsat->fname != NULL);
  assert (fsat->var_pure != NULL);

  if (fsat->file != NULL)
    fclose (fsat->file);

  if (fsat->form->kind == NOLL_FORM_UNSAT)
    /* nothing to do */
    return;

  /*
   * Iterate over unknown (in)equalities between used variables and
   *  - generate a problem for minisat
   *  - fill the result inside the pure formula
   */
  for (uint_t i = 0; i < noll_vector_size (fsat->form->lvars); i++)
    if (fsat->finfo->used_lvar[i] == true)
      {
        for (uint_t j = i + 1; j < noll_vector_size (fsat->form->lvars); i++)
          if (fsat->finfo->used_lvar[j] == true)
            {
#ifndef NDEBUG
              fprintf (stdout, "Iteration %d %d\n", i, j);
              fflush (stdout);
#endif
              if (noll_pure_matrix_at (fsat->form->pure, i, j)
                  == NOLL_PURE_OTHER)
                {
                  // not known (in)equality
                  // check first their types
                  uint_t type_i = noll_var_record (fsat->form->lvars, i);
                  uint_t type_j = noll_var_record (fsat->form->lvars, j);
                  assert (type_i != UNDEFINED_ID);
                  assert (type_j != UNDEFINED_ID);
                  if ((type_i != NOLL_TYP_VOID) &&
                      (type_j != NOLL_TYP_VOID) && (type_i != type_j))
                    {
#ifndef NDEBUG
                      fprintf (stdout, "New inequality between %s and %s (diff types)\n",
			       noll_vector_at (fsat->form->lvars, i)->vname,
			       noll_vector_at (fsat->form->lvars, j)->vname);
#endif
                      noll_pure_matrix_at (fsat->form->pure, i, j) =
                        NOLL_PURE_NEQ;
                    }
                  else
                    {
                      //variables of the same type
#ifndef NDEBUG
                      fprintf (stdout, "**************TESTING %s and %s\n",
                               noll_vector_at (fsat->form->lvars, i)->vname,
                               noll_vector_at (fsat->form->lvars, j)->vname);
#endif

                      // test entailment of equality
                      if (noll2sat_is_eq (fsat, i, j, NOLL_PURE_EQ) == 1)
                        {
#ifndef NDEBUG
                          fprintf (stdout, "UNSATISFIABLE\n");
                          fprintf (stdout, "New equality between %s and %s\n",
                                   noll_vector_at (fsat->form->lvars,
                                                   i)->vname,
                                   noll_vector_at (fsat->form->lvars,
                                                   j)->vname);
#endif
                          noll_pure_matrix_at (fsat->form->pure, i, j) =
                            NOLL_PURE_EQ;
                        }
#ifndef NDEBUG
                      else
                        {
                          fprintf (stdout, "SATISFIABLE\n");
                        }
#endif

                      // test entailment of inequality
                      if (noll2sat_is_eq (fsat, i, j, NOLL_PURE_NEQ) == 1)
                        {
#ifndef NDEBUG
                          fprintf (stdout, "UNSATISFIABLE\n");
                          fprintf (stdout,
                                   "New inequality between %s and %s\n",
                                   noll_vector_at (fsat->form->lvars,
                                                   i)->vname,
                                   noll_vector_at (fsat->form->lvars,
                                                   j)->vname);
#endif
                          noll_pure_matrix_at (fsat->form->pure, i, j) =
                            NOLL_PURE_NEQ;
                        }
#ifndef NDEBUG
                      else
                        {
                          fprintf (stdout, "SATISFIABLE\n");
                        }
#endif
                    }
                }
            }
      }
}

/**
 * If form is satisfiable, normalize it; otherwise do nothing.
 */
noll_sat_t *
noll_normalize (noll_form_t * form, char *fname, bool incr, bool destructive)
{
  if (fname == NULL || form == NULL)
    {
      printf ("File or formula does not exist! quit.\n");
      return NULL;
    }

  if (form->kind == NOLL_FORM_UNSAT)
    return NULL;

  /*
   * Build the boolean abstraction.
   */
  if (noll_option_get_verb () > 0)
    {
      fprintf (stdout, "      * build the boolean abstraction ...\n");
      fflush (stdout);
    }
  noll_sat_t *fsat = noll2sat (form, fname);

  /*
   * Test the satisfiability.
   * If the formula is unsatisfiable we only update the field "kind".
   */
  if (!noll2sat_is_sat (fsat))
    {
      form->kind = NOLL_FORM_UNSAT;
      if (noll_option_get_verb () > 0)
        fprintf (stdout, " unsat formula!\n");
    }
  else
    {
      if (noll_option_get_verb () > 0)
        fprintf (stdout, " sat formula!\n");

      /*
       * Check the implied (in)equalities.
       */
      if (noll_option_get_verb () > 0) {
        fprintf (stdout, "      * infer implied (in)equalities ...\n");
#ifndef NDEBUG
        fprintf (stdout, "        on formula:\n");
        noll_form_fprint (stdout, form);
#endif
      }
      if (incr == true)
        noll_normalize_incr (fsat);
      else
        noll_normalize_iter (fsat);

    }
  if (destructive == true)
    {
      noll_sat_free (fsat);
      return NULL;
    }
#ifndef NDEBUG
  fprintf(stdout, "      * normalized formula:\n");
  noll_form_fprint(stdout, form);
#endif
  return fsat;
}
