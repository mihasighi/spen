#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "noll2bool.h"

#define MAX_PRED 50
#define MAX_PTO 50

/* ====================================================================== */
/* Variables and types used in the construction of the boolean abstraction */
/* ====================================================================== */

int max = 1;                    //used to define a correspondence between boolean variables and integers (needed for DIMACS format)

int **var_eqns;                 // stores the integers denoting boolean variables of the form [x=y]

typedef struct noll_pto_indexed_t
{
  noll_pto_t *points_to;        // a points-to predicate
  int index;                    // the index of the boolean variable associated to the predicate
} noll_pto_indexed_t;
noll_pto_indexed_t *var_pto;    // stores the integers denoting boolean variables of the form [x,y,f]
int index_ls = 0;               //counts the number of variables of the form [x,y,f] (gives the size of var_pto)

typedef struct noll_ls_indexed_t
{
  noll_ls_t *predicate;         // a ls predicate
  int index;                    // the index of the boolean variable associated to the predicate
} noll_ls_indexed_t;
noll_ls_indexed_t *var_ls;      // stores the integers denoting boolean variables of the form [P(x,y,z)]
int index_pto = 0;              //counts the number of variables of the form [P(x,y,z)] (gives the size of var_ls)

int ***var_pto_nodest;
int index_pto_nodest = 0;       //counts the number of variables of the form [x,_,f,alpha] (gives the size of var_pto_nodest)

int **var_member;
int index_member = 0;           //counts the number of variables of the form [x\in\alpha] (gives the size of var_member)

//types and variables for the incremental sat
typedef struct noll_pure_atom
{
  noll_pure_op_t sign;          // equality or inequality
  uint_t x;                     //first variable
  uint_t y;                     //second variable
} noll_pure_atom;

/**
 * Encodes an equality as a natural number
 */
int
encode_eq (int i, int j)
{
  if (var_eqns[i][j] == -1)
    {
      var_eqns[i][j] = var_eqns[j][i] = max;
      max++;
    }
  return var_eqns[i][j];
}

/**
 * Write boolean abstraction for equalities
 */
int
bool_abstr_pure (noll_form_t * form, FILE * out)
{
  if (out == NULL || form == NULL)
    {
      printf ("File or formula does not exist\n");
      return -1;
    }

  uint_t i, j, k;
  int nb_clauses = 0;

  // needed to deal with empty pure formulas
  uint_t size = noll_vector_size (form->lvars);
  if ((form->pure != NULL) && (form->pure->size != size))
    {
      noll_pure_free (form->pure);
      form->pure = NULL;
    }
  if (form->pure == NULL)
    form->pure = noll_pure_new (size);
  noll_pure_op_t **eqns = form->pure->m;
  //write reflexivity
  for (i = 0; i < form->pure->size; i++)
    {
      fprintf (out, "%d 0\n", encode_eq (i, i));
      nb_clauses++;
    }
  //write pure formula and transitivity
  for (i = 0; i < form->pure->size; i++)
    for (j = i + 1; j < form->pure->size; j++)
      {
        if (eqns[i][j - i] == NOLL_PURE_EQ)
          {
            fprintf (out, "%d 0\n", encode_eq (i, j));
            nb_clauses++;
          }
        else if (eqns[i][j - i] == NOLL_PURE_NEQ)
          {
            fprintf (out, "-%d 0\n", encode_eq (i, j));
            nb_clauses++;
          }
        uint_t type_i =
          noll_vector_at (noll_vector_at (form->lvars, i)->vty->args,
                          0);
        uint_t type_j =
          noll_vector_at (noll_vector_at (form->lvars, j)->vty->args,
                          0);
        if (type_i != type_j)
          {
            fprintf (out, "-%d 0\n", encode_eq (i, j));
            nb_clauses++;
          }
        //fprintf(out,"begin %d\n %d,%d",form->pure->size,i,j);
        for (k = 0; k < form->pure->size; k++)
          {
            if ((type_i == type_j)
                && (type_i ==
                    noll_vector_at (noll_vector_at (form->lvars, k)->
                                    vty->args, 0)))
              {
                //test if the three variables have the same type
                fprintf (out, "-%d -%d %d 0\n", encode_eq (i, k),
                         encode_eq (j, k), encode_eq (i, j));
                nb_clauses++;
              }
          }
        //fprintf(out,"end\n");
      }
  return nb_clauses;
}

/**
 * Encodes a simple points-to constraint [x,y,f] as a natural number
 */
int
encode_pto (uint_t x, uint_t y, uint_t f)
{
  var_pto[index_pto].points_to = malloc (sizeof (struct noll_pto_t));
  var_pto[index_pto].points_to->sid = x;
  var_pto[index_pto].points_to->fields = noll_uid_array_new ();
  var_pto[index_pto].points_to->dest = noll_uid_array_new ();
  noll_uid_array_push (var_pto[index_pto].points_to->fields, f);
  noll_uid_array_push (var_pto[index_pto].points_to->dest, y);
  int temp = var_pto[index_pto].index = max;
  max++;
  index_pto++;
  return temp;
}

int
encode_pto_nodest (uint_t x, uint_t f, uint_t alpha)
{
  if (var_pto_nodest[x][f][alpha] == -1)
    {
      var_pto_nodest[x][f][alpha] = max;
      max++;
    }
  return var_pto_nodest[x][f][alpha];
}

/**
 * Encodes a membership constraint [x\in\alpha] as a natural number
 */
int
encode_member (uint_t x, uint_t alpha)
{
#ifndef NDEBUG
  fprintf(stdout, "Member: x:%d, alpha:%d --> ",x,alpha);
#endif
  if (var_member[x][alpha] == -1)
    {
      var_member[x][alpha] = max;
      max++;
    }
#ifndef NDEBUG
  fprintf(stdout, "%d\n",var_member[x][alpha]);
#endif
  return var_member[x][alpha];
}

/**
 * Encodes a ls predicate as a natural number
 */
int
encode_ls (struct noll_ls_t *pred)
{
  var_ls[index_ls].predicate = pred;
  int temp = var_ls[index_ls].index = max;
  max++;
  index_ls++;
  return temp;
}

/**
 * Search an ls atom pred in formula form.
 */
int
ls_in (noll_ls_t * pred, noll_space_t * form)
{
  uint_t res = 0;
  if (form->kind == NOLL_SPACE_LS)
    {
      res = (pred == &(form->m.ls)) ? 1 : 0;
    }
  else if (form->kind == NOLL_SPACE_PTO || form->kind == NOLL_SPACE_EMP
           || form->kind == NOLL_SPACE_JUNK)
    return 0;
  else
    {
      for (uint_t i = 0; i < noll_vector_size (form->m.sep); i++)
        {
          res = ls_in (pred, noll_vector_at (form->m.sep, i));
        }
    }
  return res;
}

/**
 * Search pto atom in formula form.
 */
int
pto_in (struct noll_pto_t *pto, noll_space_t * form)
{
  uint_t res = 0, i;
  if (form->kind == NOLL_SPACE_LS || form->kind == NOLL_SPACE_JUNK)
    {
      return 0;
    }
  else if (form->kind == NOLL_SPACE_PTO)
    {
      if (form->m.pto.sid != pto->sid)
        return 0;
      for (i = 0; i < NOLL_VECTOR_SIZE (form->m.pto.dest); i++)
        {
          if (NOLL_VECTOR_ARRAY (pto->dest)[0]
              == NOLL_VECTOR_ARRAY (form->m.pto.dest)[i]
              && NOLL_VECTOR_ARRAY (pto->fields)[0]
              == NOLL_VECTOR_ARRAY (form->m.pto.fields)[i])
            return 1;
        }
    }
  else
    {
      for (i = 0; i < NOLL_VECTOR_SIZE (form->m.sep); i++)
        {
          res = pto_in (pto, NOLL_VECTOR_ARRAY (form->m.sep)[i]);
        }
    }
  return res;
}

/**
 * Write boolean abstraction of the space formula: F(\Sigma)
 */
int
bool_abstr_space (noll_form_t * form, FILE * out)
{

  //check arguments
  if (out == NULL || form == NULL)
    {
      printf ("File or formula does not exist\n");
      return 0;
    }
  noll_space_t *f = form->space;

  if (f == NULL)
    {
#ifndef NDEBUG
      printf ("space null\n");
#endif
      return 0;
    }
  //initialize arrays that will memorize the encoding with integers
  //var_pto = malloc(form->pure->size*sizeof(int**));
  int nb_clauses = 0;

  //write in the file
  if (f->kind == NOLL_SPACE_PTO)
    {
#ifndef NDEBUG
      fprintf (stdout, "=================pto abstraction\n");
      fflush (stdout);
#endif
      uint_t source = f->m.pto.sid;
      noll_uid_array *flds = f->m.pto.fields;
      noll_uid_array *dests = f->m.pto.dest;
      for (uint_t i = 0; i < NOLL_VECTOR_SIZE (flds); i++)
        {
#ifndef NDEBUG
          fprintf (stdout, "=================pto abstraction %d din %d\n ",
                   i, index_pto);
          fflush (stdout);
#endif
          fprintf (out, "%d 0\n", encode_pto (source,
                                              NOLL_VECTOR_ARRAY (dests)[i],
                                              NOLL_VECTOR_ARRAY (flds)[i]));
          nb_clauses++;
          // Warning: only for NOLL
#ifdef NOLL_SAT
          //points to implies that source and destination are different
          fprintf (out, "-%d 0\n", encode_eq (source,
                                              NOLL_VECTOR_ARRAY (dests)[i]));
          nb_clauses++;
#endif
        }
    }
  else if (f->kind == NOLL_SPACE_LS)
    {
      uint_t pid = f->m.ls.pid;
      uint_t sid = f->m.ls.sid;
#ifndef NDEBUG
      fprintf (stdout, "=================pred abstraction P%d_alpha%d\n",
               pid, sid);
      fflush (stdout);
#endif
      int var = encode_ls (&(f->m.ls));
      uint_t source = noll_vector_at (f->m.ls.args, 0);
      uint_t dest = noll_vector_at (f->m.ls.args, 1);
      if (var == 0)
        {
          assert (0);
          // internal error
        }

      if (noll_pred_is_one_dir (pid))
        {
          uint_t var_eq = encode_eq (source, dest);
          /* /\ (pred \/ (source == dest)) */
          fprintf (out, "%d %d 0\n", var, var_eq);
          /* /\ (!pred \/ (source != dest)) */
          fprintf (out, "-%d -%d 0\n", var, var_eq);
          nb_clauses += 2;
        }
      else
        {
          // Warning: works mainly for DLL
          uint_t vpv = noll_vector_at (f->m.ls.args, 2);
          uint_t vfw = noll_vector_at (f->m.ls.args, 3);

          uint_t var_eq_in_fw = encode_eq (source, vfw);
          uint_t var_eq_out_pv = encode_eq (dest, vpv);

          fprintf (out, "%d %d 0\n", var, var_eq_in_fw);
          fprintf (out, "%d %d 0\n", var, var_eq_out_pv);
          fprintf (out, "-%d -%d -%d 0\n", var, var_eq_in_fw, var_eq_out_pv);
          nb_clauses += 3;
        }
    }
  else if (f->kind == NOLL_SPACE_WSEP)
    {
      //printf("aici1\n");fflush(stdout);
      for (uint_t i = 0; i < noll_vector_size (f->m.sep); i++)
        {
          noll_form_t *temp = malloc (sizeof (noll_form_t));
          temp->lvars = form->lvars;
          temp->svars = form->svars;
          temp->space = noll_vector_at (f->m.sep, i);
          nb_clauses += bool_abstr_space (temp, out);
          temp->lvars = temp->svars = NULL;
          temp->space = NULL;
          free (temp);
        }
    }
  else if (f->kind == NOLL_SPACE_SSEP)
    {
      //printf("aici1\n");fflush(stdout);
      for (uint_t i = 0; i < noll_vector_size (f->m.sep); i++)
        {
          noll_form_t *temp = (noll_form_t *) malloc (sizeof (noll_form_t));
          temp->lvars = form->lvars;
          temp->svars = form->svars;
          temp->space = noll_vector_at (f->m.sep, i);
          nb_clauses += bool_abstr_space (temp, out);
          temp->lvars = temp->svars = NULL;
          temp->space = NULL;
          free (temp);
        }
#ifndef NDEBUG
      fprintf (stdout, "***********begin*************%d\n", nb_clauses);
#endif
      for (uint_t i = 0; i < noll_vector_size (f->m.sep); i++)
        for (int j = 0; j < index_pto + index_ls; j++)
          {

            if (j >= index_pto && ls_in (var_ls[j - index_pto].predicate,
                                         noll_vector_at (f->m.sep, i)))
              {
                for (uint_t k = i + 1; k < noll_vector_size (f->m.sep); k++)
                  for (int t = 0; t < index_pto + index_ls; t++)
                    {

                      if (t >= index_pto
                          && ls_in (var_ls[t - index_pto].predicate,
                                    noll_vector_at (f->m.sep, k)))
                        {
                          // ls with ls
#ifndef NDEBUG
                          fprintf (stdout, "ls %d with ls %d\n",
                                   j - index_pto, t - index_pto);
#endif
                          struct noll_ls_t *atom1_ls = var_ls[j
                                                              -
                                                              index_pto].predicate;
                          struct noll_ls_t *atom2_ls =
                            var_ls[t - index_pto].predicate;

                          uint_t sval1 = atom1_ls->sid;
                          uint_t sval2 = atom2_ls->sid;
#ifndef NDEBUG
                          /* printf("index %s with index %s\n",
                             noll_vector_at(form->svars,sval1)->vname,
                             noll_vector_at(form->svars,sval2)->vname); */
                          printf ("index %d with index %d\n", sval1, sval2);
                          noll_var_array_fprint (stdout, form->lvars,
                                                 "lvars");
                          fflush (stdout);
#endif
                          // for two strongly separated predicates
                          //   there exists no location which belongs to both of them
                          //   (could be improved by checking the type of the location variable
                          //    vs the type of the set variable)
                          // FIX: except nil
                          for (uint_t sii = 1; sii
                               < noll_vector_size (form->lvars); sii++)
                            {
                              fprintf (out, "-%d -%d 0\n",
                                       encode_member (sii, sval1),
                                       encode_member (sii, sval2));
                              nb_clauses++;
                            }

                          uint_t source1 = noll_vector_at (atom1_ls->args, 0);
                          uint_t dest1 = noll_vector_at (atom1_ls->args, 1);
                          uint_t source2 = noll_vector_at (atom2_ls->args, 0);
                          uint_t dest2 = noll_vector_at (atom2_ls->args, 1);
                          fprintf (out, "-%d %d %d 0\n",
                                   encode_eq (source1, source2),
                                   encode_eq (source1, dest1),
                                   encode_eq (source2, dest2));
#ifndef NDEBUG
                          printf ("if %s=%s then %s=%s or %s=%s\n",
                                  noll_vector_at (form->lvars,
                                                  source1)->vname,
                                  noll_vector_at (form->lvars,
                                                  source2)->vname,
                                  noll_vector_at (form->lvars,
                                                  source1)->vname,
                                  noll_vector_at (form->lvars, dest1)->vname,
                                  noll_vector_at (form->lvars,
                                                  source2)->vname,
                                  noll_vector_at (form->lvars, dest2)->vname);
#endif

                          nb_clauses++;
                        }
                      else if (t < index_pto && pto_in (var_pto[t].points_to,
                                                        NOLL_VECTOR_ARRAY
                                                        (f->m.sep)[k]))
                        {
                          // ls with pto
#ifndef NDEBUG
                          fprintf (stdout, "ls %d with pto %d\n",
                                   j - index_pto, t);
#endif
                          struct noll_ls_t *atom1_ls = var_ls[j
                                                              -
                                                              index_pto].predicate;
                          struct noll_pto_t *atom2_pto = var_pto[t].points_to;
                          uint_t source1 =
                            NOLL_VECTOR_ARRAY (atom1_ls->args)[0];
                          uint_t dest1 =
                            NOLL_VECTOR_ARRAY (atom1_ls->args)[1];
                          uint_t source2 = atom2_pto->sid;
                          fprintf (out, "-%d %d 0\n", encode_eq (source1,
                                                                 source2),
                                   encode_eq (source1, dest1));
                          nb_clauses++;

                          if (noll_pred_is_one_dir (atom1_ls->pid) == false)
                            {
                              // Warning: this works only for DLL
                              // F_*(pto(src_2,dst_2) bvari, ls(in_1,out_1) bvarj)
                              // = [src_2 = out_1] ==> - [ls(in_1,out_1)]
#ifndef NDEBUG
                              fprintf (stdout, "ls %d with pto %d\n",
                                       j - index_pto, t);
#endif
                              uint_t var_eq_2_1 = encode_eq (source2, dest1);
                              uint_t prv1 =
                                NOLL_VECTOR_ARRAY (atom1_ls->args)[2];
                              uint_t fwd1 =
                                NOLL_VECTOR_ARRAY (atom1_ls->args)[3];
                              fprintf (out, "-%d %d 0\n", var_eq_2_1,
                                       encode_eq (source1, fwd1));
                              fprintf (out, "-%d %d 0\n", var_eq_2_1,
                                       encode_eq (dest1, prv1));
                              nb_clauses += 2;
                            }
                        }
                    }
              }
            if (j < index_pto && pto_in (var_pto[j].points_to,
                                         NOLL_VECTOR_ARRAY (f->m.sep)[i]))
              {
                for (uint_t k = i + 1; k < NOLL_VECTOR_SIZE (f->m.sep); k++)
                  for (int t = 0; t < index_pto; t++)
                    if (pto_in (var_pto[t].points_to,
                                NOLL_VECTOR_ARRAY (f->m.sep)[k]))
                      {
                        //pto with pto
#ifndef NDEBUG
                        fprintf (stdout, "pto %d with pto %d\n", j, t);
#endif
                        struct noll_pto_t *atom1_pto = var_pto[j].points_to;
                        struct noll_pto_t *atom2_pto = var_pto[t].points_to;
                        uint_t source1 = atom1_pto->sid;
                        uint_t source2 = atom2_pto->sid;
                        fprintf (out, "-%d 0\n", encode_eq (source1,
                                                            source2));
                        nb_clauses++;
                      }
              }
          }
#ifndef NDEBUG
      fprintf (stdout, "************end************%d\n", nb_clauses);
#endif
    }
  else
    {
#ifndef NDEBUG
      printf ("Error: unknown type of space formula");
#endif
    }
  return nb_clauses;
}

/**
 * Writes the boolean abstraction of the membership constraints of "form": F_\in
 */
int
bool_abstr_membership (noll_form_t * form, FILE * out)
{
  //check arguments
  if (out == NULL || form == NULL)
    {
      printf ("File or formula does not exist\n");
      return 0;
    }
  int nb_clauses = 0;

  /*
   * variables x in alpha such that
   * the type of x is not included in the type of alpha are false
   */
  for (uint_t i = 0; i < form->pure->size; i++)
    for (uint_t j = 0; j < NOLL_VECTOR_SIZE (form->svars); j++)
      {
        noll_var_t *t1 = noll_vector_at (form->lvars, i);
        uint_t t3 = noll_var_record (form->lvars, i);
        //the type of the location variable i

        noll_var_t *r1 = noll_vector_at (form->svars, j);
        noll_type_t *r2 = r1->vty;
        uint_t r3 = 0;
        if (noll_vector_size (r2->args) > 0)
          {
            r3 = noll_vector_at (r2->args, 0);
            if (t3 != r3)
              {
#ifndef NDEBUG
                fprintf (stdout, "Var %s is not in %s\n", t1->vname,
                         r1->vname);
#endif
                fprintf (out, "-%d 0\n", encode_member (i, j));
                nb_clauses++;
              }
          }
        else
          {
            if (!type_in_predicate_of_svar (t3, j))
              {
#ifndef NDEBUG
                fprintf (stdout, "Var %s is not in %s\n", t1->vname,
                         r1->vname);
#endif
                fprintf (out, "-%d 0\n", encode_member (i, j));
                nb_clauses++;
              }
          }
      }

  /*
   * x in alpha implies P_alpha(...), for any x and alpha
   */
  for (int i = 0; i < index_ls; i++)
    {
      uint_t svar = var_ls[i].predicate->sid;
      for (uint_t j = 0; j < noll_vector_size (form->lvars); j++)
        {
          noll_var_t *t1 = noll_vector_at (form->lvars, j);
          noll_type_t *t2 = t1->vty;
          uint_t t3 = noll_vector_at (t2->args, 0);     //the type of the location variable i
          if (type_in_predicate_of_svar (t3, svar))
            {
#ifndef NDEBUG
              fprintf (stdout, "Var %s in %s implies %s\n", t1->vname,
                       noll_vector_at (form->svars, svar)->vname,
                       noll_pred_getpred (var_ls[i].predicate->pid)->pname);
#endif
              fprintf (out, "-%d %d 0\n", encode_member (j, svar),
                       var_ls[i].index);
              nb_clauses++;
            }
        }
    }
#ifndef NDEBUG
  fprintf (stdout, "*************************\n");
#endif

  /*
   * closure of membership w.r.t. equality (the types of the variables are checked)
   */
  for (uint_t i = 0; i < form->pure->size; i++)
    for (uint_t j = 0; j < form->pure->size; j++)
      // for efficiency we may put j=i+1
      // but then I need to start by encoding with integers
      // all the constraints of the form [x\in\alpha]
      for (uint_t k = 0; k < NOLL_VECTOR_SIZE (form->svars); k++)
        {
          noll_var_t *t1 = noll_vector_at (form->lvars, i);
          noll_type_t *t2 = t1->vty;
          uint_t t3 = noll_vector_at (t2->args, 0);
          //the type of the location variable i

          noll_var_t *q1 = noll_vector_at (form->lvars, j);
          noll_type_t *q2 = q1->vty;
          uint_t q3 = noll_vector_at (q2->args, 0);
          //the type of the location variable j

          noll_var_t *r1 = noll_vector_at (form->svars, k);
          noll_type_t *r2 = r1->vty;
          uint_t r3 = 0;
          if (noll_vector_size (r2->args) > 0)
            {
              r3 = noll_vector_at (r2->args, 0);
              if (t3 == q3 && t3 == r3)
                {
#ifndef NDEBUG
                  //printf("%s = %s and %s in %s implies %s in %s\n",t1->vname,q1->vname,t1->vname,r1->vname,q1->vname,r1->vname);
#endif
                  fprintf (out, "-%d -%d %d 0\n", encode_eq (i, j),
                           encode_member (j, k), encode_member (i, k));
                  nb_clauses++;
                }
            }
          else
            {
              if (t3 == q3 && type_in_predicate_of_svar (t3, k))
                {
#ifndef NDEBUG
                  //printf("%s = %s and %s in %s implies %s in %s\n",t1->vname,q1->vname,t1->vname,r1->vname,q1->vname,r1->vname);
#endif
                  fprintf (out, "-%d -%d %d 0\n", encode_eq (i, j),
                           encode_member (j, k), encode_member (i, k));
                  nb_clauses++;
                }

            }
        }

  /*
   * a predicate implies that the source belongs to
   * the set of locations variable associated to the predicate
   */
  for (int i = 0; i < index_ls; i++)
    {
#ifndef NDEBUG
      fprintf (stdout, "predicate %s implies %s in %s\n",
               noll_pred_getpred (var_ls[i].predicate->pid)->pname,
               noll_vector_at (form->lvars,
                               noll_vector_at (var_ls[i].predicate->args,
                                               0))->vname,
               noll_vector_at (form->svars, var_ls[i].predicate->sid)->vname);
#endif
      fprintf (out, "-%d %d 0\n", var_ls[i].index,
               encode_member (NOLL_VECTOR_ARRAY (var_ls[i].predicate->args)
                              [0], var_ls[i].predicate->sid));
      nb_clauses++;
    }

  /*
   * membership implies a disjunction of points-to with no destination
   */
#ifndef NDEBUG
  fprintf (stdout,
           "///////////////////// Third part of F_in  ///////////////////////\n");
#endif
  for (uint_t i = 0; i < noll_vector_size (form->lvars); i++)
    for (uint_t j = 0; j < noll_vector_size (form->svars); j++)
      {
        //i\in j a membership predicate
        noll_var_t *lvar = noll_vector_at (form->lvars, i);
        uint_t type_lvar = noll_vector_at (lvar->vty->args, 0);
        //the type of the location variable in the membership predicate

        noll_var_t *svar = noll_vector_at (form->svars, j);
        uint_t type_svar = UNDEFINED_ID;
        //the type of the set of locations variable in the membership predicate

        if (noll_vector_size (svar->vty->args) > 0)
          type_svar = noll_vector_at (svar->vty->args, 0);

        if (((type_svar != UNDEFINED_ID) && (type_lvar != type_svar))
            || ((type_svar == UNDEFINED_ID)
                && (!type_in_predicate_of_svar (type_lvar,
                                                get_pred_of_svar (j)))))
          {                     // MS: is j
            continue;
          }

        int pid = get_pred_of_svar (j);
        if (pid >= 0)
          {                     //the set of locations variable is bound to a predicate pid
            const noll_pred_t *pred = noll_pred_getpred (pid);
            assert (NULL != pred);

            //write x in alpha => disjunction of points-to with no destination
            int flag = 1;       //used to print just once the index of the membership predicate and the 0 at the end of the clause
            /* MS: change of infos on fields */
            for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
              {
                if (noll_pred_is_field (pid, fid, NOLL_PFLD_NESTED))
                  {
                    // fid is a field of pid, even nested
                    //get the source type of a pointer field, the statement below does not work
                    uint_t type_source_field =
                      noll_vector_at (fields_array, fid)->src_r;
                    uint_t type_dest_field =
                      noll_vector_at (fields_array, fid)->pto_r;
                    //printf("types:%d and typed:%d\n",type_source_field,type_dest_field);
                    //int type_source_field = get_source_type_of_field (noll_vector_at(f_array,k));
                    //printf("type lvar:%d, field:%d, type_src_field:%d\n",type_lvar,noll_vector_at(f_array,k),type_source_field);
                    if (type_lvar == type_source_field)
                      {
                        if (flag)
                          {
                            fprintf (out, "-%d ", encode_member (i, j));
#ifndef NDEBUG
                            fprintf (stdout, "%s in %s implies ",
                                     noll_vector_at (form->lvars, i)->vname,
                                     noll_vector_at (form->svars, j)->vname);
#endif
                            flag = 0;
                          }
                        fprintf (out, "%d ", encode_pto_nodest (i, fid, j));
#ifndef NDEBUG
                        fprintf (stdout, "%s src_of %s in %s or ",
                                 noll_vector_at (form->lvars, i)->vname,
                                 noll_vector_at (fields_array, fid)->name,
                                 noll_vector_at (form->svars, j)->vname);
#endif
                      }
                  }
              }
            if (!flag)
              {

                fprintf (out, "0\n");
#ifndef NDEBUG
                fprintf (stdout, "\n");
#endif
                nb_clauses++;
              }

            /*
               //write disjunction of points-to with no destination => x in alpha
               for (int k=0;k<noll_vector_size(f_array);k++) {
               //get the source type of a pointer field, the statement below does not work
               uint_t type_source_field = noll_vector_at(fields_array,noll_vector_at(f_array,k))->src_r;
               uint_t type_dest_field = noll_vector_at(fields_array,noll_vector_at(f_array,k))->pto_r;
               //printf("types:%d and typed:%d\n",type_source_field,type_dest_field);
               //int type_source_field = get_source_type_of_field (noll_vector_at(f_array,k));
               //printf("type lvar:%d, field:%d, type_src_field:%d\n",type_lvar,noll_vector_at(f_array,k),type_source_field);
               if ( type_lvar == type_source_field ) {
               fprintf(out,"-%d %d 0\n",encode_pto_nodest(i,noll_vector_at(f_array,k)),encode_member(i,j));
               #ifndef NDEBUG
               printf("- %s src_of %s or %s in %s \n",noll_vector_at(form->lvars,i)->vname, noll_vector_at(fields_array,noll_vector_at(f_array,k))->name,noll_vector_at(form->lvars,i)->vname,noll_vector_at(form->svars,j)->vname);
               #endif
               nb_clauses++;
               }
               } */
          }
      }
  return nb_clauses;
}

int
get_ls_index_of_svar (uint_t svar)
{
  for (int i = 0; i < index_ls; i++)
    {

      if (var_ls[i].predicate && (var_ls[i].predicate->sid == svar))
        return i;
    }
  return -1;
}

int
get_pred_of_svar (uint_t svar)
{
  for (int i = 0; i < index_ls; i++)
    {

      if (var_ls[i].predicate->sid == svar)
        return var_ls[i].predicate->pid;
    }
  return -1;
}

/**
 * Test if type is covered by the predicate bound to svar.
 * @param type  index of the record
 * @param svar  set of location variable
 * @return 1 if covered, 0 if not, -1 if svar is not bound
 */
int
type_in_predicate_of_svar (uint_t type, uint_t svar)
{
  int ls_i = get_ls_index_of_svar (svar);
  if (ls_i < 0)
    // there is no predicate for this svar
    return -1;
  uint_t i = (uint_t) ls_i;

  const noll_pred_t *pred = noll_pred_getpred (var_ls[i].predicate->pid);
  assert (NULL != pred);
  noll_pred_typing_t *pred_ty = pred->typ;
  if (pred_ty->ptype0 == type)
    return 1;
  // search in other types of the predicate
  for (uint_t t = 0; t < noll_vector_size (pred_ty->ptypes); t++)
    if (type == noll_vector_at (pred_ty->ptypes, t))
      return 1;
  // the type is not in the predicate
  return 0;
}

/**
 * Writes the boolean abstraction of the determinism constraints of "form": F_det
 */
int
bool_abstr_det (noll_form_t * form, FILE * out)
{
  //check arguments
  if (out == NULL || form == NULL)
    {
      printf ("File or formula does not exist\n");
      return 0;
    }
  int nb_clauses = 0;

  //pairs of points-to
#ifndef NDEBUG
  fprintf (stdout,
           "*******************1st step of Det: pto with pto (last %d)*******************\n",
           nb_clauses);
#endif
  for (int i = 0; i < index_pto; i++)
    for (int j = i + 1; j < index_pto; j++)
      {
        uint_t f1 = noll_vector_at (var_pto[i].points_to->fields, 0);
        uint_t f2 = noll_vector_at (var_pto[j].points_to->fields, 0);
        if (f1 == f2)
          {
#ifndef NDEBUG
            fprintf (stdout, "Eq %s = %s implies 1->%s,%s xor 2->field,%s\n",
                     noll_vector_at (form->lvars,
                                     var_pto[i].points_to->sid)->vname,
                     noll_vector_at (form->lvars,
                                     var_pto[j].points_to->sid)->vname,
                     noll_vector_at (fields_array,
                                     noll_vector_at (var_pto[i].
                                                     points_to->fields,
                                                     0))->name,
                     noll_vector_at (form->lvars,
                                     noll_vector_at (var_pto[i].
                                                     points_to->dest,
                                                     0))->vname,
                     noll_vector_at (form->lvars,
                                     noll_vector_at (var_pto[j].
                                                     points_to->dest,
                                                     0))->vname);
#endif
            fprintf (out, "-%d %d %d 0\n",
                     encode_eq (var_pto[i].points_to->sid,
                                var_pto[j].points_to->sid), var_pto[i].index,
                     var_pto[j].index);
            fprintf (out, "-%d -%d -%d 0\n",
                     encode_eq (var_pto[i].points_to->sid,
                                var_pto[j].points_to->sid), var_pto[i].index,
                     var_pto[j].index);
            nb_clauses += 2;
          }
      }
#ifndef NDEBUG
  fprintf (stdout,
           "******************************************************\n");
#endif
  //printf("CCC %d\n",nb_clauses);

  //pairs of points-to with no destination
#ifndef NDEBUG
  fprintf (stdout,
           "*******************2nd step of Det: pto_nodest with pto_nodest (last %d)*******************\n",
           nb_clauses);
#endif
  for (uint_t i1 = 0; i1 < noll_vector_size (form->lvars); i1++)
    for (uint_t i2 = i1 + 1; i2 < noll_vector_size (form->lvars); i2++)
      for (uint_t j = 0; j < noll_vector_size (fields_array); j++)
        {
          uint_t source_type = noll_vector_at (fields_array, j)->src_r;
          uint_t var1_type =
            noll_vector_at (noll_vector_at (form->lvars, i1)->vty->args,
                            0);
          uint_t var2_type =
            noll_vector_at (noll_vector_at (form->lvars, i2)->vty->args,
                            0);
          if (var1_type == var2_type && var1_type == source_type)
            {
              for (uint_t s1 = 0; s1 < noll_vector_size (form->svars); s1++)
                for (uint_t s2 = s1 + 1; s2
                     < noll_vector_size (form->svars); s2++)
                  {
                    if (type_in_predicate_of_svar (var1_type, s1) == 1
                        && type_in_predicate_of_svar (var1_type, s2) == 1)
                      {
#ifndef NDEBUG
                        fprintf (stdout,
                                 "Eq %s=%s implica not(1,%s,%s) or not(2,%s,%s)\n",
                                 noll_vector_at (form->lvars, i1)->vname,
                                 noll_vector_at (form->lvars, i2)->vname,
                                 noll_vector_at (fields_array, j)->name,
                                 noll_vector_at (form->svars, s1)->vname,
                                 noll_vector_at (fields_array, j)->name,
                                 noll_vector_at (form->svars, s2)->vname);
#endif

                        fprintf (out, "-%d -%d -%d 0\n", encode_eq (i1,
                                                                    i2),
                                 encode_pto_nodest (i1, j, s1),
                                 encode_pto_nodest (i2, j, s2));
                        nb_clauses++;
                      }
                  }
            }
        }
#ifndef NDEBUG
  fprintf (stdout,
           "******************************************************\n");
#endif

  //pairs of points-to and points-to with no destination
#ifndef NDEBUG
  fprintf (stdout,
           "*******************3rd step of Det: pto with pto_nodest (last %d)*******************\n",
           nb_clauses);
#endif
  for (int i1 = 0; i1 < index_pto; i1++)
    for (uint_t i2 = 0; i2 < form->pure->size; i2++)
      for (uint_t j = 0; j < noll_vector_size (fields_array); j++)
        for (uint_t si = 0; si < noll_vector_size (form->svars); si++)
          {
            uint_t var1_type = noll_vector_at (noll_vector_at (form->lvars,
                                                               var_pto
                                                               [i1].points_to->sid)->
                                               vty->args,
                                               0);
            uint_t var2_type =
              noll_vector_at (noll_vector_at (form->lvars, i2)->vty->args,
                              0);
            if ((var1_type == var2_type)
                && (type_in_predicate_of_svar (var1_type, si) == 1)
                && (noll_vector_at (var_pto[i1].points_to->fields, 0) == j))
              {                 //maybe:var_pto[i1].points_to->sid != i2 &&
#ifndef NDEBUG
                fprintf (stdout,
                         "Eq %s=%s and 1->%s,%s implica not (2,%s,%s)\n",
                         noll_vector_at (form->lvars,
                                         var_pto[i1].points_to->sid)->vname,
                         noll_vector_at (form->lvars, i2)->vname,
                         noll_vector_at (fields_array,
                                         noll_vector_at (var_pto
                                                         [i1].points_to->
                                                         fields, 0))->name,
                         noll_vector_at (form->lvars,
                                         noll_vector_at (var_pto
                                                         [i1].points_to->dest,
                                                         0))->vname,
                         noll_vector_at (fields_array, j)->name,
                         noll_vector_at (form->svars, si)->vname);
#endif
                fprintf (out, "-%d -%d -%d 0\n",
                         encode_eq (var_pto[i1].points_to->sid, i2),
                         var_pto[i1].index, encode_pto_nodest (i2, j, si));
                //fprintf(out,"-%d -%d -%d 0\n",encode_eq(var_pto[i1].points_to->sid,i2),var_pto[i1].index,encode_pto_nodest(i2,j));
                nb_clauses++;
              }
          }
#ifndef NDEBUG
  fprintf (stdout,
           "******************************************************\n");
#endif

  //pairs of points-to and ls predicates (maybe a problem)
#ifndef NDEBUG
  fprintf (stdout,
           "*******************4th step of Det: pto with pred (last %d)*******************\n",
           nb_clauses);
#endif
  for (int i = 0; i < index_pto; i++)
    for (int j = 0; j < index_ls; j++)
      {
        uint_t svar = var_ls[j].predicate->sid;
        uint_t pid = var_ls[j].predicate->pid;
        uint_t lvar = var_pto[i].points_to->sid;
        uint_t field = noll_vector_at (var_pto[i].points_to->fields, 0);
        /* MS: change of info on fields */
        /* if field is level 0 field of pid */
        if (noll_pred_is_field (pid, field, NOLL_PFLD_BORDER))
          {
            for (uint_t k = 0; k < form->pure->size; k++)
              {
                uint_t type_lvar =
                  noll_vector_at (noll_vector_at (form->lvars, lvar)->
                                  vty->args,
                                  0);
                uint_t type_k =
                  noll_vector_at (noll_vector_at (form->lvars, k)->vty->args,
                                  0);
                if (type_lvar == type_k)
                  {
#ifndef NDEBUG
                    fprintf (stdout,
                             "Var: %s, Field: %s, Predicate: %s, SVar: %s\n",
                             noll_vector_at (form->lvars, lvar)->vname,
                             noll_vector_at (fields_array, field)->name,
                             noll_pred_getpred (pid)->pname,
                             noll_vector_at (form->svars, svar)->vname);
#endif
                    fprintf (out, "-%d -%d %d %d 0\n", encode_eq (lvar, k),
                             encode_member (k, svar), var_ls[j].index,
                             var_pto[i].index);
                    fprintf (out, "-%d -%d -%d -%d 0\n", encode_eq (lvar, k),
                             encode_member (k, svar), var_ls[j].index,
                             var_pto[i].index);
                    nb_clauses += 2;
                  }
              }
          }
      }

  //printf("CCC %d\n",nb_clauses);

  /*
     //pairs of points-to with no destination and ls predicates
     for(int i=0;i<form->pure->size;i++)
     for (int f=0; f<noll_vector_size(fields_array);f++) {
     uint_t type_i = noll_vector_at(noll_vector_at(form->lvars,i)->vty->args,0);
     uint_t type_source = noll_vector_at(fields_array,f)->src_r;
     if (type_i != type_source)
     continue;
     for (int j=0;j<index_ls;j++){
     uint_t svar=var_ls[j].predicate->sid;
     noll_uid_array* fields0 = fields_level0_pred_array[ var_ls[j].predicate->pid ];
     int flag=0;
     for (int it=0; it<noll_vector_size(fields0); it++){
     if (f == noll_vector_at(fields0,it)) {
     flag = 1;
     break;
     }
     }
     if (flag) {
     flag = 0;
     #ifndef NDEBUG
     printf("Entered in flag\n");
     #endif
     for(int k=0;k<form->pure->size;k++){
     uint_t type_k = noll_vector_at(noll_vector_at(form->lvars,k)->vty->args,0);
     if (type_i == type_k && k != i) {
     #ifndef NDEBUG
     printf("Var1: %s, Field: %s, Var2: %s, Predicate: %s, SVar: %s\n",noll_vector_at(form->lvars,i)->vname,noll_vector_at(fields_array,f)->name,noll_vector_at(form->lvars,k)->vname,noll_vector_at(preds_array,var_ls[j].predicate->pid)->pname,noll_vector_at(form->svars,var_ls[j].predicate->sid)->vname);
     #endif
     fprintf(out,"-%d -%d -%d -%d 0\n",encode_eq(i,k),
     encode_member(k,svar),
     var_ls[j].index,
     encode_pto_nodest(i,f));
     //fprintf(out,"-%d -%d -%d -%d 0\n",encode_eq(i,k),encode_member(k,svar),var_ls[j].index,encode_pto_nodest(i,f));
     nb_clauses++;
     }
     }
     #ifndef NDEBUG
     printf("Out of flag\n");
     #endif
     }
     }
     }
   */
  //printf("CCC %d\n",nb_clauses);

  //compute pairs of predicates with common fields of level 0
  int **common_fields;
  common_fields = (int **) malloc (noll_vector_size (preds_array)
                                   * sizeof (int *));
  for (uint_t i = 0; i < noll_vector_size (preds_array); i++)
    {
      common_fields[i] = (int *) malloc (noll_vector_size (preds_array)
                                         * sizeof (int));
    }
  for (uint_t i = 0; i < noll_vector_size (preds_array); i++)
    {
      for (uint_t j = i; j < noll_vector_size (preds_array); j++)
        {
          common_fields[i][j] = 0;
          common_fields[j][i] = 0;
          const noll_pred_t *pi = noll_pred_getpred (i);
          assert (NULL != pi);
          const noll_pred_t *pj = noll_pred_getpred (j);
          assert (NULL != pj);
          /* is fid belongs to level 0 of both predicates pi and pj */
          /* MS: change of info on fields */
          for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
            if (noll_pred_is_field (i, fid, NOLL_PFLD_BORDER) &&
                noll_pred_is_field (j, fid, NOLL_PFLD_BORDER))
              {
                common_fields[i][j] = 1;
                common_fields[j][i] = 1;
#ifndef NDEBUG
                fprintf (stdout, "%s has common fields with %s\n",
                         pi->pname, pj->pname);
#endif
                break;
              }
        }
    }

  //pairs of ls predicates
#ifndef NDEBUG
  fprintf (stdout,
           "*******************5th step of Det: pred with pred (last %d)*******************\n",
           nb_clauses);
#endif
  for (int i = 0; i < index_ls; i++)
    for (int j = i + 1; j < index_ls; j++)
      {
        if (common_fields[var_ls[i].predicate->pid][var_ls[j].predicate->pid])
          {
            uint_t svar1 = var_ls[i].predicate->sid;
            uint_t svar2 = var_ls[j].predicate->sid;
            uint_t pred1 = var_ls[i].predicate->pid;
            uint_t pred2 = var_ls[j].predicate->pid;
            const noll_pred_t *pred1p =
              noll_pred_getpred (var_ls[i].predicate->pid);
            assert (NULL != pred1p);
            const noll_pred_t *pred2p =
              noll_pred_getpred (var_ls[j].predicate->pid);
            assert (NULL != pred2p);
            /* MS: change of fields infos */
            uint_t type1 = pred1p->typ->ptype0;
            uint_t type2 = pred2p->typ->ptype0;
            assert (type1 == type2);
            for (uint_t k = 0; k < form->pure->size; k++)
              for (uint_t t = k + 1; t < form->pure->size; t++) // MS: why not t = k ?
                if ((noll_vector_at
                     (noll_vector_at (form->lvars, k)->vty->args,
                      0) == noll_vector_at (noll_vector_at (form->lvars,
                                                            t)->vty->args, 0))
                    && (type1 ==
                        noll_vector_at (noll_vector_at (form->lvars, k)->
                                        vty->args, 0)))
                  {
#ifndef NDEBUG
                    fprintf (stdout,
                             "Pred1: %s, Pred2: %s, Var1: %s, Var2: %s\n",
                             noll_pred_getpred (pred1)->pname,
                             noll_pred_getpred (pred2)->pname,
                             noll_vector_at (form->lvars, k)->vname,
                             noll_vector_at (form->lvars, t)->vname);
#endif
                    /*fprintf(out, "-%d -%d -%d %d %d 0\n",
                       encode_member(k, svar1), encode_member(t,
                       svar1), encode_eq(k, t), // MS: svar2
                       var_ls[i].index, var_ls[j].index); */
                    fprintf (out, "-%d -%d -%d -%d -%d 0\n", encode_member (k, svar1), encode_member (t, svar2), encode_eq (k, t),      // MS: svar2
                             var_ls[i].index, var_ls[j].index);
                    nb_clauses += 1;
                  }
          }

      }

  //printf("CCC %d\n",nb_clauses);
  for (uint_t i = 0; i < noll_vector_size (preds_array); i++)
    {

      free (common_fields[i]);
    }
  free (common_fields);

  return nb_clauses;
}

void
bool_abstr_share_var_in_sterm (FILE * out, noll_form_t * form, uint_t vi,
                               noll_sterm_array * t)
{

  uint_t ty_vi = noll_var_record (form->lvars, vi);

  for (uint_t tj = 0; tj < noll_vector_size (t); tj++)
    {
      noll_sterm_t *term = noll_vector_at (t, tj);
      if ((term->kind == NOLL_STERM_LVAR)
          && (ty_vi == noll_var_record (form->lvars, term->lvar)))
        {
#ifndef NDEBUG
          fprintf (stdout, "%s = %s ",
                   noll_vector_at (form->lvars, vi)->vname,
                   noll_vector_at (form->lvars, term->lvar)->vname);
#endif
          fprintf (out, "%d ", encode_eq (vi, term->lvar));
        }
      else if ((term->kind == NOLL_STERM_SVAR)
               && type_in_predicate_of_svar (ty_vi, term->svar))
        {
#ifndef NDEBUG
          fprintf (stdout, "%s in %s ",
                   noll_vector_at (form->lvars, vi)->vname,
                   noll_vector_at (form->svars, term->svar)->vname);
#endif
          fprintf (out, "%d ", encode_member (vi, term->svar));
        }
      else if ((term->kind == NOLL_STERM_PRJ)
               && type_in_predicate_of_svar (ty_vi, term->svar)
               && (ty_vi == noll_var_record (form->lvars, term->lvar)))
        {
#ifndef NDEBUG
          fprintf (stdout, "%s in %s ",
                   noll_vector_at (form->lvars, vi)->vname,
                   noll_vector_at (form->svars, term->svar)->vname);
#endif
          fprintf (out, "%d ", encode_member (vi, term->svar));
        }
      else
        {
          // this term is not useful, ignore it
#ifndef NDEBUG
          fprintf (stdout, "nothing ");
#endif
          continue;
        }
    }
}

/**
 * Writes the boolean abstraction of the sharing constraints of "form": F(\Lambda)
 */
int
bool_abstr_share (noll_form_t * form, FILE * out)
{
  //check arguments
  if (out == NULL || form == NULL)
    {
      printf ("File or formula does not exist\n");
      return 0;
    }
  int nb_clauses = 0;

  if (form->share == NULL)
    return 0;

  // simplify_share (form);

  for (uint_t iterator = 0; iterator < noll_vector_size (form->share);
       iterator++)
    {
      //the case for a single inclusion
      noll_atom_share_t *atom = noll_vector_at (form->share, iterator);
      switch (atom->kind)
        {
        case NOLL_SHARE_IN:
          {
            assert (atom->t_left->kind == NOLL_STERM_LVAR);
            uint_t lvar = atom->t_left->lvar;
            bool_abstr_share_var_in_sterm (out, form, lvar, atom->t_right);
            /*
               for (uint_t i = 0; i < noll_vector_size (atom->t_right); i++) {
               assert (noll_vector_at (atom->t_right, i)->kind == NOLL_STERM_SVAR);
               {
               // TODO: check types
               #ifndef NDEBUG
               fprintf(stdout, "PROBLEM\n");
               #endif
               fprintf(out, "%d ", encode_member(lvar,
               noll_vector_at (atom->t_right, i)->svar));
               }
               //else {
               // TODO: singleton dealt below, but what about projection?
               //   fprintf(out, "%d ", encode_eq(lvar,
               //                   noll_vector_at (atom->t_right, i)->lvar));
               // }
               }
             */
            fprintf (out, "0\n");
            nb_clauses++;
            break;
          }
        case NOLL_SHARE_NI:
          {
            assert (atom->t_left->kind == NOLL_STERM_LVAR);
            uint_t lvar = atom->t_left->lvar;
            for (uint_t i = 0; i < noll_vector_size (atom->t_right); i++)
              {
                noll_sterm_t *ti = noll_vector_at (atom->t_right, i);
                if (ti->kind >= NOLL_STERM_SVAR)
                  {
                    // projection also dealt
#ifndef NDEBUG
                    fprintf (stdout, "++++++ %s not in %s\n ",
                             noll_vector_at (form->lvars, lvar)->vname,
                             noll_vector_at (form->svars, ti->svar)->vname);
#endif
                    fprintf (out, "-%d 0\n", encode_member (lvar, ti->svar));
                    nb_clauses++;
                  }
                else
                  {
#ifndef NDEBUG
                    fprintf (stdout, "++++++ %s != %s\n ",
                             noll_vector_at (form->lvars, lvar)->vname,
                             noll_vector_at (form->lvars, ti->lvar)->vname);
#endif
                    fprintf (out, "-%d 0\n", encode_eq (lvar, ti->lvar));
                    nb_clauses++;
                  }
              }
            break;
          }
        default:
          {                     // case inclusion
#ifndef NDEBUG
            fprintf (stdout, "noll2bool: share atom");
            noll_share_atom_fprint (stdout, form->lvars, form->svars, atom);
            fprintf (stdout, "\n");
#endif
            assert (atom->t_left->kind >= NOLL_STERM_SVAR);
            uint_t left_svar = atom->t_left->svar;
            uint_t ty_left =
              (atom->t_left->kind == NOLL_STERM_SVAR) ? UNDEFINED_ID
              : noll_var_record (form->lvars, atom->t_left->lvar);
            /*
             * for any variable vi, if vi in t_left then vi in one of the t_right
             * but only if vi is of type compatible with t_left and t_right
             */
            for (uint_t vi = 0; vi < noll_vector_size (form->lvars); vi++)
              {
                uint_t ty_vi = noll_var_record (form->lvars, vi);
                if ((ty_left != UNDEFINED_ID) && (ty_left != ty_vi))
                  // ty_left is precise, but not equal to ty_vi
                  continue;
                if ((ty_left == UNDEFINED_ID)
                    && !type_in_predicate_of_svar (ty_vi, left_svar))
                  // ty_left is a set, but does not contain ty_vi
                  continue;
                // here, vi and left_svar have compatible types
#ifndef NDEBUG
                fprintf (stdout, "++++++ %s in %s implies ",
                         noll_vector_at (form->lvars, vi)->vname,
                         noll_vector_at (form->svars, left_svar)->vname);
#endif
                // print \neg x \in \alpha_1
                fprintf (out, "-%d ", encode_member (vi, left_svar));
                // print disjunction of left terms for vi
                bool_abstr_share_var_in_sterm (out, form, vi, atom->t_right);
                // end clause
                fprintf (out, "0\n");
#ifndef NDEBUG
                fprintf (stdout, " +++++++++++++++++++\n");
#endif
                nb_clauses++;
              }

            /*
             * if t_left is associated to a ls predicate,
             * and t_left->lvar has the same type as the recursive type of the predicate
             * and if this predicate is not empty
             * then the source of this predicate belongs to one of the terms in t_right
             */
            int pi = get_ls_index_of_svar (left_svar);
            if (pi != -1)
              {
                uint_t source =
                  noll_vector_at (var_ls[pi].predicate->args, 0);
                // if t_left is a projection,
                // we generate the constraint only if the type of source
                // is the type of the projection
                if ((ty_left != UNDEFINED_ID) && noll_var_record (form->lvars,
                                                                  source) !=
                    ty_left)
                  break;        // nothing to be done
                // else, generate the constraint
                // if [pi ...] true then
                fprintf (out, "-%d ", var_ls[pi].index);
#ifndef NDEBUG
                fprintf (stdout, "++++++ pred-%d implies ", pi);
#endif
                // print disjunction for each term of t_right
                bool_abstr_share_var_in_sterm (out, form, source,
                                               atom->t_right);
                // end clause
                fprintf (out, "0\n");
#ifndef NDEBUG
                fprintf (stdout, " +++++++++++++++++++\n");
#endif
                nb_clauses++;
              }
            break;
          }
        }
    }

  return nb_clauses;
}

/**
 * Alloc the data structures used  for boolean abstraction.
 */
void
bool_abstr_init (noll_form_t * form)
{
  //initialize the arrays that store the encoding with integers
  uint_t nvars = noll_vector_size (form->lvars);
  var_eqns = (int **) malloc (nvars * sizeof (int *));
  for (uint_t i = 0; i < nvars; i++)
    {
      var_eqns[i] = (int *) malloc (nvars * sizeof (int));
      for (uint_t j = 0; j < nvars; j++)
        var_eqns[i][j] = -1;
    }
  var_ls =
    (noll_ls_indexed_t *) malloc (MAX_PRED * sizeof (noll_ls_indexed_t));
  index_ls = 0;
  var_pto
    = (noll_pto_indexed_t *) malloc (MAX_PTO * sizeof (noll_pto_indexed_t));
  index_pto = 0;
  var_member = (int **) malloc (nvars * sizeof (int *));
  uint_t nsvars = noll_vector_size (form->svars);
  //printf("$$$$$ Init $$$$$$$: %d %d\n",nvars,nsvars);
  for (uint_t i = 0; i < nvars; i++)
    {
      var_member[i] = (int *) malloc (nsvars * sizeof (int));
      for (uint_t j = 0; j < nsvars; j++)
        var_member[i][j] = -1;
    }
  var_pto_nodest = (int ***) malloc (nvars * sizeof (int **));
  for (uint_t i = 0; i < nvars; i++)
    {
      var_pto_nodest[i] = (int **) malloc (noll_vector_size (fields_array)
                                           * sizeof (int *));

      for (uint_t j = 0; j < noll_vector_size (fields_array); j++)
        {
          var_pto_nodest[i][j] = (int *) malloc (nsvars * sizeof (int));
          for (uint_t k = 0; k < nsvars; k++)
            var_pto_nodest[i][j][k] = -1;
        }
    }
}

void
bool_abstr_free (noll_form_t * form)
{
  uint_t nvars = noll_vector_size (form->lvars);
  for (uint_t i = 0; i < nvars; i++)
    {
      free (var_eqns[i]);
    }
  free (var_eqns);

  free (var_ls);
  free (var_pto);
  for (uint_t i = 0; i < nvars; i++)
    {
      free (var_member[i]);
    }
  free (var_member);
  for (uint_t i = 0; i < nvars; i++)
    {
      for (uint_t j = 0; j < noll_vector_size (fields_array); j++)
        free (var_pto_nodest[i][j]);
      free (var_pto_nodest[i]);
    }
  free (var_pto_nodest);

  max = 1;
  index_ls = 0;
  index_pto = 0;
  index_pto_nodest = 0;
  index_member = 0;
}

/**
 * Write the DIMACS file for the boolean abstraction of a formula
 */
void
write_bool_abstr (noll_form_t * form, char *fname, int *nbvar, int *nbclauses)
{

  // init the data structures used
  bool_abstr_init (form);
  FILE *out;
  out = fopen (fname, "w");
  int nb_clauses = 0;
  nb_clauses += bool_abstr_pure (form, out);
#ifndef NDEBUG
  fprintf (stdout, "Clauses for F(Pi) and F_eq = %d\n", nb_clauses);
#endif
  nb_clauses += bool_abstr_space (form, out);
#ifndef NDEBUG
  fprintf (stdout, "Clauses for F(Pi) and F_eq and F(Sigma) = %d\n",
           nb_clauses);
#endif
  nb_clauses += bool_abstr_membership (form, out);
#ifndef NDEBUG
  fprintf (stdout, "Clauses for F(Pi) and F_eq and F(Sigma) and F_in = %d\n",
           nb_clauses);
#endif
  nb_clauses += bool_abstr_det (form, out);
#ifndef NDEBUG
  fprintf (stdout,
           "Clauses for F(Pi) and F_eq and F(Sigma) and F_in and F_det = %d\n",
           nb_clauses);
#endif
  nb_clauses += bool_abstr_share (form, out);
#ifndef NDEBUG
  fprintf (stdout, "Clauses for the final formulae = %d\n", nb_clauses);
#endif
  fclose (out);

  *nbvar = max - 1;
  *nbclauses = nb_clauses;
}

/**
 * Uses the boolean abstraction in the file fname,
 * returns 1 if the boolean abstraction implies [x oper y]
 * returns 0, otherwise
 */
int
test_in_equality (uint_t x, uint_t y, noll_pure_op_t oper, int nbv, int nbc,
                  char *fname)
{
  if (&nbv != &nbv)
    {
      assert (0);               // just to remove "unused variable" warning
    }

  //adding the (in)equality between x and y to the input file*/
  FILE *out;
  int new = 0;
  //test if the index of the equality between x and y has not been generated
  if (var_eqns[x][y] == -1)
    {
      encode_eq (x, y);
      new = 1;
      //#ifndef NDEBUG
      printf ("New variable %d\n", max);
      //#endif
    }

  // print the prefix file with information about variables and clauses
  char *pre_fname = (char *) malloc ((5 + strlen (fname)) * sizeof (char));
  memset (pre_fname, 0, (5 + strlen (fname)) * sizeof (char));
  sprintf (pre_fname, "pre_%s", fname);
  out = fopen (pre_fname, "w");
  fprintf (out, "p cnf %d %d\n", max - 1, nbc + 1);
#ifndef NDEBUG
  fprintf (stdout, "---- minisat query prefix: p cnf %d %d\n", max - 1,
           nbc + 1);
#endif
  free (pre_fname);
  fclose (out);

  // print the suffix file with the equality to test
  char *eq_fname = (char *) malloc ((5 + strlen (fname)) * sizeof (char));
  memset (eq_fname, 0, (5 + strlen (fname)) * sizeof (char));
  sprintf (eq_fname, "eq_%s", fname);
  out = fopen (eq_fname, "w");

  //write a new clause in the DIMACS file
  if (oper == NOLL_PURE_EQ)
    {
      fprintf (out, "-%d 0\n", encode_eq (x, y));
    }
  else if (oper == NOLL_PURE_NEQ)
    {
      fprintf (out, "%d 0\n", encode_eq (x, y));
    }
  else
    {
      free (eq_fname);
      return -1;
    }
  fclose (out);

  /*
   * delete the index generated for
   * the equality between x and y (if it was generated here)
   */
  if (new == 1)
    {
      var_eqns[x][y] = -1;
      max--;
      //printf("Variable deleted %d\n",max);
    }

  // build the final file for sat using cat
  char *command = (char *) calloc ((100 + 4 * strlen (fname)), sizeof (char));
  memset (command, 0, (100 + 4 * strlen (fname)) * sizeof (char));
  sprintf (command, "cat pre_%s %s eq_%s 1> full_new_%s", fname, fname, fname,
           fname);
  if (system (command) != -1)
    assert (0);

  // print the minisat command
  memset (command, 0, (100 + 4 * strlen (fname)) * sizeof (char));
  sprintf (command, "minisat -verb=0 full_new_%s result.txt 1> msat_eq_%s",
           fname, fname);
  if (system (command) != -1)
    {
      FILE *res;
      res = fopen ("result.txt", "r");
      char *s = (char *) malloc (10 * sizeof (char));
      s[9] = '\0';
      fgets (s, 10, res);
      fclose (res);
      if (strcmp (s, "UNSAT\n") == 0)
        {
          free (s);
          free (command);
          return 1;
        }
      free (s);
    }
  free (command);
  return 0;
}

/**
 * Test of satisfiability.
 * File fname shall contain the boolean abstraction.
 */
int
test_satisfiability (int nbv, int nbc, char *fname)
{
  // print the prefix file for sat
  char *fname_pre = (char *) malloc ((strlen (fname) + 5) * sizeof (char));
  memset (fname_pre, 0, (strlen (fname) + 5) * sizeof (char));
  // fname_pre[0] = '\0';
  sprintf (fname_pre, "pre_%s", fname);
  FILE *out = fopen (fname_pre, "w");
  fprintf (out, "p cnf %d %d\n", nbv, nbc);
#ifndef NDEBUG
  fprintf (stdout, "---- minisat query prefix: p cnf %d %d\n", nbv, nbc);
#endif
  fclose (out);
  free (fname_pre);

  // build the final file for sat using cat
  char *command =
    (char *) malloc ((100 + 3 * strlen (fname)) * sizeof (char));
  memset (command, 0, (100 + 3 * strlen (fname)) * sizeof (char));
  //command[0] = '\0';
  sprintf (command, "cat pre_%s %s 1> sat_%s", fname, fname, fname);
  if (system (command) != -1)
    {

      // print the minisat command
      memset (command, 0, (100 + 3 * strlen (fname)) * sizeof (char));
      //command[0] = '\0';
      sprintf (command, "minisat -verb=0 sat_%s result.txt 1> msat_%s",
               fname, fname);

      //call minisat
      if (system (command) != -1)
        {
          FILE *res;
          res = fopen ("result.txt", "r");
          char *s = malloc (10 * sizeof (char));
          s[9] = '\0';
          fgets (s, 10, res);
          //printf("*********************%s**************8\n",s);
          fclose (res);
          if (strcmp (s, "UNSAT\n") == 0)
            {
              //printf("*******************UNSAT*******************\n");

              free (command);
              free (s);
              return 0;
            }
          free (s);
        }
    }
  free (command);
  return 1;
}

/**
 * Computes normal form of formula form (in place).
 * File fname will contain the boolean abstraction.
 */
void
normalize (noll_form_t * form, char *fname)
{
  if (fname == NULL || form == NULL)
    {
      printf ("File or formula does not exist\n");
      return;
    }
  /*
   * Build the boolean abstraction
   */
  int nbv, nbc;
  write_bool_abstr (form, fname, &nbv, &nbc);

  /*
   * Test the satisfiability
   * If the formula is unsatisfiable we only update the field "kind"
   */
  if (!test_satisfiability (nbv, nbc, fname))
    {
      form->kind = NOLL_FORM_UNSAT;
#ifndef NDEBUG
      printf ("+++++++++++The formula is unsatisfiable+++++++++++++\n");
#endif
      bool_abstr_free (form);
      return;
    }

  /*
   * Checking the implied (in)equalities
   */
#ifndef NDEBUG
  //all (in)equalities are written in the file "($fname)_inc.txt"
  char *fname_inc = (char *) malloc ((strlen (fname) + 20) * sizeof (char));
  memset (fname_inc, 0, (strlen (fname) + 20) * sizeof (char));
  // fname_pre[0] = '\0';
  sprintf (fname_inc, "%s_inc.txt", fname);

  FILE *inc = fopen (fname_inc, "w");
  int counter = 0;
#endif

  int c = 0;
  for (uint_t i = 0; i < form->pure->size; i++)
    for (uint_t j = i + 1; j < form->pure->size; j++)
      {
#ifndef NDEBUG
        fprintf (stdout, "Iteration %d %d\n", i, j);
        fflush (stdout);
#endif
        if ((form->pure->m[i][j - i] != NOLL_PURE_EQ)
            && (form->pure->m[i][j - i] != NOLL_PURE_NEQ))
          {
            uint_t type_i =
              noll_vector_at (noll_vector_at (form->lvars, i)->vty->args,
                              0);
            uint_t type_j =
              noll_vector_at (noll_vector_at (form->lvars, j)->vty->args,
                              0);
            if (type_i != type_j)       //variables of different types
              form->pure->m[i][j - i] = NOLL_PURE_NEQ;
            else
              {                 //variables of the same type
#ifndef NDEBUG
                fprintf (stdout, "**************TESTING %s and %s\n",
                         noll_vector_at (form->lvars, i)->vname,
                         noll_vector_at (form->lvars, j)->vname);
#endif
                c++;

                // Test entailment of equality
#ifndef NDEBUG
                fprintf (inc, "a -%d 0\n", encode_eq (i, j));
                fprintf (stdout, "Bound %d is ", counter);
                counter++;
#endif
                if (test_in_equality (i, j, NOLL_PURE_EQ, nbv, nbc, fname)
                    == 1)
                  {
#ifndef NDEBUG
                    fprintf (stdout, "UNSATISFIABLE\n");
                    fprintf (stdout, "New equality between %s and %s\n",
                             noll_vector_at (form->lvars, i)->vname,
                             noll_vector_at (form->lvars, j)->vname);
#endif
                    form->pure->m[i][j - i] = NOLL_PURE_EQ;
                  }
#ifndef NDEBUG
                else
                  {
                    fprintf (stdout, "SATISFIABLE\n");
                  }
#endif

                // Test entailment of inequality
#ifndef NDEBUG
                fprintf (inc, "a %d 0\n", encode_eq (i, j));
                fprintf (stdout, "Bound %d is ", counter);
                counter++;
#endif
                if (test_in_equality (i, j, NOLL_PURE_NEQ, nbv, nbc, fname)
                    == 1)
                  {
#ifndef NDEBUG
                    fprintf (stdout, "UNSATISFIABLE\n");
                    fprintf (stdout, "New inequality between %s and %s\n",
                             noll_vector_at (form->lvars, i)->vname,
                             noll_vector_at (form->lvars, j)->vname);
#endif
                    form->pure->m[i][j - i] = NOLL_PURE_NEQ;
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
  /*
   * Go back to the initial state (free memory)
   */
#ifndef NDEBUG
  fclose (inc);
#endif
  bool_abstr_free (form);
}

/**
 * Computes normal form of formula form (in place).
 * File fname will contain the boolean abstraction.
 */
void
normalize_incremental (noll_form_t * form, char *fname)
{
  if (fname == NULL || form == NULL)
    {
      printf ("File or formula does not exist\n");
      return;
    }
  /*
   * Build the boolean abstraction
   */
  int nbv, nbc;
  write_bool_abstr (form, fname, &nbv, &nbc);

  /*
   * Test the satisfiability
   * If the formula is unsatisfiable we only update the field "kind"
   */
  if (!test_satisfiability (nbv, nbc, fname))
    {
      form->kind = NOLL_FORM_UNSAT;
#ifndef NDEBUG
      printf ("+++++++++++The formula is unsatisfiable+++++++++++++\n");
#endif
      bool_abstr_free (form);
      return;
    }

  /*
   * Checking the implied (in)equalities
   */
  //all (in)equalities are written in the file "($fname)_inc.txt"
  char *fname_inc = (char *) malloc ((strlen (fname) + 20) * sizeof (char));
  memset (fname_inc, 0, (strlen (fname) + 20) * sizeof (char));
  // fname_pre[0] = '\0';
  sprintf (fname_inc, "inc_%s", fname);

  FILE *inc = fopen (fname_inc, "w");

  int c = 0;
  int counter = 0;
  noll_pure_atom *atoms_array;
  atoms_array = (noll_pure_atom *) malloc (form->pure->size * form->pure->size
                                           * sizeof (noll_pure_atom));
  for (uint_t i = 0; i < form->pure->size; i++)
    for (uint_t j = i + 1; j < form->pure->size; j++)
      {
#ifndef NDEBUG
        fprintf (stdout, "Iteration %d %d\n", i, j);
        fflush (stdout);
#endif
        if ((form->pure->m[i][j - i] != NOLL_PURE_EQ)
            && (form->pure->m[i][j - i] != NOLL_PURE_NEQ))
          {
            uint_t type_i =
              noll_vector_at (noll_vector_at (form->lvars, i)->vty->args,
                              0);
            uint_t type_j =
              noll_vector_at (noll_vector_at (form->lvars, j)->vty->args,
                              0);
            if (type_i != type_j)       //variables of different types
              form->pure->m[i][j - i] = NOLL_PURE_NEQ;
            else
              {                 //variables of the same type
#ifndef NDEBUG
                fprintf (stdout, "**************TESTING %s and %s\n",
                         noll_vector_at (form->lvars, i)->vname,
                         noll_vector_at (form->lvars, j)->vname);
#endif
                c++;

                // Entailment of equality
                fprintf (inc, "a -%d 0\n", encode_eq (i, j));
                atoms_array[counter].sign = NOLL_PURE_EQ;
                atoms_array[counter].x = i;
                atoms_array[counter].y = j;
                //fprintf (stdout,"Bound %d is ",counter);
                counter++;

                // Entailment of inequality
                fprintf (inc, "a %d 0\n", encode_eq (i, j));
                atoms_array[counter].sign = NOLL_PURE_NEQ;
                atoms_array[counter].x = i;
                atoms_array[counter].y = j;
                //fprintf (stdout,"Bound %d is ",counter);
                counter++;
              }
          }
      }

  fclose (inc);
  free (fname_inc);

  char *fname_pre = (char *) malloc ((strlen (fname) + 5) * sizeof (char));
  memset (fname_pre, 0, (strlen (fname) + 5) * sizeof (char));
  // fname_pre[0] = '\0';
  sprintf (fname_pre, "pre_%s", fname);
  FILE *out = fopen (fname_pre, "w");
  fprintf (out, "p inccnf\n");
  fclose (out);
  free (fname_pre);

  // build the final file for sat using cat
  char *command = (char *) calloc ((100 + 4 * strlen (fname)), sizeof (char));
  memset (command, 0, (100 + 4 * strlen (fname)) * sizeof (char));
  sprintf (command, "cat pre_%s %s inc_%s 1> full_%s", fname, fname, fname,
           fname);
  if (system (command) == -1)
    assert (0);

  // print the minisat command
  memset (command, 0, (100 + 4 * strlen (fname)) * sizeof (char));
  sprintf (command, "minisat_inc -verb=0 full_%s 1> results_%s",
           fname, fname);
  if (system (command) == -1)
    assert (0);

  FILE *res;

  char *fname_res = (char *) malloc ((strlen (fname) + 20) * sizeof (char));
  memset (fname_res, 0, (strlen (fname) + 20) * sizeof (char));
  // fname_pre[0] = '\0';
  sprintf (fname_res, "results_%s", fname);

  res = fopen (fname_res, "r");

  char *temp = malloc (100 * sizeof (char));
  char *eq = "equality";
  char *neq = "inequality";
  char *delim = " ";

  //printf("Here begins the problem %s %d\n", fname_res,counter);
  for (int k = 0; k < counter; k++)
    {
#ifndef NDEBUG
      printf ("Iteration %d \n", k);
      fflush (stdout);
#endif
      fscanf (res, "%s", temp);
      fscanf (res, "%s", temp);
      fscanf (res, "%s", temp);
      fscanf (res, "%s", temp);
      /*              if (fscanf(res,"%as",temp) != 4) {
         printf("Passed\n");
         continue;
         } */
      if (temp == NULL)
        {
#ifndef NDEBUG
          printf ("Passed\n");
#endif
          continue;
        }

      if (strcmp (temp, "UNSATISFIABLE") == 0)
        {
#ifndef NDEBUG
          fprintf (stdout, "New %s between %s and %s\n",
                   atoms_array[k].sign == NOLL_PURE_EQ ? eq : neq,
                   noll_vector_at (form->lvars, atoms_array[k].x)->vname,
                   noll_vector_at (form->lvars, atoms_array[k].y)->vname);
#endif
          if (atoms_array[k].x <= atoms_array[k].y)
            form->pure->m[atoms_array[k].x][atoms_array[k].y
                                            - atoms_array[k].x] =
              atoms_array[k].sign;
          else
            form->pure->m[atoms_array[k].y][atoms_array[k].x
                                            - atoms_array[k].y] =
              atoms_array[k].sign;
        }
    }
  free (temp);

  /*
   * Go back to the initial state (free memory)
   */
  free (fname_res);
  free (command);
  free (atoms_array);
  fclose (res);
  bool_abstr_free (form);
}
