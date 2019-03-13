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
 * Abstract Syntax Tree of NOLL formulas.
 */

#include<sys/time.h>

#include "noll_form.h"
#include "noll_preds.h"
#include "noll2bool.h"
#include "noll2sat.h"
#include "noll2graph.h"
#include "noll_graph.h"

NOLL_VECTOR_DEFINE (noll_dterm_array, noll_dterm_t *);

NOLL_VECTOR_DEFINE (noll_dform_array, noll_dform_t *);

NOLL_VECTOR_DEFINE (noll_space_array, noll_space_t *);

NOLL_VECTOR_DEFINE (noll_share_array, noll_atom_share_t *);

NOLL_VECTOR_DEFINE (noll_sterm_array, noll_sterm_t *);

NOLL_VECTOR_DEFINE (noll_form_array, noll_form_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

noll_logic_t noll_form_logic;

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

noll_form_t *
noll_form_new ()
{
  noll_form_t *form = (noll_form_t *) malloc (sizeof (noll_form_t));
  form->kind = NOLL_FORM_VALID;
  form->lvars = noll_var_array_new ();
  form->svars = noll_var_array_new ();
  form->pure = NULL;            //noll_pure_new();
  form->space = noll_space_new ();
  form->share = noll_share_new ();

  return form;
}

void
noll_form_free (noll_form_t * form)
{
  assert (form != NULL);
  if (form->lvars != NULL)
    {
      noll_var_array_delete (form->lvars);
      form->lvars = NULL;
    }
  if (form->svars != NULL)
    {
      noll_var_array_delete (form->svars);
      form->svars = NULL;
    }
  if (form->pure != NULL)
    {
      noll_pure_free (form->pure);
      form->pure = NULL;
    }
  if (form->space != NULL)
    {
      noll_space_free (form->space);
      form->space = NULL;
    }
  if (form->share != NULL)
    {
      noll_share_free (form->share);
      form->share = NULL;
    }
  free (form);
}

void
noll_form_set_unsat (noll_form_t * form)
{
  form->kind = NOLL_FORM_UNSAT;
  // DO NOT FREE variables, already pointed by the context
  if (form->pure != NULL)
    {
      noll_pure_free (form->pure);
      form->pure = NULL;
    }
  if (form->space != NULL)
    {
      noll_space_free (form->space);
      form->space = NULL;
    }
  if (form->share != NULL)
    {
      noll_share_free (form->share);
      form->share = NULL;
    }
}

noll_dterm_t *
noll_dterm_new (void)
{
  noll_dterm_t *ret = (noll_dterm_t *) malloc (sizeof (struct noll_dterm_s));
  ret->kind = NOLL_DATA_INT;
  ret->typ = NOLL_TYP_INT;
  ret->p.value = 0;
  ret->args = NULL;
  return ret;
}

noll_dterm_t *
noll_dterm_new_var (uint_t vid, noll_typ_t ty)
{
  noll_dterm_t *ret = (noll_dterm_t *) malloc (sizeof (struct noll_dterm_s));
  ret->kind = NOLL_DATA_VAR;
  ret->typ = ty;
  ret->p.sid = vid;
  ret->args = NULL;
  return ret;
}

void
noll_dterm_free (noll_dterm_t * d)
{
  if (d == NULL)
    return;
  if ((d->kind > NOLL_DATA_EMPTYBAG) && (d->args != NULL))
    noll_dterm_array_delete (d->args);
  free (d);
}

noll_dform_t *
noll_dform_new (void)
{
  noll_dform_t *ret = (noll_dform_t *) malloc (sizeof (struct noll_dform_s));
  ret->kind = NOLL_DATA_EMPTYBAG;
  ret->typ = NOLL_TYP_BAGINT;
  ret->p.targs = NULL;
  return ret;
}

noll_dform_t *
noll_dform_new_eq (noll_dterm_t * t1, noll_dterm_t * t2)
{
  assert (t1 != NULL);
  assert (t2 != NULL);
  assert (t1->typ == t2->typ);
  noll_dform_t *ret = (noll_dform_t *) malloc (sizeof (struct noll_dform_s));
  ret->kind = NOLL_DATA_EQ;
  ret->typ = t1->typ;
  ret->p.targs = noll_dterm_array_new ();
  noll_dterm_array_push (ret->p.targs, t1);
  noll_dterm_array_push (ret->p.targs, t2);
  return ret;
}

void
noll_dform_free (noll_dform_t * d)
{
  if (d == NULL)
    return;
  if (d->kind != NOLL_DATA_IMPLIES)
    {
      if (d->p.targs != NULL)
        noll_dterm_array_delete (d->p.targs);
    }
  else
    {
      if (d->p.bargs != NULL)
        noll_dform_array_delete (d->p.bargs);
    }
  free (d);
}

noll_pure_t *
noll_pure_new (uint_t size)
{
  noll_pure_t *ret = (noll_pure_t *) malloc (sizeof (struct noll_pure_t));
  ret->m = NULL;
  ret->size = size;
  if (ret->size > 0)
    {
      ret->m =
        (noll_pure_op_t **) malloc (ret->size * sizeof (noll_pure_op_t *));
      for (uid_t i = 0; i < ret->size; i++)
        {
          uid_t sz = ret->size - i;
          ret->m[i] =
            (noll_pure_op_t *) malloc (sz * sizeof (noll_pure_op_t));
          // set the diagonal
          ret->m[i][0] = NOLL_PURE_EQ;
          for (uid_t j = 1; j < sz; j++)
            ret->m[i][j] = NOLL_PURE_OTHER;
        }
    }
  ret->data = NULL;
  return ret;
}

void
noll_pure_free (noll_pure_t * p)
{
  if (!p)
    return;
  if (p->m)
    {
      for (uid_t i = 0; i < p->size; i++)
        if (p->m[i])
          free (p->m[i]);

      free (p->m);
    }
  if (p->data)
    {
      noll_dform_array_delete (p->data);
    }
  free (p);
}

noll_space_t *
noll_space_new ()
{
  noll_space_t *ret = (noll_space_t *) malloc (sizeof (noll_space_t));
  ret->kind = NOLL_SPACE_EMP;
  ret->is_precise = true;
  return ret;
}

void
noll_space_free (noll_space_t * s)
{
  if (!s)
    return;
  switch (s->kind)
    {
    case NOLL_SPACE_PTO:
      {
        if (noll_vector_size (s->m.pto.fields) > 0)
          {
            if (s->m.pto.fields)
              noll_uid_array_delete (s->m.pto.fields);
            if (s->m.pto.dest)
              noll_uid_array_delete (s->m.pto.dest);
          }
        break;
      }
    case NOLL_SPACE_LS:
      {
        if (s->m.ls.args && noll_vector_size (s->m.ls.args) > 0)
          noll_uid_array_delete (s->m.ls.args);
        break;
      }
    case NOLL_SPACE_WSEP:
    case NOLL_SPACE_SSEP:
      {
        noll_space_array_delete (s->m.sep);
        break;
      }
    default:
      break;
    }
  free (s);
  return;
}

noll_space_t *
noll_space_sub (noll_space_t * a, noll_uid_array * sub)
{
  if (NULL == a)
    return NULL;
  noll_space_t *r = noll_space_new ();
  r->is_precise = a->is_precise;
  r->kind = a->kind;
  switch (a->kind)
    {
    case NOLL_SPACE_PTO:
      {
        assert (a->m.pto.sid < noll_vector_size (sub));
        r->m.pto.sid = noll_vector_at (sub, a->m.pto.sid);
        r->m.pto.fields = noll_uid_array_new ();
        noll_uid_array_copy (r->m.pto.fields, a->m.pto.fields);
        r->m.pto.dest = noll_uid_array_new ();
        for (uint_t i = 0; i < noll_vector_size (a->m.pto.dest); i++)
          {
            uid_t v_old = noll_vector_at (a->m.pto.dest, i);
            assert (v_old < noll_vector_size (sub));
            uint_t v_new = noll_vector_at (sub, v_old);
            noll_uid_array_push (r->m.pto.dest, v_new);
          }
        break;
      }
    case NOLL_SPACE_LS:
      {
        r->m.ls.pid = a->m.ls.pid;
        r->m.ls.sid = a->m.ls.sid;
        r->m.ls.is_loop = a->m.ls.is_loop;
        r->m.ls.args = noll_uid_array_new ();
        for (uint_t i = 0; i < noll_vector_size (a->m.ls.args); i++)
          {
            uid_t v_old = noll_vector_at (a->m.ls.args, i);
            assert (v_old < noll_vector_size (sub));
            uint_t v_new = noll_vector_at (sub, v_old);
            noll_uid_array_push (r->m.ls.args, v_new);
          }
        break;
      }
    case NOLL_SPACE_WSEP:
    case NOLL_SPACE_SSEP:
      {
        r->m.sep = noll_space_array_new ();
        for (uint_t i = 0; i < noll_vector_size (a->m.sep); i++)
          {
            noll_space_t *sepi = noll_vector_at (a->m.sep, i);
            noll_space_t *sepi_new = noll_space_sub (sepi, sub);
            noll_space_array_push (r->m.sep, sepi_new);
          }
        break;
      }
    default:
      break;
    }

  return r;
}

noll_sterm_t *
noll_sterm_new_var (uid_t v, noll_sterm_kind_t kind)
{
  noll_sterm_t *tv = (noll_sterm_t *) malloc (sizeof (noll_sterm_t));
  tv->kind = kind;
  tv->lvar = (kind == NOLL_STERM_LVAR) ? v : UNDEFINED_ID;
  tv->svar = (kind == NOLL_STERM_SVAR) ? v : UNDEFINED_ID;
  return tv;
}

noll_sterm_t *
noll_sterm_new_prj (uid_t s, uid_t v)
{
  noll_sterm_t *tv = (noll_sterm_t *) malloc (sizeof (noll_sterm_t));
  tv->kind = NOLL_STERM_PRJ;
  tv->lvar = v;
  tv->svar = s;
  return tv;
}

noll_share_array *
noll_share_new ()
{
  return noll_share_array_new ();
}

void
noll_share_free (noll_share_array * s)
{
  if (s == NULL)
    return;
  // TODO: free also the sterms in each element
  noll_share_array_delete (s);
}

noll_sterm_t *
noll_sterm_copy (noll_sterm_t * a)
{
  if (a == NULL)
    return NULL;

  noll_sterm_t *tv = (noll_sterm_t *) malloc (sizeof (noll_sterm_t));
  tv->kind = a->kind;
  tv->lvar = a->lvar;
  tv->svar = a->svar;
  return tv;
}

int
noll_pure_add_dform (noll_pure_t * form, noll_dform_t * df)
{
  assert (form != NULL);
  assert (df != NULL);
  if (form->data == NULL)
    form->data = noll_dform_array_new ();
  noll_dform_array_push (form->data, df);
  return 1;
}

noll_form_kind_t
noll_pure_update_eq (noll_pure_t * f, uid_t l, uid_t c)
{
  assert (f);
  assert (l < c);

  if (noll_pure_matrix_at (f, l, c) == NOLL_PURE_NEQ)
    {
#ifndef NDEBUG
      fprintf (stdout, "noll_pure_update_eq(%d,%d): set unsat!\n", l, c);
#endif
      return NOLL_FORM_UNSAT;
    }
  noll_pure_matrix_at (f, l, c) = NOLL_PURE_EQ;
  return NOLL_FORM_SAT;
}

noll_form_kind_t
noll_pure_update_neq (noll_pure_t * f, uid_t l, uid_t c)
{
  assert (f);
  assert (l < c);

  if (noll_pure_matrix_at (f, l, c) == NOLL_PURE_EQ)
    {
#ifndef NDEBUG
      fprintf (stdout, "noll_pure_update_neq(%d,%d): set unsat!\n", l, c);
#endif
      return NOLL_FORM_UNSAT;
    }
  noll_pure_matrix_at (f, l, c) = NOLL_PURE_NEQ;
  return NOLL_FORM_SAT;
}

noll_form_kind_t
noll_pure_close_eq (noll_pure_t * pure, uid_t l, uid_t c)
{
  assert (pure->size > l && pure->size > c);
  assert (l < c);

  noll_form_kind_t res = NOLL_FORM_SAT;
  // close with entries < c-1
  for (uid_t j = l + 1; (j < c) && (res != NOLL_FORM_UNSAT); j++)
    {
      if ((res == NOLL_FORM_SAT) &&
          (noll_pure_matrix_at (pure, l, j) == NOLL_PURE_EQ))
        /* l = c && l = j => j = c */
        res = noll_pure_update_eq (pure, j, c);

      if ((res == NOLL_FORM_SAT) &&
          (noll_pure_matrix_at (pure, l, j) == NOLL_PURE_NEQ))
        /* l = c && l != j => j != c */
        res = noll_pure_update_neq (pure, j, c);
    }

  // close with entries > vcol
  for (uid_t j = c + 1; (j < pure->size) && (res != NOLL_FORM_UNSAT); j++)
    {
      if ((res == NOLL_FORM_SAT) &&
          (noll_pure_matrix_at (pure, l, j) == NOLL_PURE_EQ))
        /* v_lin = v_col && v_lin = j =>  v_col = j */
        res = noll_pure_update_eq (pure, c, j);

      if ((res == NOLL_FORM_SAT) &&
          (noll_pure_matrix_at (pure, l, j) == NOLL_PURE_NEQ))
        /* v_lin = v_col && v_lin != j => j != v_col */
        res = noll_pure_update_neq (pure, c, j);

      if ((res == NOLL_FORM_SAT) &&
          (noll_pure_matrix_at (pure, c, j) == NOLL_PURE_EQ))
        /* v_lin = v_col && v_col = j =>  v_lin = j */
        res = noll_pure_update_eq (pure, l, j);

      if ((res == NOLL_FORM_SAT) &&
          (noll_pure_matrix_at (pure, c, j) == NOLL_PURE_NEQ))
        /* v_lin = v_col && v_col != j => v_lin != j */
        res = noll_pure_update_neq (pure, l, j);
    }
  return res;
}

noll_form_kind_t
noll_pure_close_neq (noll_pure_t * pure, uid_t l, uid_t c)
{
  assert (pure->size > l && pure->size > c);
  assert (l < c);

  noll_form_kind_t res = NOLL_FORM_SAT;
  // close with entries < vcol-1
  for (uid_t j = l + 1; (res != NOLL_FORM_UNSAT) && (j < c); j++)
    {
      if (noll_pure_matrix_at (pure, l, j) == NOLL_PURE_EQ)
        /* v_lin != v_col && v_lin = j => j != v_col */
        res = noll_pure_update_neq (pure, j, c);
    }
  // close with entries > vcol
  for (uid_t j = c + 1; (res != NOLL_FORM_UNSAT) && (j < pure->size); j++)
    {
      if ((res == NOLL_FORM_SAT) &&
          (noll_pure_matrix_at (pure, l, j) == NOLL_PURE_EQ))
        /* v_lin != v_col && v_lin = j =>  v_col != j */
        res = noll_pure_update_neq (pure, c, j);

      if ((res == NOLL_FORM_SAT) &&
          (noll_pure_matrix_at (pure, c, j) == NOLL_PURE_EQ))
        /* v_lin != v_col && v_col = j =>  v_lin != j */
        res = noll_pure_update_neq (pure, l, j);
    }
  return res;
}

noll_form_kind_t
noll_pure_add_eq (noll_pure_t * f, uid_t v1, uid_t v2)
{
  assert (f && f->m);
  if (v1 == v2)
    /* return NOLL_FORM_SAT; */
    return NOLL_FORM_VALID;
  uid_t l = (v1 < v2) ? v1 : v2;
  uid_t c = (v1 < v2) ? v2 : v1;

  noll_form_kind_t status = noll_pure_update_eq (f, l, c);
  /// call closure 
  status = noll_pure_close_eq (f, l, c);
  return status;
}

noll_form_kind_t
noll_pure_add_neq (noll_pure_t * f, uid_t v1, uid_t v2)
{
  assert (f && f->m);
  if (v1 == v2)
    return NOLL_FORM_UNSAT;
  uid_t l = (v1 < v2) ? v1 : v2;
  uid_t c = (v1 < v2) ? v2 : v1;

  noll_form_kind_t status = noll_pure_update_neq (f, l, c);
  /// call closure
  status = noll_pure_close_neq (f, l, c);
  return status;
}

void
noll_form_add_eq (noll_form_t * f, uid_t v1, uid_t v2)
{
  assert (f != NULL);
  if (f->kind == NOLL_FORM_UNSAT)
    return;

  /// add the equality and do the closure
  f->kind = noll_pure_add_eq (f->pure, v1, v2);
  return;
}

void
noll_form_add_neq (noll_form_t * f, uid_t v1, uid_t v2)
{
  assert (f != NULL);
  if (f->kind == NOLL_FORM_UNSAT)
    return;

  /// add the equality and do the closure
  f->kind = noll_pure_add_neq (f->pure, v1, v2);
  return;
}


/* ====================================================================== */
/* Typing */
/* ====================================================================== */


/**
 * Type the formula @p form.
 * @return 0 if incorrect typing
 */
int
noll_form_type (noll_form_t * form)
{
  if (form != NULL)             // only to use form
    return 1;
  /* TODO: redo typing here */
  return 0;
}


/* ====================================================================== */
/* Getters/Setters */
/* ====================================================================== */

int
noll_form_is_unsat (noll_form_t * phi)
{
  return phi->kind == NOLL_FORM_UNSAT;
}

int
noll_form_is_sat (noll_form_t * phi)
{
  return phi->kind == NOLL_FORM_SAT;
}

int
noll_form_is_valid (noll_form_t * phi)
{
  return phi->kind == NOLL_FORM_VALID;
}

int
noll_form_array_is_unsat (noll_form_array * phi1_phiN)
{
  assert (phi1_phiN != NULL);

  /* all formulae shall be unsat */
  for (size_t i = 0; i < noll_vector_size (phi1_phiN); i++)
    if (noll_vector_at (phi1_phiN, i)->kind != NOLL_FORM_UNSAT)
      return 0;
  return 1;
}

int
noll_form_array_is_valid (noll_form_array * phi1_phiN)
{
  assert (phi1_phiN != NULL);

  /* one formula shall be valid */
  for (size_t i = 0; i < noll_vector_size (phi1_phiN); i++)
    if (noll_form_is_valid (noll_vector_at (phi1_phiN, i)))
      return 1;
  return 0;
}

/* ====================================================================== */
/* Composition/Reduction */
/* ====================================================================== */

/**
 * @brief Do the union between @p dst and @p src in @p dst 
 */
void
noll_dform_array_cup_all (noll_dform_array * dst, noll_dform_array * src)
{
  assert (dst != NULL);
  if (src == NULL)
    return;
  for (uint_t i = 0; i < noll_vector_size (src); i++)
    noll_dform_array_push (dst, noll_vector_at (src, i));       // TODO: do a cup
}

noll_dterm_t *
noll_dterm_apply (noll_dterm_t * dt, noll_uid_array * m)
{
  if (dt == NULL)
    return NULL;
  /// if m == NULL, then copy

  noll_dterm_t *res = noll_dterm_new ();
  res->kind = dt->kind;
  res->typ = dt->typ;
  switch (dt->kind)
    {
    case NOLL_DATA_INT:
      res->p.value = dt->p.value;
      break;
    case NOLL_DATA_VAR:
      if (m == NULL)
        res->p.sid = dt->p.sid;
      else if (dt->p.sid < noll_vector_size (m))
        {
          uid_t vm = noll_vector_at (m, dt->p.sid);
          if (vm != UNDEFINED_ID)
            res->p.sid = vm;
          else
            {
#ifndef NDEBUG
              fprintf (stdout,
                       "\ndterm_apply: undefined mapping for var %d!\n",
                       dt->p.sid);
#endif
              /// copy the old value
              res->p.sid = dt->p.sid;
            }
        }
      else
        {
#ifndef NDEBUG
          fprintf (stdout,
                   "\ndterm_apply: undefined mapping for var %d!\n",
                   dt->p.sid);
#endif
          res->p.sid = dt->p.sid;
        }
      break;
    case NOLL_DATA_ITE:
      {
        noll_dform_t *cond_m = noll_dform_apply (dt->p.cond, m);
        if (cond_m == NULL)
          {
            noll_dterm_free (res);
            return NULL;
          }
        res->p.cond = cond_m;
        break;
      }
    default:
      break;
    }
  /// only dterm arguments
  if (dt->args != NULL)
    {
      uint_t size = noll_vector_size (dt->args);
      res->args = noll_dterm_array_new ();
      noll_dterm_array_reserve (res->args, size);
      for (uint_t i = 0; i < size; i++)
        {
          noll_dterm_t *a = noll_dterm_apply (noll_vector_at (dt->args, i),
                                              m);
          if (a == NULL)
            {
              noll_dterm_free (res);
              return NULL;
            }
          noll_dterm_array_push (res->args, a);
        }
    }
  return res;
}

noll_dform_t *
noll_dform_apply (noll_dform_t * df, noll_uid_array * m)
{
  if (df == NULL)
    return NULL;
  /// if m == NULL, copy only
  noll_dform_t *res = noll_dform_new ();
  res->kind = df->kind;
  res->typ = df->typ;
  if (df->kind == NOLL_DATA_IMPLIES)
    {
      res->p.bargs = noll_dform_array_new ();
      noll_dform_array_reserve (res->p.bargs, 2);
      for (uint_t i = 0; i < 2; i++)
        {
          noll_dform_t *a =
            noll_dform_apply (noll_vector_at (df->p.bargs, i), m);
          if (a == NULL)
            {
              noll_dform_free (res);
              return NULL;
            }
          noll_dform_array_push (res->p.bargs, a);
        }
      return res;
    }
  /// only dterm arguments
  if (df->p.targs != NULL)
    {
      uint_t size = noll_vector_size (df->p.targs);
      res->p.targs = noll_dterm_array_new ();
      noll_dterm_array_reserve (res->p.targs, size);
      for (uint_t i = 0; i < size; i++)
        {
          noll_dterm_t *a =
            noll_dterm_apply (noll_vector_at (df->p.targs, i), m);
          if (a == NULL)
            {
              noll_dform_free (res);
              return NULL;
            }
          noll_dterm_array_push (res->p.targs, a);
        }
    }
  return res;
}


/**
 * @brief Apply the substitution @p m on @p df and generate new formulas 
 */
noll_dform_array *
noll_dform_array_apply (noll_dform_array * df, noll_uid_array * m)
{
  if (df == NULL || m == NULL)
    return NULL;
  noll_dform_array *res = noll_dform_array_new ();
  for (uint_t i = 0; i < noll_vector_size (df); i++)
    {
      noll_dform_t *dfi = noll_vector_at (df, i);
      noll_dform_t *dfi_m = noll_dform_apply (dfi, m);
      if (dfi_m == NULL)
        {
          noll_dform_array_delete (res);
          return NULL;
        }
      noll_dform_array_push (res, dfi_m);
    }
  return res;
}

/**
 * @brief Compute conjunct @p f1 & @p f2 and apply substitution @p mg2 
 */
noll_dform_array *
noll_dform_array_compose (noll_uid_array * mg2, noll_dform_array * f1,
                          noll_dform_array * f2)
{
  noll_dform_array *df1 = noll_dform_array_apply (f1, mg2);
  noll_dform_array *df2 = noll_dform_array_apply (f2, mg2);
  noll_dform_array_cup_all (df1, df2);  // copy pointers
  noll_dform_array_delete (df2);
  return df1;
}

/* ====================================================================== */
/* Solvers */
/* ====================================================================== */

/**
 * @brief Check that @p diff entails @p f->m[@p m].
 * 
 * @return 0 if some constraint not entailed, 1 otherwise
 */
int
noll_pure_check_entl (bool ** diff, uint_t dsize, noll_pure_t * f,
                      noll_uid_array * lmap,
                      noll_var_array * exvars, noll_uid_array * map,
                      noll_dform_array * df)
{
  /// this procedure could also be called for the pure part
  /// of a recursive rule, where @p f->m includes also existential vars,
  /// all shall be included in @p m 
  assert (noll_vector_size (exvars) == noll_vector_size (map));
  assert (f->size == noll_vector_size (lmap));
  noll_dform_array *dfn = noll_dform_array_new ();
  int res = 1;
  for (uint_t lv2 = 1; (lv2 < noll_vector_size (lmap)) && res; lv2++)
    {
      uint_t v2 = noll_vector_at (lmap, lv2);
      noll_type_t *ty2 = noll_var_type (exvars, v2);
      for (uint_t lv1 = 0; (lv1 < lv2) && res; lv1++)
        {
          uint_t v1 = noll_vector_at (lmap, lv1);
          noll_type_t *ty1 = noll_var_type (exvars, v1);
          noll_pure_op_t rhs_op = noll_pure_matrix_at (f, lv1, lv2);
          if (rhs_op == NOLL_PURE_OTHER)
            continue;
          uint_t nv1 = noll_vector_at (map, v1);
          uint_t nv2 = noll_vector_at (map, v2);
          if (rhs_op == NOLL_PURE_EQ)
            {
              if (ty1->kind != ty2->kind)
                {
#ifndef NDEBUG
                  fprintf (stdout,
                           "\n**** pure_check_entl: fails (typing) to prove (n%d == n%d)\n",
                           nv1, nv2);
#endif
                  res = 0;
                }
              else
                /// one or both of variables is not yet bounded to a node, 
                /// update m if the other is bounded
              if (nv1 < dsize && nv2 >= dsize)
                noll_uid_array_set (map, v2, nv1);
              else if (nv2 < dsize && nv1 >= dsize)
                noll_uid_array_set (map, v1, nv2);
              else if (ty1->kind == NOLL_TYP_RECORD)
                {
                  /// shall be equal and less than dsize
                  res = ((nv1 < dsize) && (nv2 < dsize)
                         && (nv1 == nv2)) ? 1 : 0;
#ifndef NDEBUG
                  if (res == 0)
                    fprintf (stdout,
                             "\n**** pure_check_entl: fails (record) to prove (n%d == n%d)\n",
                             nv1, nv2);
#endif

                }
              else
                {
                  /// there are nodes for data variables, generate a data constraint

                  noll_dform_t *df_eq =
                    noll_dform_new_eq (noll_dterm_new_var (v1, ty1->kind),
                                       noll_dterm_new_var (v2,
                                                           ty2->kind));
                  noll_dform_array_push (dfn, df_eq);
                }
            }
          else if ((nv1 < dsize) && (nv2 < dsize))
            {
              assert (rhs_op == NOLL_PURE_NEQ);
              bool lhs_isDiff = (nv1 != nv2);
              if (nv1 < nv2)
                lhs_isDiff = diff[nv2][nv1];
              else if (nv2 < nv1)
                lhs_isDiff = diff[nv1][nv2];
              res = (lhs_isDiff) ? 1 : 0;
            }
          else
            {
              /// inequality between unmapped vars
              /// push the constraint if vars are integer vars
              if ((ty1->kind == ty2->kind) && (ty1->kind == NOLL_TYP_INT))
                /// generate an inequality constraint for data vars
                {
                  noll_dform_t *df_eq =
                    noll_dform_new_eq (noll_dterm_new_var (v1, ty1->kind),
                                       noll_dterm_new_var (v2,
                                                           ty2->kind));
                  df_eq->kind = NOLL_DATA_NEQ;
                  noll_dform_array_push (dfn, df_eq);
                }
              else
                /// cannot be checked
                assert (0);
            }
        }
    }
  if (res == 1)
    noll_dform_array_cup_all (df, dfn);
  noll_dform_array_clear (dfn);
  return res;
}

/**
 * @brief Check that constraints on data variables from @p df1 entail @p df2 .
 */
uint_t ndform = 0;
int
noll_dform_array_check_entl (noll_var_array * lv1, noll_dform_array * df1,
                             noll_var_array * lv2, noll_uid_array * m,
                             noll_dform_array * df2)
{
  // TODO: for the moment prited out into a file
  char *fname = (char *) malloc (20 * sizeof (char));
  fname[0] = '\0';
  snprintf (fname, 20, "df-%d.txt", ndform);
  ndform++;
  FILE *f = fopen (fname, "w");
  fprintf (f, "lhs = (");
  noll_var_array_fprint (f, lv1, "[");
  fprintf (f, "] ");
  noll_dform_array_fprint (f, lv1, df1);
  fprintf (f, ") \n==>\nrhs = (");
  noll_var_array_fprint (f, lv2, "[");
  fprintf (f, "] x  [");
  for (uint_t i = 0; i < noll_vector_size (m); i++)
    fprintf (f, "%d -> %d,", i, noll_vector_at (m, i));
  fprintf (f, "] ");
  noll_dform_array_fprint (f, lv2, df2);
  fprintf (f, ") \n");
  fclose (f);
  free (fname);
  return 1;
}

/* ====================================================================== */
/* Printing */

/* ====================================================================== */

void
noll_dterm_fprint (FILE * f, noll_var_array * lvars, noll_dterm_t * dt)
{

  if (dt == NULL)
    {
      fprintf (f, "null");
      return;
    }

  switch (dt->kind)
    {
    case NOLL_DATA_INT:
      fprintf (f, "%ld", dt->p.value);
      break;
    case NOLL_DATA_VAR:
      fprintf (f, "%s", noll_var_name (lvars, dt->p.sid, dt->typ));
      break;
    case NOLL_DATA_EMPTYBAG:
      fprintf (f, "emptybag");
      break;
    case NOLL_DATA_FIELD:
      fprintf (f, "(%s ", noll_field_name (dt->p.sid));
      break;
    case NOLL_DATA_PLUS:
      fprintf (f, "(+ ");
      break;
    case NOLL_DATA_MINUS:
      fprintf (f, "(- ");
      break;
    case NOLL_DATA_BAG:
      fprintf (f, "(bag ");
      break;
    case NOLL_DATA_BAGUNION:
      fprintf (f, "(bagunion ");
      break;
    case NOLL_DATA_BAGMINUS:
      fprintf (f, "(bagminus ");
      break;
    case NOLL_DATA_ITE:
      fprintf (f, "(ite ");
      noll_dform_fprint (f, lvars, dt->p.cond);
      fprintf (f, " ");
      break;
    default:
      fprintf (f, "(error)");
      break;
    }

  if (dt->args != NULL)
    {
      for (uint_t i = 0; i < noll_vector_size (dt->args); i++)
        {
          noll_dterm_fprint (f, lvars, noll_vector_at (dt->args, i));
          fprintf (f, " ");
        }
      fprintf (f, ")");
    }
}

void
noll_dform_fprint (FILE * f, noll_var_array * lvars, noll_dform_t * df)
{
  if (df == NULL)
    {
      fprintf (f, "null\n");
      return;
    }
  if (df->kind == NOLL_DATA_IMPLIES)
    {
      fprintf (f, "(=> ");
      noll_dform_fprint (f, lvars, noll_vector_at (df->p.bargs, 0));
      noll_dform_fprint (f, lvars, noll_vector_at (df->p.bargs, 1));
      fprintf (f, ")");
      return;
    }
  switch (df->kind)
    {
    case NOLL_DATA_EQ:
      fprintf (f, "(= ");
      break;
    case NOLL_DATA_NEQ:
      fprintf (f, "(<> ");
      break;
    case NOLL_DATA_LT:
      fprintf (f, "(< ");
      break;
    case NOLL_DATA_GT:
      fprintf (f, "(> ");
      break;
    case NOLL_DATA_LE:
      fprintf (f, "(<= ");
      break;
    case NOLL_DATA_GE:
      fprintf (f, "(>= ");
      break;
    case NOLL_DATA_SUBSET:
      fprintf (f, "(subset ");
      break;
    default:
      break;                    /// print only the term
    }
  if (df->p.targs != NULL)
    for (uint_t i = 0; i < noll_vector_size (df->p.targs); i++)
      {
        noll_dterm_fprint (f, lvars, noll_vector_at (df->p.targs, i));
        fprintf (f, " ");
      }
  fprintf (f, ")");
}

void
noll_dform_array_fprint (FILE * f,
                         noll_var_array * lvars, noll_dform_array * df)
{
  if (df == NULL)
    {
      fprintf (f, "null\n");
      return;
    }

  fprintf (f, "\n(and ");
  for (uint_t i = 0; i < noll_vector_size (df); i++)
    {
      fprintf (f, "\n\t");
      noll_dform_fprint (f, lvars, noll_vector_at (df, i));
    }
  fprintf (f, "\n)\n");
}

void
noll_pure_fprint (FILE * f, noll_var_array * lvars, noll_pure_t * phi)
{
  if (!phi || !phi->m)
    {
      fprintf (f, "null\n");
      return;
    }
  for (uid_t l = 0; l < phi->size; l++)
    for (uid_t c = l; c < phi->size; c++)
      {
        fprintf (f, "%s", noll_var_name (lvars, l, NOLL_TYP_RECORD));
        switch (noll_pure_matrix_at (phi, l, c))
          {
          case NOLL_PURE_EQ:
            fprintf (f, "=");
            break;
          case NOLL_PURE_NEQ:
            fprintf (f, "<>");
            break;
          default:
            fprintf (f, "#");
            break;
          }
        fprintf (f, "%s, ", noll_var_name (lvars, c, NOLL_TYP_RECORD));
      }
  noll_dform_array_fprint (f, lvars, phi->data);
  fprintf (f, "\n");
}

void
noll_space_fprint (FILE * f,
                   noll_var_array * lvars,
                   noll_var_array * svars, noll_space_t * phi)
{
  if (phi == NULL)
    {
#ifndef NDEBUG
      fprintf (f, "(null) ");
#endif
      fprintf (f, "emp\n");
      return;
    }

#ifndef NDEBUG
  if (phi->is_precise == true)
    fprintf (f, "[precise] ");
  else
    fprintf (f, "[junk] ");
#endif
  switch (phi->kind)
    {
    case NOLL_SPACE_EMP:
      fprintf (f, "emp");
      break;
    case NOLL_SPACE_JUNK:
      fprintf (f, "junk");
      break;
    case NOLL_SPACE_PTO:
      {
        fprintf (f, "(pto  ");
        if (lvars == NULL)
          fprintf (f, "*%d ", phi->m.pto.sid);
        else
          fprintf (f, "%s ", noll_vector_at (lvars, phi->m.pto.sid)->vname);
        /* print the set of fields */
        for (size_t i = 0; i < noll_vector_size (phi->m.pto.fields); i++)
          {
            fprintf (f, "(%s %s) ",
                     noll_field_name (noll_vector_at
                                      (phi->m.pto.fields,
                                       i)),
                     noll_var_name (lvars,
                                    noll_vector_at (phi->m.pto.dest,
                                                    i), NOLL_TYP_RECORD));
          }
        /* end pto */
        fprintf (f, ")");
        break;
      }
    case NOLL_SPACE_LS:
      {
        const noll_pred_t *pred = noll_pred_getpred (phi->m.ls.pid);
        assert (NULL != pred);
        fprintf (f, "(%s_", pred->pname);
        if ((svars != NULL) && (noll_vector_size (svars) > phi->m.ls.sid))
          {
            fprintf (f, "%s", noll_vector_at (svars, phi->m.ls.sid)->vname);
          }
        else
          fprintf (f, "*%d", phi->m.ls.sid);
        for (uid_t i = 0; i < noll_vector_size (phi->m.ls.args); i++)
          {
            uint_t vi = noll_vector_at (phi->m.ls.args, i);
            if (lvars == NULL)
              fprintf (f, " *%d ", vi);
            else if (vi == VNIL_ID)
              fprintf (f, " nil ");
            else
              {
                noll_var_t *vari = noll_vector_at (lvars, vi);
                assert (vari != NULL);
                fprintf (f, " %s ", vari->vname);
              }
          }
        fprintf (f, ")");
        break;
      }
    default:
      {
        assert (phi->kind == NOLL_SPACE_WSEP || phi->kind == NOLL_SPACE_SSEP);
        if (phi->kind == NOLL_SPACE_WSEP)
          fprintf (f, "(wsep ");
        else
          fprintf (f, "(ssep ");
        for (uid_t i = 0; i < noll_vector_size (phi->m.sep); i++)
          {
            noll_space_fprint (f, lvars, svars,
                               noll_vector_at (phi->m.sep, i));
            fprintf (f, "\n\t");
          }
        fprintf (f, ")");
        break;
      }
    }
}

void
noll_share_sterm_fprint (FILE * f,
                         noll_var_array * lvars,
                         noll_var_array * svars, noll_sterm_t * t)
{
  assert (t);
  switch (t->kind)
    {
    case NOLL_STERM_LVAR:
      fprintf (f, " %s ", noll_var_name (lvars, t->lvar, NOLL_TYP_RECORD));
      break;
    case NOLL_STERM_SVAR:
      fprintf (f, " %s ", noll_var_name (svars, t->svar, NOLL_TYP_SETLOC));
      break;
    case NOLL_STERM_PRJ:
      fprintf (f, " (prj %s %s) ",
               noll_var_name (svars, t->svar, NOLL_TYP_SETLOC),
               noll_var_name (lvars, t->lvar, NOLL_TYP_RECORD));
      break;
    default:
      fprintf (f, "error");
      break;
    }
}

void
noll_share_sterm_array_fprint (FILE * f,
                               noll_var_array *
                               lvars,
                               noll_var_array * svars, noll_sterm_array * t)
{
  assert (t);
  if (noll_vector_size (t) > 1)
    fprintf (f, "(unloc ");
  for (uid_t i = 0; i < noll_vector_size (t); i++)
    {
      noll_share_sterm_fprint (f, lvars, svars, noll_vector_at (t, i));
      // fprintf (f, "\n");
    }

  if (noll_vector_size (t) > 1)
    fprintf (f, " )");
}

void
noll_share_atom_fprint (FILE * f,
                        noll_var_array * lvars,
                        noll_var_array * svars, noll_atom_share_t * phi)
{
  assert (phi);
  fprintf (f, "(");
  switch (phi->kind)
    {
    case NOLL_SHARE_IN:
      fprintf (f, "inloc ");
      break;
    case NOLL_SHARE_NI:
      fprintf (f, "not-inloc ");
      break;
    case NOLL_SHARE_SUBSET:
      fprintf (f, "leloc ");
      break;
    default:
      fprintf (f, "error ");
      break;
    }
  // fprintf (f, "\n\t");
  noll_share_sterm_fprint (f, lvars, svars, phi->t_left);
  // fprintf (f, "\n\t");
  noll_share_sterm_array_fprint (f, lvars, svars, phi->t_right);
  fprintf (f, ")");
}

void
noll_share_fprint (FILE * f,
                   noll_var_array * lvars,
                   noll_var_array * svars, noll_share_array * phi)
{
  if (!phi)
    {
      fprintf (f, "null\n");
      return;
    }
  for (uid_t i = 0; i < noll_vector_size (phi); i++)
    {
      noll_share_atom_fprint (f, lvars, svars, noll_vector_at (phi, i));
      fprintf (f, " &&\n");
    }
  fprintf (f, "true\n");
}

void
noll_form_fprint (FILE * f, noll_form_t * phi)
{
  assert (f != NULL);
  if (!phi)
    {
      fprintf (stdout, "null\n");
      return;
    }

  switch (phi->kind)
    {
    case NOLL_FORM_UNSAT:
      fprintf (f, "unsat\n");
      break;
    case NOLL_FORM_SAT:
      fprintf (f, "sat\n");
      break;
    case NOLL_FORM_VALID:
      fprintf (f, "valid\n");
      break;
    default:
      fprintf (f, "error\n");
      break;
    }
  fprintf (f, "\n\t lvars: ");
  noll_var_array_fprint (f, phi->lvars, "lvars");
  fprintf (f, "\n\t svars: ");
  noll_var_array_fprint (f, phi->svars, "svars");
  fprintf (f, "\n\t pure part: ");
  noll_pure_fprint (f, phi->lvars, phi->pure);
  fprintf (f, "\n\t shape part: ");
  noll_space_fprint (f, phi->lvars, phi->svars, phi->space);
  fprintf (f, "\n\t share part: ");
  noll_share_fprint (f, phi->lvars, phi->svars, phi->share);
}
