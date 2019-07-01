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
 * Building the boolean abstraction of NOLL formula.
 */

#include "noll2sat.h"
#include "noll_option.h"

NOLL_VECTOR_DEFINE (noll_sat_pure_array, noll_sat_pure_t *);

NOLL_VECTOR_DEFINE (noll_sat_space_array, noll_sat_space_t *);

NOLL_VECTOR_DEFINE (noll_sat_in_array, noll_sat_in_t *);

NOLL_VECTOR_DEFINE (noll_sat_array, noll_sat_t *);

/* ====================================================================== */
/* Constructors/destructors */
/* ====================================================================== */

/**
 * Build a boolean abstraction for phi
 */
noll_sat_t *
noll_sat_new (noll_form_t * phi)
{
  noll_sat_t *fsat = (noll_sat_t *) malloc (sizeof (noll_sat_t));

  fsat->form = phi;
  fsat->fname = NULL;
  fsat->finfo = NULL;
  fsat->var_pure = NULL;
  fsat->var_pto = NULL;
  fsat->var_pred = NULL;
  fsat->var_apto = NULL;
  fsat->var_inset = NULL;
  return fsat;
}

/**
 * Free the boolean abstraction
 */
void
noll_sat_free (noll_sat_t * fsat)
{
  if (fsat == NULL)
    return;

  fsat->fname = NULL;
  if (fsat->file != NULL)
    fclose (fsat->file);

  if (fsat->finfo != NULL)
    {
      if (fsat->finfo->used_lvar != NULL)
        free (fsat->finfo->used_lvar);
      if (fsat->finfo->used_svar != NULL)
        free (fsat->finfo->used_svar);
      if (fsat->finfo->used_flds != NULL)
        free (fsat->finfo->used_flds);
      if (fsat->finfo->used_pred != NULL)
        free (fsat->finfo->used_pred);
      free (fsat->finfo);
      fsat->finfo = NULL;
    }

  if (fsat->var_pure != NULL)
    {
      for (uint_t i = 0; i < noll_vector_size (fsat->form->lvars); i++)
        {
          if (fsat->var_pure[i] != NULL)
            free (fsat->var_pure[i]);
          fsat->var_pure[i] = NULL;
        }
      free (fsat->var_pure);
      fsat->var_pure = NULL;
    }

  fsat->form = NULL;
  if (fsat->var_pto != NULL)
    noll_sat_space_array_delete (fsat->var_pto);
  if (fsat->var_pred != NULL)
    noll_sat_space_array_delete (fsat->var_pred);
  if (fsat->var_apto != NULL)
    noll_sat_space_array_delete (fsat->var_apto);
  if (fsat->var_inset != NULL)
    noll_sat_in_array_delete (fsat->var_inset);

  free (fsat);
}


/* ====================================================================== */
/* Arrays of space forms */
/* ====================================================================== */

/*
 * result of a - b
 */
int
noll_sat_space_cmp (noll_sat_space_t * a, noll_sat_space_t * b)
{
  assert (a != NULL);
  assert (a->forig != NULL);
  assert (b != NULL);
  assert (b->forig != NULL);

  assert (a->forig->kind == b->forig->kind);
#ifndef NDEBUG
  // fprintf (stdout, "---- space compare: ");
  // noll_space_fprint(stdout, a->forig);
  // noll_space_fprint(stdout, b->forig);
#endif

  switch (a->forig->kind)
    {
    case NOLL_SPACE_PTO:
      {
        // lexicographic order on (x,f)
        uint_t xa = a->forig->m.pto.sid;
        uint_t xb = b->forig->m.pto.sid;
        uint_t fa = noll_vector_at (a->forig->m.pto.fields, a->m.idx);
        uint_t fb = noll_vector_at (b->forig->m.pto.fields, b->m.idx);
        if (xa < xb)
          return -1;
        if (xa > xb)
          return 1;
        // xa == xb
        if (fa < fb)
          return -1;
        if (fa > fb)
          return 1;
        // fa == fb
        return 0;
      }
    case NOLL_SPACE_LS:
      {
        // may be ls or anonymous pto depending on the value of a->m.p.var
        if (a->m.p.var == UNDEFINED_ID)
          {
            // is a ls formula, lexicographic order on (in, P, alpha)
            uint_t ina = noll_vector_at (a->forig->m.ls.args, 0);
            uint_t inb = noll_vector_at (b->forig->m.ls.args, 0);
            uint_t pida = a->forig->m.ls.pid;
            uint_t pidb = b->forig->m.ls.pid;
            uint_t sa = a->forig->m.ls.sid;
            uint_t sb = b->forig->m.ls.sid;

            if (ina < inb)
              return -1;
            if (ina > inb)
              return 1;
            // ina == inb
            if (pida < pidb)
              return -1;
            if (pida > pidb)
              return 1;
            // pida == pidb
            if (sa < sb)
              return -1;
            if (sa > sb)
              return 1;
            // sa == sb
            return 0;
          }
        else
          {
            // is a anonymous pto, order on (var, fld, sid)
            uint_t va = a->m.p.var;
            uint_t vb = b->m.p.var;
            uint_t fa = a->m.p.fld;
            uint_t fb = b->m.p.fld;
            uint_t sa = a->forig->m.ls.sid;
            uint_t sb = b->forig->m.ls.sid;
            if (va < vb)
              return -1;
            if (va > vb)
              return 1;
            // va == vb
            if (fa < fb)
              return -1;
            if (fa > fb)
              return 1;
            // fa == fb
            if (sa < sb)
              return -1;
            if (sa > sb)
              return 1;
            // sa == sb
            return 0;
          }
        break;
      }
    default:
      assert (0);
      break;
    }
  return -1;
}

void
noll_sat_space_array_swap_at (noll_sat_space_array * a, uint_t i, uint_t j)
{
  noll_sat_space_t *tmp = noll_vector_at (a, i);
  noll_vector_at (a, i) = noll_vector_at (a, j);
  noll_vector_at (a, j) = tmp;
}

void
noll_sat_space_array_quickSort (noll_sat_space_array * a, int left, int right)
{
  if (left > right)
    return;
  int i = left;
  int j = right;
  int tmp = left + ((right - left) / 2);
#ifndef NDEBUG
  //fprintf (stdout, "---- quicksort between %d,%d pivot pos %d\n", left, right, tmp);
  //fflush (stdout);
#endif
  noll_sat_space_t *pivot = noll_vector_at (a, tmp);
#ifndef NDEBUG
  //noll_space_fprint (stdout, pivot->forig);
  //fflush (stdout);
#endif
  /* partition */
  while (i <= j)
    {
#ifndef NDEBUG
      // fprintf (stdout, "---- quicksort between %d,%d \n", i, j);
      // fflush (stdout);
#endif
      while (noll_sat_space_cmp (noll_vector_at (a, i), pivot) < 0)
        i++;
      while (noll_sat_space_cmp (noll_vector_at (a, j), pivot) > 0)
        j--;
      if (i <= j)
        {
          noll_sat_space_array_swap_at (a, i, j);
          i++;
          j--;
        }
    }
  /* recursion */
  if (left < j)
    noll_sat_space_array_quickSort (a, left, j);
  if (i < right)
    noll_sat_space_array_quickSort (a, i, right);
}

void
noll_sat_space_array_sort (noll_sat_space_array * a)
{
#ifndef NDEBUG
  fprintf (stdout, "---- space array to be sorted: \n[");
  for (uint_t i = 0; i < noll_vector_size (a); i++)
    {
      fprintf (stdout, "\n%d: ", i);
      noll_space_fprint (stdout, NULL, NULL, (noll_vector_at (a, i))->forig);
    }
  fprintf (stdout, "\n]\n");
#endif
  /* use quicksort */
  noll_sat_space_array_quickSort (a, 0, noll_vector_size (a) - 1);

#ifndef NDEBUG
  fprintf (stdout, "---- space array sorted: \n[");
  for (uint_t i = 0; i < noll_vector_size (a); i++)
    {
      fprintf (stdout, "\n%d: ", i);
      noll_space_fprint (stdout, NULL, NULL, (noll_vector_at (a, i))->forig);
    }
  fprintf (stdout, "\n]\n");
#endif
}

uint_t
noll_sat_space_array_bsearch (noll_sat_space_array * a,
                              noll_sat_space_t * target)
{
  if (noll_vector_size (a) == 0)
    return 0;
#ifndef NDEBUG
  /*
     fprintf (stdout, "++++ bsearch of ");
     noll_space_fprint(stdout, target->forig);
     fprintf (stdout, " in [");
     for (uint_t i = 0; i < noll_vector_size(a); i++)
     noll_space_fprint(stdout, noll_vector_at(a,i)->forig);
     fprintf (stdout, "]\n");
     fflush (stdout);
   */
#endif

  uint_t min = 0;
  uint_t max = noll_vector_size (a) - 1;
  uint_t pos = 0;
  while (min < max)
    {
      pos = min + ((max - min) / 2);
      int cmp = noll_sat_space_cmp (noll_vector_at (a, pos), target);
#ifndef NDEBUG
      /*
         fprintf (stdout, "++++ bsearch space between: %d,%d at pos %d\n", min, max, pos);
         fprintf (stdout, "++++ space compare: return %d\n", cmp);
       */
#endif
      if (cmp < 0)
        min = pos + 1;
      else if (cmp > 0)
        max = pos - 1;
      else
        min = max = pos;
    }
  // position is at min = max
  if (noll_sat_space_cmp (noll_vector_at (a, min), target) != 0)
    pos = noll_vector_size (a); // unknown
  else
    pos = min;
  return pos;
}

uint_t
noll_sat_in_array_bsearch (noll_sat_in_array * a, uint_t x, uint_t alpha)
{
  if (noll_vector_size (a) == 0)
    return 0;
#ifndef NDEBUG
  /*
     fprintf (stdout, "++++ bsearch of (%d,%d) in [", x, alpha);
     for (uint_t i = 0; i < noll_vector_size(a); i++)
     fprintf (stdout, "(%d,%d),", noll_vector_at(a,i)->x, noll_vector_at(a,i)->alpha);
     fprintf (stdout, "]\n");
     fflush (stdout);
   */
#endif
  uint_t min = 0;
  uint_t max = noll_vector_size (a) - 1;
  uint_t pos = 0;
  while (min < max)
    {
      pos = min + ((max - min) / 2);
      int cmp = 0;
      noll_sat_in_t *a_pos = noll_vector_at (a, pos);
      if (a_pos->x < x)
        cmp = -1;
      else if (a_pos->x > x)
        cmp = 1;
      else
        {                       // x == a_pos->x
          if (a_pos->alpha < alpha)
            cmp = -1;
          else if (a_pos->alpha > alpha)
            cmp = 1;
        }
#ifndef NDEBUG
      /*
         fprintf (stdout, "++++ bsearch space between: %d,%d at pos %d\n", min, max, pos);
         fprintf (stdout, "++++ space compare: return %d\n", cmp);
       */
#endif
      if (cmp < 0)
        min = pos + 1;
      else if (cmp > 0)
        max = pos - 1;
      else
        min = max = pos;
    }
  // position is at min = max
  if ((noll_vector_at (a, min)->x != x)
      || (noll_vector_at (a, min)->alpha != alpha))
    pos = noll_vector_size (a); // unknown
  else
    pos = min;
  return pos;
}

/* ====================================================================== */
/* Collect information for boolean abstraction */
/* ====================================================================== */

noll_form_info_t *
noll2sat_info_alloc (noll_form_t * form)
{
  noll_form_info_t *res =
    (noll_form_info_t *) malloc (sizeof (noll_form_info_t));
  res->used_lvar =
    (bool *) malloc (sizeof (bool) * noll_vector_size (form->lvars));
  for (uint_t i = 0; i < noll_vector_size (form->lvars); i++)
    res->used_lvar[i] = false;
  res->used_svar =
    (bool *) malloc (sizeof (bool) * noll_vector_size (form->svars));
  for (uint_t i = 0; i < noll_vector_size (form->svars); i++)
    res->used_svar[i] = false;
  res->used_pred =
    (bool *) malloc (sizeof (bool) * noll_vector_size (preds_array));
  for (uint_t i = 0; i < noll_vector_size (preds_array); i++)
    res->used_pred[i] = false;
  res->used_flds =
    (bool *) malloc (sizeof (bool) * noll_vector_size (fields_array));
  for (uint_t i = 0; i < noll_vector_size (fields_array); i++)
    res->used_flds[i] = false;
  res->lvar_size = 0;
  res->svar_size = 0;
  res->fld_size = 0;
  res->pto_size = 0;
  res->ls_size = 0;

  return res;
}

void
noll2sat_info_pure (noll_pure_t * f, noll_sat_t * res)
{
  if (f == NULL)
    return;
  assert (res != NULL);

  /// only location vars are considered
  uint_t rec = UNDEFINED_ID;
  for (uint_t i = 0; i < f->size; i++)
    {
      rec = noll_var_record (res->form->lvars, i);
      if (rec == UNDEFINED_ID)
        continue;
      for (uint_t j = i + 1; j < f->size; j++)
        {
          rec = noll_var_record (res->form->lvars, j);
          if (rec == UNDEFINED_ID)
            continue;
          if (noll_pure_matrix_at (f, i, j) != NOLL_PURE_OTHER)
            {
              res->finfo->used_lvar[i] = true;
              res->finfo->used_lvar[j] = true;
            }
        }
    }
}

void
noll2sat_info_space (noll_space_t * f, noll_sat_t * res)
{
  if (f == NULL)
    return;
  assert (res != NULL);

  switch (f->kind)
    {
    case NOLL_SPACE_PTO:
      res->finfo->used_lvar[f->m.pto.sid] = true;       /// it is a location var
      uint_t size = 0;
      for (uint_t i = 0; i < noll_vector_size (f->m.pto.fields); i++)
        {
          uint_t fi = noll_vector_at (f->m.pto.fields, i);
          uint_t vi = noll_vector_at (f->m.pto.dest, i);
          uint_t ri = noll_var_record (res->form->lvars, vi);
          if (ri == UNDEFINED_ID)
            continue;
          if (res->finfo->used_lvar[vi] == false)
            {
              res->finfo->used_lvar[vi] = true;
              res->finfo->lvar_size++;
            }
          if (res->finfo->used_flds[fi] == false)
            {
              res->finfo->used_flds[fi] = true;
              res->finfo->fld_size++;
            }
          noll_sat_space_t *pto_i =
            (noll_sat_space_t *) malloc (sizeof (noll_sat_space_t));
          pto_i->forig = f;
          pto_i->m.idx = i;
          noll_sat_space_array_push (res->var_pto, pto_i);
          size++;
        }
      res->finfo->pto_size += size;     //noll_vector_size (f->m.pto.fields);
      break;

    case NOLL_SPACE_LS:
      res->finfo->used_pred[f->m.ls.pid] = true;
      if (res->finfo->used_svar[f->m.ls.sid] == false)
        {
          res->finfo->used_svar[f->m.ls.sid] = true;
          res->finfo->svar_size++;
        }
      for (uint_t i = 0; i < noll_vector_size (f->m.ls.args); i++)
        {
          uint_t ai = noll_vector_at (f->m.ls.args, i);
          uint_t ri = noll_var_record (res->form->lvars, ai);
          if (ri == UNDEFINED_ID)
            continue;           // consider only location args
          if (res->finfo->used_lvar[ai] == false)
            {
              res->finfo->used_lvar[ai] = true;
              res->finfo->lvar_size++;
            }
        }
      noll_sat_space_t *pred =
        (noll_sat_space_t *) malloc (sizeof (noll_sat_space_t));
      pred->forig = f;
      pred->m.p.var = UNDEFINED_ID;
      pred->m.p.fld = UNDEFINED_ID;
      noll_sat_space_array_push (res->var_pred, pred);
      res->finfo->ls_size++;
      break;

    case NOLL_SPACE_WSEP:
    case NOLL_SPACE_SSEP:
      for (uint_t i = 0; i < noll_vector_size (f->m.sep); i++)
        noll2sat_info_space ((noll_space_t *) noll_vector_at (f->m.sep, i),
                             res);
      break;
    default:
      break;
    }
  return;
}

void
noll2sat_info_share (noll_atom_share_t * f, noll_sat_t * res)
{
  if (f == NULL || res == NULL)
    return;

  /// all built over location vars, no test needed
  if (f->t_left->kind == NOLL_STERM_LVAR)
    {
      if (res->finfo->used_lvar[f->t_left->lvar] == false)
        {
          res->finfo->used_lvar[f->t_left->lvar] = true;
          res->finfo->lvar_size++;
        }
    }
  else if ((f->t_left->kind == NOLL_STERM_SVAR)
           || (f->t_left->kind == NOLL_STERM_PRJ))
    {
      if (res->finfo->used_svar[f->t_left->svar] == false)
        {
          res->finfo->used_svar[f->t_left->svar] = true;
          res->finfo->svar_size++;
        }
    }
  for (uint_t i = 0; i < noll_vector_size (f->t_right); i++)
    {
      noll_sterm_t *ti = noll_vector_at (f->t_right, i);
      if (ti->kind == NOLL_STERM_LVAR)
        {
          if (res->finfo->used_lvar[ti->lvar] == false)
            {
              res->finfo->used_lvar[ti->lvar] = true;
              res->finfo->lvar_size++;
            }
        }
      else if ((ti->kind == NOLL_STERM_SVAR) || (ti->kind == NOLL_STERM_PRJ))
        {
          if (res->finfo->used_svar[ti->svar] == false)
            {
              res->finfo->used_svar[ti->svar] = true;
              res->finfo->svar_size++;
            }
        }
    }

}

void
noll2sat_info (noll_form_t * form, noll_sat_t * res)
{
  if (form == NULL || res == NULL)
    return;

  noll2sat_info_pure (form->pure, res);
  noll2sat_info_space (form->space, res);
  if (form->share != NULL)
    for (uint_t i = 0; i < noll_vector_size (form->share); i++)
      noll2sat_info_share (noll_vector_at (form->share, i), res);
  // 'nil' shall always be used
  if (res->finfo->used_lvar[0] == false)
    res->finfo->used_lvar[0] = true;

#ifndef NDEBUG1
  fprintf (stdout, "\n=== Collected info for formula: ");
  fprintf (stdout, "\n\t\t used vars: [");
  for (uint_t i = 0; i < noll_vector_size (form->lvars); i++)
    if (res->finfo->used_lvar[i] == true)
      fprintf (stdout, "%d: %s, ", i,
               ((noll_var_t *) noll_vector_at (form->lvars, i))->vname);
  fprintf (stdout, "]\n\t\t used svars: [");
  for (uint_t i = 0; i < noll_vector_size (form->svars); i++)
    if (res->finfo->used_svar[i] == true)
      fprintf (stdout, "%s, ",
               ((noll_var_t *) noll_vector_at (form->svars, i))->vname);
  fprintf (stdout, "]\n\t\t used preds: [");
  for (uint_t i = 0; i < noll_vector_size (preds_array); i++)
    if (res->finfo->used_pred[i] == true)
      fprintf (stdout, "%s, ", (noll_pred_getpred (i))->pname);
  fprintf (stdout, "]\n\t\t used fields: [");
  for (uint_t i = 0; i < noll_vector_size (fields_array); i++)
    if (res->finfo->used_flds[i] == true)
      fprintf (stdout, "%s, ",
               ((noll_field_t *) noll_vector_at (fields_array, i))->name);
  fprintf (stdout, "]");
  fprintf (stdout, "\n\t\t #pto atoms %d", res->finfo->pto_size);
  fprintf (stdout, "\n\t\t #pred atoms %d\n", res->finfo->ls_size);
#endif

}

noll_sat_t *
noll2sat_fill_bvar (noll_form_t * form, char *fname)
{
  /* pre-conditions: all inputs shall be != NULL */
  assert (form != NULL);
  assert (fname != NULL);

  noll_sat_t *res = (noll_sat_t *) malloc (sizeof (noll_sat_t));
  res->form = form;
  res->fname = fname;           /* TODO: copy? */
  res->file = fopen (fname, "w");
  if (res->file == NULL)
    {
#ifndef NDEBUG
      fprintf (stdout, "\nError: while open file %s! quit.\n", fname);
#endif
      free (res);
      return NULL;
    }

  res->finfo = noll2sat_info_alloc (form);

  res->no_clauses = 0;
  res->no_vars = 0;             /* max used number for boolean vars */

  // fill infos about formula, including var_pto and var_pred arrays
  res->var_pto = noll_sat_space_array_new ();
  res->var_pred = noll_sat_space_array_new ();
  noll2sat_info (form, res);

  /* fill bvars used for [x = y] encoding only for used variables in phi */
  res->start_pure = 1;          /* 0 index is used to signal clause end */
  res->size_pure = 0;
  res->size_var_pure = noll_vector_size (form->lvars);
  res->var_pure = (uint_t **) malloc (sizeof (uint_t *) * res->size_var_pure);
  for (uint_t i = 0; i < res->size_var_pure; i++)
    {
      if (res->finfo->used_lvar[i] == true)
        {
          res->var_pure[i] = (uint_t *) malloc (sizeof (uint_t) * (i + 1));
          for (uint_t j = 0; j <= i; j++)
            {
              if (res->finfo->used_lvar[j] == true)
                res->var_pure[i][j] = (res->size_pure++) + res->start_pure;
              else
                res->var_pure[i][j] = 0;
            }
        }
      else
        {
          res->var_pure[i] = NULL;
        }
    }

  /* fill bvars used for pto */
  res->start_pto = res->start_pure + res->size_pure;
  res->size_pto = res->finfo->pto_size;
  noll_sat_space_array_resize (res->var_pto, res->size_pto);
  noll_sat_space_array_sort (res->var_pto);

  /* fill bvars used for ls atoms in form */
  res->start_pred = res->start_pto + res->size_pto;
  res->size_pred = res->finfo->ls_size;
  noll_sat_space_array_resize (res->var_pred, res->size_pred);
  noll_sat_space_array_sort (res->var_pred);

  /* fill bvars used for anonymous points-to constraints [x,f,space_atom] */
  res->start_apto = res->start_pred + res->size_pred;
  res->size_apto = 0;           /* computed below */
  res->var_apto = noll_sat_space_array_new ();
  // ignore 'nil'
  for (uint_t xi = 1; xi < noll_vector_size (form->lvars); xi++)
    if (res->finfo->used_lvar[xi] == true)
      {
        noll_var_t *x = noll_vector_at (form->lvars, xi);
        uint_t tid_x = noll_var_record (form->lvars, xi);
        if (tid_x == UNDEFINED_ID)
          continue;             // ignore non location vars
        for (uint_t lsi = 0; lsi < noll_vector_size (res->var_pred); lsi++)
          {
            noll_space_t *ls =
              ((noll_sat_space_t *)
               noll_vector_at (res->var_pred, lsi))->forig;
            uint_t ls_pid = ls->m.ls.pid;
            // see all fields 
            /* MS: change of info on fields */
            for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
              {
                if (noll_pred_is_field (ls_pid, fid, NOLL_PFLD_NESTED))
                  {
                    uint_t fld_tid_src =
                      noll_vector_at (fields_array, fid)->src_r;
                    if (tid_x == fld_tid_src)
                      {
                        noll_sat_space_t *new_sat =
                          (noll_sat_space_t *)
                          malloc (sizeof (noll_sat_space_t));
                        new_sat->forig = ls;
                        new_sat->m.p.var = xi;
                        new_sat->m.p.fld = fid;
                        noll_sat_space_array_push (res->var_apto, new_sat);
                        res->size_apto++;
                      }
                  }
              }
          }
      }
  noll_sat_space_array_resize (res->var_apto, res->size_apto);
  noll_sat_space_array_sort (res->var_apto);

  /* fill bvars used for sharing constraints [x in alpha] */
  res->start_inset = res->start_apto + res->size_apto;
  res->size_inset = 0;          // computed below
  res->var_inset = noll_sat_in_array_new ();
  /* the array is generated lexically sorted (x, alpha) */
  // ignore 'nil'
  for (uint_t xi = 1; xi < noll_vector_size (form->lvars); xi++)
    {
      if (res->finfo->used_lvar[xi] == true)
        {
          for (uint_t alpha_i = 0; alpha_i < noll_vector_size (form->svars);
               alpha_i++)
            {
              if (res->finfo->used_svar[alpha_i] == true)
                {
                  noll_sat_in_t *new_bvar =
                    (noll_sat_in_t *) malloc (sizeof (noll_sat_in_t));
                  new_bvar->alpha = alpha_i;
                  new_bvar->x = xi;
                  noll_sat_in_array_push (res->var_inset, new_bvar);
                  res->size_inset++;
                }
            }
        }
    }
  noll_sat_in_array_resize (res->var_inset, res->size_inset);
  // already sorted

  res->no_vars = res->start_inset + res->size_inset;

#ifndef NDEBUG
  fprintf (stdout, "===== Set of bvar generated: of size %d\n", res->no_vars);
  fprintf (stdout, "\t - [x = y]: start %d number %d\n", res->start_pure,
           res->size_pure);
  fprintf (stdout, "\t - [x,f,y]: start %d number %d\n", res->start_pto,
           res->size_pto);
  fprintf (stdout, "\t - [P_alpha]: start %d number %d\n", res->start_pred,
           res->size_pred);
  fprintf (stdout, "\t - [x,f,P]: start %d number %d\n", res->start_apto,
           res->size_apto);
  fprintf (stdout, "\t - [x in alpha]: start %d number %d\n",
           res->start_inset, res->size_inset);
#endif

  return res;
}

/* ====================================================================== */
/* Auxiliary function */
/* ====================================================================== */

/**
 * Test if type is covered by the predicate bound to svar.
 * @param type  index of the record
 * @param svar  set of location variable
 * @return 1 if covered, 0 if not, -1 if svar is not bound
 */
int
type_in_pred_of_svar (noll_sat_t * fsat, uint_t type, uint_t svar)
{
  uint_t i = 0;
  for (; i < noll_vector_size (fsat->var_pred); i++)
    {
      noll_sat_space_t *ls_i = noll_vector_at (fsat->var_pred, i);
      if (ls_i->forig->m.ls.sid != svar)
        continue;
      const noll_pred_t *pred_i = noll_pred_getpred (ls_i->forig->m.ls.pid);
      assert (NULL != pred_i);
      noll_pred_typing_t *typ_pred_i = pred_i->typ;
      if (typ_pred_i->ptype0 == type)
        return 1;
      // search in other types of the predicate
      for (uint_t t = 0; t < noll_vector_size (typ_pred_i->ptypes); t++)
        if (type == noll_vector_at (typ_pred_i->ptypes, t))
          return 1;
    }
  if (i >= noll_vector_size (fsat->var_pred))
    // there is no predicate for this svar
    return -1;
  // the type is not in the predicate
  return 0;
}

/* ====================================================================== */
/* Access variables of the boolean abstraction */
/* ====================================================================== */

uint_t
noll2sat_get_bvar_eq (noll_sat_t * fsat, uint_t vi, uint_t vj)
{
  uint_t vcol = (vi > vj) ? vj : vi;    // min
  uint_t vlin = (vi >= vj) ? vi : vj;   // max
  uint_t *vlin_array = fsat->var_pure[vlin];
  if ((vlin_array == NULL) || (vlin_array[vcol] == 0))
    return 0;                   // not encoded
  return vlin_array[vcol];
}

uint_t
noll2sat_get_bvar_pto (noll_sat_t * fsat, noll_space_t * subform, uint_t i)
{
  assert (fsat != NULL);
  assert (subform != NULL);

  /* Binary search of information in a sorted array and
   * return the position in the array.
   */
  if (fsat->var_pto == NULL || noll_vector_size (fsat->var_pto) == 0)
    return 0;

  noll_sat_space_t *target =
    (noll_sat_space_t *) malloc (sizeof (noll_sat_space_t));
  target->forig = subform;
  target->m.idx = i;

  uint_t pos = noll_sat_space_array_bsearch (fsat->var_pto, target);
  if (pos < noll_vector_size (fsat->var_pto))
    pos += fsat->start_pto;
  else
    pos = 0;
  target->forig = NULL;
  free (target);
  return pos;
}

uint_t
noll2sat_get_bvar_pred (noll_sat_t * fsat, noll_space_t * subform,
                        uint_t vin, uint_t pid, uint_t sid)
{
  if ((&vin != &vin) || (&pid != &pid) || (&sid != &sid))
    {
      assert (0);               // just to remove "unused variable" warning
    }

  assert (fsat != NULL);
  assert (subform != NULL);

  /* Binary search of information in a sorted array and
   * return the position in the array.
   */
  if (fsat->var_pred == NULL || noll_vector_size (fsat->var_pred) == 0)
    return 0;
  noll_sat_space_t *target =
    (noll_sat_space_t *) malloc (sizeof (noll_sat_space_t));
  target->forig = subform;
  target->m.p.var = UNDEFINED_ID;

  uint_t pos = noll_sat_space_array_bsearch (fsat->var_pred, target);
  if (pos < noll_vector_size (fsat->var_pred))
    pos += fsat->start_pred;
  else
    pos = 0;
  target->forig = NULL;
  free (target);
  return pos;
}

int
noll2sat_get_sat_pure (noll_sat_t * fsat, uint_t bvar,
                       uint_t * vi, uint_t * vj)
{
  assert (fsat != NULL);

  // pure formulas are encoded in bvar
  // between [fsat->start_pure, fsat->start_pto)
  if (bvar < fsat->start_pure || bvar >= fsat->start_pto)
    return -1;
  uint_t ivar = fsat->start_pure;
  bool found = false;
  for (uint_t i = 0; i < fsat->size_var_pure && !found; i++)
    {
      if (fsat->var_pure[i] != NULL && bvar < (ivar + i + 1))
        {
          for (uint_t j = 0; j <= i; j++)
            {
              if (fsat->var_pure[i][j] == bvar)
                {
                  *vi = i;
                  *vj = j;
                  found = true;
                }
            }
        }
      else
        ivar += (i + 1);
    }
  if (!found)
    return -1;
  return 1;
}


noll_sat_space_t *
noll2sat_get_sat_space (noll_sat_t * fsat, uint_t bvar)
{
  assert (fsat != NULL);

  // space formulas are encoded in bvar
  // between [fsat->start_pto, fsat->start_apto)
  if (bvar < fsat->start_pto || bvar >= fsat->start_apto)
    return NULL;
  if (bvar < fsat->start_pred)  // a pto
    return noll_vector_at (fsat->var_pto, bvar - fsat->start_pto);
  else
    return noll_vector_at (fsat->var_pred, bvar - fsat->start_pred);
}

uint_t
noll2sat_get_bvar_in (noll_sat_t * fsat, uint_t x, uint_t alpha)
{
  assert (fsat != NULL);

  // binary search x in fsat->var_in
  uint_t pos = noll_sat_in_array_bsearch (fsat->var_inset, x, alpha);
  if (pos < noll_vector_size (fsat->var_inset))
    pos += fsat->start_inset;
  else
    pos = 0;
  return pos;
}

uint_t
noll2sat_get_bvar_apto (noll_sat_t * fsat, uint_t x, uint_t f,
                        noll_space_t * forig)
{
  assert (fsat != NULL);
  assert (forig != NULL);

  /* Binary search of information in a sorted array and
   * return the position in the array.
   */
  if (fsat->var_apto == NULL || noll_vector_size (fsat->var_apto) == 0)
    return 0;
  noll_sat_space_t *target =
    (noll_sat_space_t *) malloc (sizeof (noll_sat_space_t));
  target->forig = forig;
  target->m.p.var = x;
  target->m.p.fld = f;

  uint_t pos = noll_sat_space_array_bsearch (fsat->var_apto, target);
  if (pos < noll_vector_size (fsat->var_apto))
    pos += fsat->start_apto;
  else
    pos = 0;
  free (target);
  return pos;
}

/* ====================================================================== */
/* Printing the boolean abstraction */
/* ====================================================================== */

/**
 * @brief Build a boolean abstraction from @p form in file fname.
 * If form is unsat, return NULL;
 */
noll_sat_t *
noll2sat (noll_form_t * form, char *fname)
{

  if (form->kind == NOLL_FORM_UNSAT)
    return NULL;

  // initialize the variables of the boolean abstraction
  noll_sat_t *fsat = noll2sat_fill_bvar (form, fname);

  // print the boolean abstraction and update the number of clauses
  int nb_clauses = 0;
#ifndef NDEBUG
  fprintf (stdout, "---- F(Pi) and F_eq\n");
#endif
  nb_clauses = noll2sat_pure (fsat);
#ifndef NDEBUG
  fprintf (stdout, "Clauses for F(Pi) and F_eq = %d\n", nb_clauses);
  fprintf (stdout, "---- F(Sigma)\n");
#endif
  nb_clauses = noll2sat_space (fsat);
#ifndef NDEBUG
  fprintf (stdout, "Clauses for F(Sigma) = %d\n", nb_clauses);
  fprintf (stdout, "---- F_in\n");
#endif
  nb_clauses = noll2sat_membership (fsat);
#ifndef NDEBUG
  fprintf (stdout, "Clauses for F_in = %d\n", nb_clauses);
  fprintf (stdout, "---- F_det\n");
#endif
  nb_clauses = noll2sat_det (fsat);
#ifndef NDEBUG
  fprintf (stdout, "Clauses for F_det = %d\n", nb_clauses);
  fprintf (stdout, "---- F(Lambda)\n");
#endif
  nb_clauses = noll2sat_share (fsat);
#ifndef NDEBUG
  fprintf (stdout, "Clauses for F(Lambda) = %d\n", nb_clauses);
  fprintf (stdout, "Clauses for final formula = %d\n", fsat->no_clauses);
#endif
  fclose (fsat->file);
  fsat->file = NULL;

  // DO NOT free the boolean abstraction, fsat, needed further
  return fsat;
}

/*
 * return the number of clauses generated
 */
int
noll2sat_pure (noll_sat_t * fsat)
{
  assert (fsat != NULL);
  assert (fsat->file != NULL);
  assert (fsat->form != NULL);

  // variables shall be generated
  assert (fsat->var_pure != NULL);

  int nb_clauses = 0;

  // deal with empty pure formulas
  uint_t size = noll_vector_size (fsat->form->lvars);
  if ((fsat->form->pure != NULL) && (fsat->form->pure->size != size))
    {
      noll_pure_free (fsat->form->pure);
      fsat->form->pure = NULL;
    }
  if (fsat->form->pure == NULL)
    fsat->form->pure = noll_pure_new (size);

  // only used, location variables are considered
  for (uint_t i = 0; i < fsat->form->pure->size; i++)
    {
      uint_t typ_i = noll_var_record (fsat->form->lvars, i);
      if (typ_i == UNDEFINED_ID)
        continue;
      if (fsat->finfo->used_lvar[i] == true)
        {
          // write reflexivity
          uint_t eq_i_i = noll2sat_get_bvar_eq (fsat, i, i);
          fprintf (fsat->file, "%d 0\n", eq_i_i);
          nb_clauses++;

          // write pure formula and transitivity
          for (uint_t j = i + 1; j < fsat->form->pure->size; j++)
            {
              uint_t typ_j = noll_var_record (fsat->form->lvars, j);
              if (typ_j == UNDEFINED_ID)
                continue;
              if (fsat->finfo->used_lvar[j] == true)
                {

                  uint_t eq_i_j = noll2sat_get_bvar_eq (fsat, i, j);
                  // write pure formula
                  noll_pure_op_t op =
                    noll_pure_matrix_at (fsat->form->pure, i, j);
                  if (op == NOLL_PURE_EQ)
                    {
#ifndef NDEBUG
                      fprintf (stdout, "---- pure: [x%d = x%d]\n", i, j);
#endif
                      fprintf (fsat->file, "%d 0\n", eq_i_j);
                      nb_clauses++;
                    }
                  else if (op == NOLL_PURE_NEQ)
                    {
#ifndef NDEBUG
                      fprintf (stdout, "---- pure: [x%d <> x%d]\n", i, j);
#endif
                      fprintf (fsat->file, "-%d 0\n", eq_i_j);
                      nb_clauses++;
                    }

                  // write pure induced by typing
                  // take into account 'nil' of type NOLL_TYP_VOID
                  if ((typ_i != NOLL_TYP_VOID) &&
                      (typ_j != NOLL_TYP_VOID) && (typ_i != typ_j))
                    {
                      fprintf (fsat->file, "-%d 0\n", eq_i_j);
                      nb_clauses++;
                    }

                  // write transitivity
                  for (uint_t k = 0; k < fsat->form->pure->size; k++)
                    {
                      if (fsat->finfo->used_lvar[k] == true)
                        {
                          uint_t eq_i_k = noll2sat_get_bvar_eq (fsat, i, k);
                          uint_t eq_j_k = noll2sat_get_bvar_eq (fsat, j, k);
                          //fprintf (fsat->file, "-%d -%d %d 0\n", eq_i_j,
                          //        eq_j_k, eq_i_k);
                          fprintf (fsat->file, "-%d -%d %d 0\n", eq_i_k,
                                   eq_j_k, eq_i_j);
#ifndef NDEBUG
                          fprintf (stdout,
                                   "---- pure: trans[x%d=x%d] by x%d\n", i, j,
                                   k);
#endif
                          nb_clauses++;
                        }
                    }
                }
            }
        }
    }
  fsat->no_clauses += nb_clauses;
  return nb_clauses;
}

/**
 * Print F_* between one atom in bvars_subform and one atom in bvars_i.
 */
int
noll2sat_space_sep (noll_sat_t * fsat, noll_uint_array * bvars_subform,
                    noll_uint_array * bvars_i)
{

  assert (fsat != NULL);
  assert (bvars_subform != NULL);
  assert (bvars_i != NULL);

  int nb_clauses = 0;

  for (uint_t bi = 0; bi < noll_vector_size (bvars_i); bi++)
    {
      uint_t bvari = noll_vector_at (bvars_i, bi);
      noll_sat_space_t *atomi = noll2sat_get_sat_space (fsat, bvari);
      if (atomi == NULL)
        continue;
      for (uint_t sbj = 0; sbj < noll_vector_size (bvars_subform); sbj++)
        {
          uint_t bvarj = noll_vector_at (bvars_subform, sbj);
          noll_sat_space_t *atomj = noll2sat_get_sat_space (fsat, bvarj);
          if (atomi->forig->kind == NOLL_SPACE_PTO)
            {
              if (atomj->forig->kind == NOLL_SPACE_PTO)
                {
                  // F_*(pto bvari, pto bvarj) = ![src_i = src_j]
#ifndef NDEBUG
                  fprintf (stdout, "---- F_*(pto %d, pto %d)\n", bvari,
                           bvarj);
#endif
                  uint_t src_i = atomi->forig->m.pto.sid;
                  uint_t src_j = atomj->forig->m.pto.sid;
                  uint_t bvar_eq_i_j = noll2sat_get_bvar_eq (fsat, src_i,
                                                             src_j);
                  assert (bvar_eq_i_j != 0);
                  fprintf (fsat->file, "-%d 0\n", bvar_eq_i_j);
                  nb_clauses++;
                }
              else
                {
                  // atomj->forig->kind == NOLL_SPACE_LS
                  // F_*(pto(src_i,...) bvari, ls(in_j,out_j) bvarj)
                  // = [src_i = in_j] ==> [in_j = out_j]
#ifndef NDEBUG
                  fprintf (stdout, "---- F_*(pto %d, ls %d)\n", bvari, bvarj);
#endif
                  uint_t src_i = atomi->forig->m.pto.sid;
                  uint_t in_j = noll_vector_at (atomj->forig->m.ls.args, 0);
                  uint_t out_j =
                    (noll_pred_isUnaryLoc (atomj->forig->m.ls.pid)) ? 0 :
                    noll_vector_at (atomj->forig->m.ls.args, 1);
                  uint_t bvar_eq_i_j = noll2sat_get_bvar_eq (fsat, src_i,
                                                             in_j);
                  uint_t bvar_eq_j_j = noll2sat_get_bvar_eq (fsat, in_j,
                                                             out_j);
                  fprintf (fsat->file, "-%d %d 0\n", bvar_eq_i_j,
                           bvar_eq_j_j);
                  nb_clauses++;

                  if (noll_pred_is_one_dir (atomj->forig->m.ls.pid) == false)
                    {
                      // Warning: this works only for DLL
                      // F_*(pto(src_i,dst_i) bvari, dll(in_j,out_j) bvarj)
                      // = [src_i = out_j] ==> ![dll(in_j,out_j)]
#ifndef NDEBUG
                      fprintf (stdout, "---- F_*(pto %d, ls %d)\n", bvari,
                               bvarj);
#endif
                      bvar_eq_i_j = noll2sat_get_bvar_eq (fsat, src_i, out_j);
                      fprintf (fsat->file, "-%d -%d 0\n", bvar_eq_i_j, bvarj);
                      nb_clauses++;
                    }
                }
            }
          else
            {
              // atomi->forig->kind == NOLL_SPACE_LS
              if (atomj->forig->kind == NOLL_SPACE_PTO)
                {
                  // F_*(ls(in_i,out_i) bvari, pto(src_j,...) bvarj)
                  // = [src_j = in_i] ==> [in_i = out_i]
#ifndef NDEBUG
                  fprintf (stdout, "---- F_*(ls %d (P%d), pto %d)\n",
                           bvari, atomi->forig->m.ls.pid, bvarj);
#endif
                  uint_t src_j = atomj->forig->m.pto.sid;
                  uint_t in_i = noll_vector_at (atomi->forig->m.ls.args, 0);
                  uint_t out_i =
                    (noll_pred_isUnaryLoc (atomi->forig->m.ls.pid)) ? 0 :
                    noll_vector_at (atomi->forig->m.ls.args, 1);
                  uint_t bvar_eq_i_j = noll2sat_get_bvar_eq (fsat, src_j,
                                                             in_i);
                  uint_t bvar_eq_i_i = noll2sat_get_bvar_eq (fsat, in_i,
                                                             out_i);
                  fprintf (fsat->file, "-%d %d 0\n", bvar_eq_i_j,
                           bvar_eq_i_i);
                  nb_clauses++;

                  if (noll_pred_is_one_dir (atomi->forig->m.ls.pid) == false)
                    {
                      // Warning: this works only for DLL
                      // F_*(dll(in_i,out_i) bvari, pto(src_j,dst_j) bvarj)
                      // = [src_j = out_i] ==> ![dll(in_i,out_i)]
#ifndef NDEBUG
                      fprintf (stdout, "---- F_*(dls %d (P%d), pto %d)\n",
                               bvari, atomi->forig->m.ls.pid, bvarj);
#endif
                      bvar_eq_i_j = noll2sat_get_bvar_eq (fsat, src_j, out_i);
                      fprintf (fsat->file, "-%d -%d 0\n", bvar_eq_i_j, bvari);
                      nb_clauses++;
                    }
                }
              else
                {
                  // atomj->forig->kind == NOLL_SPACE_LS
                  // F_*(ls(in_i,out_i) bvari, ls(in_j,out_j) bvarj)
#ifndef NDEBUG
                  fprintf (stdout, "---- F_*(ls %d, ls %d)\n", bvari, bvarj);
#endif

                  // = for all used locations x, [x in sid_i] ==> ![x in sid_j]  and
                  // for two strongly separated predicates there is
                  // no location which belongs to both of them
                  // (could be improved by checking the type of the locvar
                  // vs the type of the set of loc variable)
                  uint_t sid_i = atomi->forig->m.ls.sid;
                  uint_t sid_j = atomj->forig->m.ls.sid;
                  for (uint_t xk = 1;   // ignore 'nil'
                       xk < noll_vector_size (fsat->form->lvars); xk++)
                    {
                      uint_t rk = noll_var_record (fsat->form->lvars, xk);
                      if (rk == UNDEFINED_ID)
                        continue;       // only location vars
                      if (fsat->finfo->used_lvar[xk] == true)
                        {
                          uint_t bvar_k_in_i = noll2sat_get_bvar_in (fsat, xk,
                                                                     sid_i);
                          assert (bvar_k_in_i != 0);
                          uint_t bvar_k_in_j = noll2sat_get_bvar_in (fsat, xk,
                                                                     sid_j);
                          assert (bvar_k_in_j != 0);
                          fprintf (fsat->file, "-%d -%d 0\n", bvar_k_in_i,
                                   bvar_k_in_j);
                          fprintf (fsat->file, "-%d -%d 0\n", bvar_k_in_j,
                                   bvar_k_in_i);
                          nb_clauses += 2;
                        }
                    }

                  // = [in_i = in_j] ==> [in_i = out_i] \/ [in_j = out_j]
                  uint_t in_i = noll_vector_at (atomi->forig->m.ls.args, 0);
                  uint_t out_i =
                    (noll_pred_isUnaryLoc (atomi->forig->m.ls.pid)) ? 0 :
                    noll_vector_at (atomi->forig->m.ls.args, 1);
                  uint_t in_j = noll_vector_at (atomj->forig->m.ls.args, 0);
                  uint_t out_j =
                    (noll_pred_isUnaryLoc (atomj->forig->m.ls.pid)) ? 0 :
                    noll_vector_at (atomj->forig->m.ls.args, 1);
                  uint_t bvar_eq_i_j =
                    noll2sat_get_bvar_eq (fsat, in_i, in_j);
                  uint_t bvar_eq_i_i = noll2sat_get_bvar_eq (fsat, in_i,
                                                             out_i);
                  uint_t bvar_eq_j_j = noll2sat_get_bvar_eq (fsat, in_j,
                                                             out_j);
                  fprintf (fsat->file, "-%d %d %d 0\n", bvar_eq_i_j,
                           bvar_eq_i_i, bvar_eq_j_j);
                  nb_clauses++;
                }
            }
        }
    }
  return nb_clauses;
}

/**
 * Store also the encoding of atoms seen during the printing,
 * in order to generate F_*
 */
int
noll2sat_space_aux (noll_sat_t * fsat, noll_space_t * subform,
                    noll_uint_array * bvars_used)
{

  assert (fsat != NULL);
  assert (fsat->form != NULL);
  assert (fsat->file != NULL);

  if (subform == NULL)
    {
#ifndef NDEBUG
      fprintf (stdout, "==== NULL space formula!\n");
#endif
      return 0;
    }

  int nb_clauses = 0;

  switch (subform->kind)
    {
    case NOLL_SPACE_PTO:
      {
        uint_t vsrc = subform->m.pto.sid;
        noll_uid_array *flds = subform->m.pto.fields;
        noll_uid_array *dests = subform->m.pto.dest;
        for (uint_t i = 0; i < noll_vector_size (flds); i++)
          {
            uint_t fi = noll_vector_at (flds, i);
            uint_t vdsti = noll_vector_at (dests, i);
            uint_t ri = noll_var_record (fsat->form->lvars, vdsti);
            if (ri == UNDEFINED_ID)
              continue;         // only location vars 
            uint_t bvar_pto = noll2sat_get_bvar_pto (fsat, subform, i);
#ifndef NDEBUG
            fprintf (stdout,
                     "----- pto abstraction for [x%d,f%d,y%d] (bvar %d) from ",
                     vsrc, fi, vdsti, bvar_pto);
            noll_space_fprint (stdout, fsat->form->lvars, fsat->form->svars,
                               subform);
            fprintf (stdout, "\n");
            fflush (stdout);
#endif
            if (bvar_pto == 0)
              {
                assert (0);
                // internal error
              }
            // print points to
            fprintf (fsat->file, "%d 0\n", bvar_pto);
            nb_clauses++;
            // Warning: only for NOLL
#ifdef NOLL_SAT
            // points to implies that source and destination are different
            //uint_t eq_src_dst = noll2sat_get_bvar_eq (fsat, vsrc, vdsti);
            //fprintf (fsat->file, "-%d 0\n", eq_src_dst);
            //nb_clauses++;
#endif
            // push atom in the list
            noll_uint_array_push (bvars_used, bvar_pto);
          }
        break;
      }
    case NOLL_SPACE_LS:
      {
        uint_t pid = subform->m.ls.pid;
        uint_t sid = subform->m.ls.sid;
        uint_t vin = noll_vector_at (subform->m.ls.args, 0);
        // TODO: refine the computation below depending on the base case
        uint_t vout = (noll_pred_isUnaryLoc (pid) == true) ?
          // get the index of 'nil' in formula 
          0 : noll_vector_at (subform->m.ls.args, 1);
        uint_t bvar_ls =
          noll2sat_get_bvar_pred (fsat, subform, vin, pid, sid);
#ifndef NDEBUG
        fprintf (stdout,
                 "----- ls abstraction for [P%d,alpha%d,x%d,x%d,...] (bvar %d) from ",
                 pid, sid, vin, vout, bvar_ls);
        noll_space_fprint (stdout, fsat->form->lvars, fsat->form->svars,
                           subform);
        fprintf (stdout, "\n");
        fflush (stdout);
#endif
        if (bvar_ls == 0)
          {
            assert (0);
            // internal error
          }

        if (noll_pred_is_one_dir (pid))
          {
            uint_t bvar_eq_in_out = noll2sat_get_bvar_eq (fsat, vin, vout);

            fprintf (fsat->file, "%d %d 0\n", bvar_ls, bvar_eq_in_out);
            fprintf (fsat->file, "-%d -%d 0\n", bvar_ls, bvar_eq_in_out);
            nb_clauses += 2;
          }
        else
          {
            // Warning: works mainly for DLL
            uint_t vpv = noll_vector_at (subform->m.ls.args, 2);
            uint_t vfw = noll_vector_at (subform->m.ls.args, 3);

            uint_t bvar_eq_in_fw = noll2sat_get_bvar_eq (fsat, vin, vfw);
            uint_t bvar_eq_out_pv = noll2sat_get_bvar_eq (fsat, vout, vpv);

            fprintf (fsat->file, "%d %d 0\n", bvar_ls, bvar_eq_in_fw);
            fprintf (fsat->file, "%d %d 0\n", bvar_ls, bvar_eq_out_pv);
            fprintf (fsat->file, "-%d -%d 0\n", bvar_ls, bvar_eq_in_fw);
            fprintf (fsat->file, "-%d -%d 0\n", bvar_ls, bvar_eq_out_pv);
            nb_clauses += 4;
          }
        // push atom in the list
        noll_uint_array_push (bvars_used, bvar_ls);
        break;
      }
    case NOLL_SPACE_WSEP:
      {
        // translate subformula and collect their used bvars
        for (uint_t i = 0; i < noll_vector_size (subform->m.sep); i++)
          {
            nb_clauses += noll2sat_space_aux (fsat,
                                              noll_vector_at (subform->m.sep,
                                                              i), bvars_used);
          }
        break;
      }

    case NOLL_SPACE_SSEP:
      {
        // translate subformula and collect their used bvars
        noll_uint_array *bvars_subform = noll_uint_array_new ();        // acc for atoms
        for (uint_t i = 0; i < noll_vector_size (subform->m.sep); i++)
          {
            noll_uint_array *bvars_i = noll_uint_array_new ();
            // translate formula
            nb_clauses += noll2sat_space_aux (fsat,
                                              noll_vector_at (subform->m.sep,
                                                              i), bvars_i);
#ifndef NDEBUG
            fprintf (stdout, "\n----- F_* abstraction \n");
            fflush (stdout);
#endif
            // put F_* corresponding to
            // the bvars_subform (collected until i) and bvars_used_i atoms
            nb_clauses += noll2sat_space_sep (fsat, bvars_subform, bvars_i);

            // push bvars_i in bvars_subform and bvars_used
            for (uint_t bi = 0; bi < noll_vector_size (bvars_i); bi++)
              {
                noll_uint_array_push (bvars_subform,
                                      noll_vector_at (bvars_i, bi));
                noll_uint_array_push (bvars_used,
                                      noll_vector_at (bvars_i, bi));
              }
            // clean bvars_i
            noll_uint_array_clear (bvars_i);
          }
        noll_uint_array_clear (bvars_subform);
        break;
      }
    default:
      break;
    }
  return nb_clauses;
}

/**
 * Writes the boolean abstraction of the space constraints: F(Sigma)
 */
int
noll2sat_space (noll_sat_t * fsat)
{

  assert (fsat != NULL);
  assert (fsat->form != NULL);
  assert (fsat->file != NULL);

  // call function above with the empty array
  noll_uint_array *atoms = noll_uint_array_new ();
  int nb_clauses = noll2sat_space_aux (fsat, fsat->form->space, atoms);
  noll_uint_array_delete (atoms);

  fsat->no_clauses += nb_clauses;
  return nb_clauses;
}

/**
 * Writes the boolean abstraction of the membership constraints: F_\in
 */
int
noll2sat_membership (noll_sat_t * fsat)
{

  assert (fsat != NULL);
  assert (fsat->form != NULL);
  assert (fsat->file != NULL);

  int nb_clauses = 0;

  /* variables [x in alpha] such that
   * the type of x is not included in the type of alpha are false
   */
  for (uint_t xi = 1; xi < noll_vector_size (fsat->form->lvars); xi++)
    {
      if (fsat->finfo->used_lvar[xi] == true)
        {
          noll_type_t *typ_xi = noll_var_type (fsat->form->lvars, xi);
          assert (typ_xi != NULL);
          if (typ_xi->kind != NOLL_TYP_RECORD)
            continue;
          uid_t rec_xi = noll_var_record (fsat->form->lvars, xi);
          for (uint_t alphaj = 0;
               alphaj < noll_vector_size (fsat->form->svars); alphaj++)
            {
              if (fsat->finfo->used_svar[alphaj] == true)
                {
                  noll_var_t *alpha =
                    noll_vector_at (fsat->form->svars, alphaj);
                  noll_type_t *types_alpha = alpha->vty;
                  if (((noll_vector_size (types_alpha->args) > 0)
                       && (rec_xi != noll_vector_at (types_alpha->args, 0)))
                      || (type_in_pred_of_svar (fsat, rec_xi, alphaj) == 0))
                    {
#ifndef NDEBUG
                      fprintf (stdout, "---- var x%d is not in %s\n", xi,
                               alpha->vname);
#endif
                      uint_t bvar_i_in_j = noll2sat_get_bvar_in (fsat, xi,
                                                                 alphaj);
                      assert (bvar_i_in_j != 0);
                      fprintf (fsat->file, "-%d 0\n", bvar_i_in_j);
                      nb_clauses++;
                    }
                }
            }
        }
    }

  /*
   * x in alpha implies P_alpha(...), for any x != nil and alpha
   */
  for (uint_t lsi = 0; lsi < noll_vector_size (fsat->var_pred); lsi++)
    {
      uint_t alpha_i =
        (noll_vector_at (fsat->var_pred, lsi))->forig->m.ls.sid;
      uint_t p_i = (noll_vector_at (fsat->var_pred, lsi))->forig->m.ls.pid;
      if (alpha_i == UNDEFINED_ID)
        // no svar bound to this predicate
        continue;
      // alpha_i is used
      // get all vars except nil
      for (uint_t xj = 1; xj < noll_vector_size (fsat->form->lvars); xj++)
        {
          if (fsat->finfo->used_lvar[xj] == true)
            {
              noll_type_t *typ_xj = noll_var_type (fsat->form->lvars, xj);
              assert (typ_xj != NULL);
              if (typ_xj->kind != NOLL_TYP_RECORD)
                continue;
              // if (type_in_pred_of_svar(fsat, typ_xj, alpha_i))  { // TODO: check that not needed!
              uint_t bvar_j_in_i = noll2sat_get_bvar_in (fsat, xj, alpha_i);
              assert (bvar_j_in_i != 0);
#ifndef NDEBUG
              fprintf (stdout,
                       "---- var %s in %s (bvar %d) implies %s (bvar %d)\n",
                       noll_var_name (fsat->form->lvars, xj, NOLL_TYP_RECORD),
                       noll_var_name (fsat->form->svars, alpha_i,
                                      NOLL_TYP_SETLOC), bvar_j_in_i,
                       noll_pred_name (p_i), fsat->start_pred + lsi);
#endif
              fprintf (fsat->file, "-%d %d 0\n", bvar_j_in_i,
                       fsat->start_pred + (uint_t) lsi);
              nb_clauses++;
              // }
            }
        }
    }

  /*
   * closure of membership w.r.t. equality (the types of the variables are checked)
   * [xi in alpha_i] /\ [xi = xj] ==> [xj in alpha_i]
   */
  for (uint_t i = 0; i < noll_vector_size (fsat->var_inset); i++)
    {
      uint_t bvar_in_i = fsat->start_inset + i;
      uint_t x_i = noll_vector_at (fsat->var_inset, i)->x;
      noll_type_t *typ_xi = noll_var_type (fsat->form->lvars, x_i);
      assert (typ_xi != NULL);
      if ((x_i == 0) || typ_xi->kind != NOLL_TYP_RECORD)
        continue;
      uid_t rec_i = noll_var_record (fsat->form->lvars, x_i);
      uint_t alpha_i = noll_vector_at (fsat->var_inset, i)->alpha;
      noll_type_t *types_alpha_i =
        noll_vector_at (fsat->form->svars, alpha_i)->vty;
      for (uint_t x_j = 1; x_j < noll_vector_size (fsat->form->lvars); x_j++)
        {
          if (x_j != x_i && fsat->finfo->used_lvar[x_j] == true)
            {
              noll_type_t *typ_xj = noll_var_type (fsat->form->lvars, x_j);
              assert (typ_xj != NULL);
              if (typ_xj->kind != NOLL_TYP_RECORD)
                continue;
              uid_t rec_j = noll_var_record (fsat->form->lvars, x_j);

              uint_t bvar_eq_i_j = noll2sat_get_bvar_eq (fsat, x_i, x_j);
              uint_t bvar_in_j_i = noll2sat_get_bvar_in (fsat, x_j, alpha_i);

              if (((noll_vector_size (types_alpha_i->args) > 0)
                   && (rec_i == rec_j)
                   && (rec_i == noll_vector_at (types_alpha_i->args, 0)))
                  || ((rec_i == rec_j)
                      && type_in_pred_of_svar (fsat, rec_i, alpha_i)))
                {
#ifndef NDEBUG
                  fprintf (stdout, "---- var %s, %s, %s\n",
                           noll_var_name (fsat->form->lvars, x_i,
                                          NOLL_TYP_RECORD),
                           noll_var_name (fsat->form->lvars, x_j,
                                          NOLL_TYP_RECORD),
                           noll_var_name (fsat->form->svars, alpha_i,
                                          NOLL_TYP_SETLOC));
#endif
                  fprintf (fsat->file, "-%d -%d %d 0\n", bvar_eq_i_j,
                           bvar_in_i, bvar_in_j_i);
                  nb_clauses++;
                }
            }
        }
    }

  /*
   * a predicate implies that the source belongs to
   * the set of locations variable associated to the predicate:
   * [P_alpha(x,...)] ==> [x in alpha]
   */
  for (uint_t i = 0; i < noll_vector_size (fsat->var_pred); i++)
    {
      uint_t pid_i = noll_vector_at (fsat->var_pred, i)->forig->m.ls.pid;
      uint_t x_i = noll_vector_at (noll_vector_at (fsat->var_pred,
                                                   i)->forig->m.ls.args, 0);
      if (x_i == 0) /* nil */ continue;
      uint_t alpha_i = noll_vector_at (fsat->var_pred, i)->forig->m.ls.sid;
#ifndef NDEBUG
      fprintf (stdout, "---- predicate %s implies %s in %s\n",
               noll_pred_getpred (pid_i)->pname,
               noll_vector_at (fsat->form->lvars, x_i)->vname,
               noll_vector_at (fsat->form->svars, alpha_i)->vname);
#endif
      uint_t bvar_pred_i = fsat->start_pred + i;
      uint_t bvar_in_i = noll2sat_get_bvar_in (fsat, x_i, alpha_i);
      fprintf (fsat->file, "-%d %d 0\n", bvar_pred_i, bvar_in_i);
      nb_clauses++;
    }

  /*
   * membership implies a disjunction of points-to with no destination
   * for alpha bound to some predicate and any x
   * [x in alpha] ==> \/ [x,f,alpha]
   */
  for (uint_t i = 0; i < noll_vector_size (fsat->var_pred); i++)
    {
      noll_sat_space_t *ls_i = noll_vector_at (fsat->var_pred, i);
      uint_t pid_i = ls_i->forig->m.ls.pid;
      uint_t alpha_i = ls_i->forig->m.ls.sid;
      if (alpha_i == UNDEFINED_ID)
        continue;               // no svar bound
      noll_type_t *types_alpha_i =
        noll_vector_at (fsat->form->svars, alpha_i)->vty;

      // try all location variables x except 'nil'
      for (uint_t x_j = 1; x_j < noll_vector_size (fsat->form->lvars); x_j++)
        if (fsat->finfo->used_lvar[x_j])
          {
            uint_t typ_j = noll_var_record (fsat->form->lvars, x_j);
            uint_t bvar_j_in_i = noll2sat_get_bvar_in (fsat, x_j, alpha_i);

            if (((noll_vector_size (types_alpha_i->args) > 0)
                 && (typ_j != noll_vector_at (types_alpha_i->args, 0)))
                || (type_in_pred_of_svar (fsat, typ_j, alpha_i) == 0))
              // [x in alpha] is false because of typing
              continue;         // go to a new variable

            // look at the fields of the predicate
            const noll_pred_t *pred = noll_pred_getpred (pid_i);
            assert (NULL != pred);
            int flag = 0;       //used to print just once the index of the membership predicate
            // and the 0 at the end of the clause
            /* MS: change of infos on fields */
            for (uint_t f_k = 0; f_k < noll_vector_size (fields_array); f_k++)
              {
                if (noll_pred_is_field (pid_i, f_k, NOLL_PFLD_NESTED))
                  {
                    /* if the field is defined in pid_i, get the source of f_k */
                    uint_t typ_src_fk =
                      noll_vector_at (fields_array, f_k)->src_r;
                    if (typ_j == typ_src_fk)
                      {
                        uint_t bvar_apto_j_k = noll2sat_get_bvar_apto (fsat,
                                                                       x_j,
                                                                       f_k,
                                                                       ls_i->
                                                                       forig);
                        if (!flag)
                          {
                            fprintf (fsat->file, "-%d ", bvar_j_in_i);
#ifndef NDEBUG
                            fprintf (stdout, "%s in %s implies ",
                                     noll_vector_at (fsat->form->lvars,
                                                     x_j)->vname,
                                     noll_vector_at (fsat->form->svars,
                                                     alpha_i)->vname);
#endif
                            flag = 1;
                          }
                        fprintf (fsat->file, "%d ", bvar_apto_j_k);
#ifndef NDEBUG
                        fprintf (stdout, "%s src_of %s in %s or ",
                                 noll_vector_at (fsat->form->lvars,
                                                 x_j)->vname,
                                 noll_vector_at (fields_array, f_k)->name,
                                 noll_vector_at (fsat->form->svars,
                                                 alpha_i)->vname);
#endif
                      }
                  }
              }
            if (flag)
              {
                fprintf (fsat->file, "0\n");
#ifndef NDEBUG
                fprintf (stdout, "\n");
#endif
                nb_clauses++;
              }
          }
    }
  fsat->no_clauses += nb_clauses;
  return nb_clauses;
}

/*
 * write F_det ([x_i,f,y_i], [x_j,f,y_j]) = [x_i = x_j] ==> [x_i,f,y_i] xor [x_j,f,y_j]
 * or [x_i,f,y_i] and [x_j,f,y_j] => ![x_i = x_j]  (for syntactic x_i != xj)
 */
int
noll2sat_det_pto_pto (noll_sat_t * fsat)
{
  int nb_clauses = 0;

  for (uint_t i = 0; i < fsat->size_pto; i++)
    for (uint_t j = i + 1; j < fsat->size_pto; j++)
      {
        noll_sat_space_t *sat_i = noll_vector_at (fsat->var_pto, i);
        noll_sat_space_t *sat_j = noll_vector_at (fsat->var_pto, j);
        uint_t x_i = sat_i->forig->m.pto.sid;
        uint_t x_j = sat_j->forig->m.pto.sid;
        uint_t f_i =
          noll_vector_at (sat_i->forig->m.pto.fields, sat_i->m.idx);
        uint_t f_j =
          noll_vector_at (sat_j->forig->m.pto.fields, sat_j->m.idx);
        if (f_i == f_j)
          {
#ifndef NDEBUG
            fprintf (stdout,
                     "---- [%s = %s] ==> [1->%s,%s] xor [2->field,%s]\n",
                     noll_vector_at (fsat->form->lvars, x_i)->vname,
                     noll_vector_at (fsat->form->lvars, x_j)->vname,
                     noll_vector_at (fields_array, f_i)->name,
                     noll_vector_at (fsat->form->lvars,
                                     noll_vector_at (sat_i->forig->m.pto.dest,
                                                     sat_i->m.idx))->vname,
                     noll_vector_at (fsat->form->lvars,
                                     noll_vector_at (sat_j->forig->m.pto.dest,
                                                     sat_j->m.idx))->vname);
#endif
            uint_t bvar_eq_i_j = noll2sat_get_bvar_eq (fsat, x_i, x_j);
            fprintf (fsat->file, "-%d %d %d 0\n", bvar_eq_i_j,
                     fsat->start_pto + i, fsat->start_pto + j);
            fprintf (fsat->file, "-%d -%d -%d 0\n", bvar_eq_i_j,
                     fsat->start_pto + i, fsat->start_pto + j);
            nb_clauses += 2;
          }
      }

  return nb_clauses;
}

/*
 * write F_det ([x_i,f,_], [x_j,f,_]) = [x_i = x_j] ==> ![x_i,f,_] or ![x_j,f,_]
 * or [x_i,f,_] and [x_j,f,_] ==> ![x_i = x_j] (for syntactic x_i != x_j)
 */
int
noll2sat_det_apto_apto (noll_sat_t * fsat)
{
  int nb_clauses = 0;

  for (uint_t i = 0; i < fsat->size_apto; i++)
    for (uint_t j = i + 1; j < fsat->size_apto; j++)
      {
        noll_sat_space_t *sat_i = noll_vector_at (fsat->var_apto, i);
        noll_sat_space_t *sat_j = noll_vector_at (fsat->var_apto, j);
        uint_t x_i = sat_i->m.p.var;
        uint_t x_j = sat_j->m.p.var;
        uint_t f_i = sat_i->m.p.fld;
        uint_t f_j = sat_j->m.p.fld;
        if ((f_i == f_j) && (sat_i->forig != sat_j->forig) && (x_i != x_j))
          {
#ifndef NDEBUG
            fprintf (stdout,
                     "---- [%s = %s] ==> ![%s->%s,_] or ![%s->%s,_]\n",
                     noll_vector_at (fsat->form->lvars, x_i)->vname,
                     noll_vector_at (fsat->form->lvars, x_j)->vname,
                     noll_vector_at (fsat->form->lvars, x_i)->vname,
                     noll_vector_at (fields_array, f_i)->name,
                     noll_vector_at (fsat->form->lvars, x_j)->vname,
                     noll_vector_at (fields_array, f_i)->name);
#endif
            uint_t bvar_eq_i_j = noll2sat_get_bvar_eq (fsat, x_i, x_j);
            fprintf (fsat->file, "-%d -%d -%d 0\n", bvar_eq_i_j,
                     fsat->start_apto + i, fsat->start_apto + j);
            nb_clauses++;
          }
      }
  return nb_clauses;
}

/*
 * write F_det ([x_i,f,_], nil) = [x_i = nil] ==> ![x_i,f,_]
 */
int
noll2sat_det_apto_nil (noll_sat_t * fsat)
{
  int nb_clauses = 0;

  for (uint_t i = 0; i < fsat->size_apto; i++)
    {
      noll_sat_space_t *sat_i = noll_vector_at (fsat->var_apto, i);
      uint_t x_i = sat_i->m.p.var;
      uint_t f_i = sat_i->m.p.fld;
      uint_t x_nil = 0;
#ifndef NDEBUG
      fprintf (stdout,
               "---- [%s = %s] ==> ![%s->%s,_]\n",
               noll_vector_at (fsat->form->lvars, x_i)->vname,
               noll_vector_at (fsat->form->lvars, x_nil)->vname,
               noll_vector_at (fsat->form->lvars, x_i)->vname,
               noll_vector_at (fields_array, f_i)->name);
#endif
      uint_t bvar_eq_i_j = noll2sat_get_bvar_eq (fsat, x_i, x_nil);
      fprintf (fsat->file, "-%d -%d 0\n", bvar_eq_i_j, fsat->start_apto + i);
      nb_clauses++;
    }
  return nb_clauses;
}

/*
 * write F_det ([x_i,f,y_i], [x_j,f,alpha]) = [x_i = x_j] & [x_i,f,y_i] ==> ![x_j,f,alpha]
 * or [x_i,f,y_i] & [x_j,f,alpha] => ![x_i = x_j] 
 */
int
noll2sat_det_pto_apto (noll_sat_t * fsat)
{
  int nb_clauses = 0;

  for (uint_t i = 0; i < fsat->size_pto; i++)
    for (uint_t j = 0; j < fsat->size_apto; j++)
      {
        noll_sat_space_t *sat_i = noll_vector_at (fsat->var_pto, i);
        noll_sat_space_t *sat_j = noll_vector_at (fsat->var_apto, j);
        uint_t x_i = sat_i->forig->m.pto.sid;
        uint_t f_i =
          noll_vector_at (sat_i->forig->m.pto.fields, sat_i->m.idx);
        uint_t x_j = sat_j->m.p.var;
        uint_t f_j = sat_j->m.p.fld;
        if (f_i == f_j)
          {
#ifndef NDEBUG
            fprintf (stdout,
                     "---- [%s = %s] & [%s,%s,%s] ==> ![%s,%s,%s]\n",
                     noll_vector_at (fsat->form->lvars, x_i)->vname,
                     noll_vector_at (fsat->form->lvars, x_j)->vname,
                     noll_vector_at (fsat->form->lvars, x_i)->vname,
                     noll_vector_at (fields_array, f_i)->name,
                     noll_vector_at (fsat->form->lvars,
                                     noll_vector_at (sat_i->forig->m.pto.dest,
                                                     sat_i->m.idx))->vname,
                     noll_vector_at (fsat->form->lvars, x_j)->vname,
                     noll_vector_at (fields_array, f_i)->name,
                     noll_var_name (fsat->form->svars, sat_j->forig->m.ls.sid,
                                    NOLL_TYP_SETLOC));
#endif
            uint_t bvar_eq_i_j = noll2sat_get_bvar_eq (fsat, x_i, x_j);
            fprintf (fsat->file, "-%d -%d -%d 0\n", bvar_eq_i_j,
                     fsat->start_pto + i, fsat->start_apto + j);
            nb_clauses++;
          }
      }

  return nb_clauses;
}

/*
 * write F_det ([x_i,f,y_i]) = [x_i,f,y_i] ==> ![x_j = nil]
 */
int
noll2sat_det_pto_nil (noll_sat_t * fsat)
{
  int nb_clauses = 0;

  for (uint_t i = 0; i < fsat->size_pto; i++)
    {
      noll_sat_space_t *sat_i = noll_vector_at (fsat->var_pto, i);
      uint_t x_i = sat_i->forig->m.pto.sid;
      uint_t f_i = noll_vector_at (sat_i->forig->m.pto.fields, sat_i->m.idx);
      uint_t x_nil = 0;
#ifndef NDEBUG
      fprintf (stdout,
               "---- [%s,%s,%s] ==> ![%s = %s] & \n",
               noll_vector_at (fsat->form->lvars, x_i)->vname,
               noll_vector_at (fields_array, f_i)->name,
               noll_vector_at (fsat->form->lvars,
                               noll_vector_at (sat_i->forig->m.pto.dest,
                                               sat_i->m.idx))->vname,
               noll_vector_at (fsat->form->lvars, x_i)->vname,
               noll_vector_at (fsat->form->lvars, x_nil)->vname);
#endif
      uint_t bvar_eq_i_j = noll2sat_get_bvar_eq (fsat, x_i, x_nil);
      fprintf (fsat->file, "-%d -%d 0\n", fsat->start_pto + i, bvar_eq_i_j);
      nb_clauses++;
    }
  return nb_clauses;
}

/*
 * write F_det ([x_i,f,y_i], [P,alpha(x_j,y_j,_)]) =
 *          for all f in Fields0(P) and x_k in phi
 *          (old) [x_i = x_k] & [x_k in alpha] ==> [x_i,f,y_i] xor [P,alpha(x_j,y_j,_)]
 *              [x_i = x_k] & [x_i,f,y_i] ==> ![x_k in alpha]
 */
int
noll2sat_det_pto_pred (noll_sat_t * fsat)
{
  int nb_clauses = 0;

  for (uint_t i = 0; i < fsat->size_pto; i++)
    for (uint_t j = 0; j < fsat->size_pred; j++)
      {
        noll_sat_space_t *sat_i = noll_vector_at (fsat->var_pto, i);
        noll_sat_space_t *sat_j = noll_vector_at (fsat->var_pred, j);
        uid_t x_i = sat_i->forig->m.pto.sid;
        uid_t f_i = noll_vector_at (sat_i->forig->m.pto.fields, sat_i->m.idx);
        uid_t pid_j = sat_j->forig->m.ls.pid;
        uid_t alpha_j = sat_j->forig->m.ls.sid;
        const noll_pred_t *pred_j = noll_pred_getpred (pid_j);
        assert (NULL != pred_j);
        /* test if f_i is in fieldsof level 0 for pred_j */
        /* MS: change of info on fields */
        if (!noll_pred_is_field (pid_j, f_i, NOLL_PFLD_BORDER))
          continue;

        // f_i is in fields0, write constraint for any x
        // with the same type as x_i (to optimize the number of constraints)
        for (uint_t x_k = 0; x_k < noll_vector_size (fsat->form->lvars);
             x_k++)
          if (fsat->finfo->used_lvar[x_k] == true)
            {
              uid_t typ_x_i = noll_var_record (fsat->form->lvars, x_i);
              uid_t typ_x_k = noll_var_record (fsat->form->lvars, x_k);
              if (typ_x_i == typ_x_k)
                {
#ifndef NDEBUG
                  fprintf (stdout,
                           "---- var: %s, field: %s, Predicate: %s, SVar: %s\n",
                           noll_vector_at (fsat->form->lvars, x_i)->vname,
                           noll_vector_at (fields_array, f_i)->name,
                           pred_j->pname, noll_vector_at (fsat->form->svars,
                                                          alpha_j)->vname);
#endif
                  uid_t bvar_eq_i_k = noll2sat_get_bvar_eq (fsat, x_i,
                                                            x_k);
                  uid_t bvar_in_k_j = noll2sat_get_bvar_in (fsat, x_k,
                                                            alpha_j);
                  fprintf (fsat->file, "-%d -%d %d -%d 0\n", bvar_eq_i_k,
                           bvar_in_k_j, fsat->start_pto + i,
                           fsat->start_pred + j); 
		  fprintf (fsat->file, "-%d -%d -%d %d 0\n", bvar_eq_i_k,
                           bvar_in_k_j, fsat->start_pto + i,
                           fsat->start_pred + j);
                  nb_clauses += 2;
                }
            }
      }
  return nb_clauses;
}

/*
 * write F_det ([P,alpha(x_i,_)], [Q,beta(x_j,_)]) =
 *          if Fields0(P) /\ Fields0(Q) != 0 then
 *            for all x1, x2 in usedvar(phi) s.t. type(x1)=type(x2)=type0(P)
 *            (old)  [x1 = x2] & [x1 in alpha] & [x2 in beta] ==>
 *                      [P,alpha(x_i,_)] xor [Q,beta(x_j,_)]
 *              [x1 = x2] & [x1 in alpha] => ![x2 in beta] 
 *              [x1 = x2] & [x1 in beta]  => ![x2 in alpha] 
 */
int
noll2sat_det_pred_pred (noll_sat_t * fsat)
{
  int nb_clauses = 0;

  for (uint_t i = 0; i < fsat->size_pred; i++)
    for (uint_t j = i + 1; j < fsat->size_pred; j++)
      {
        noll_sat_space_t *sat_i = noll_vector_at (fsat->var_pred, i);
        noll_sat_space_t *sat_j = noll_vector_at (fsat->var_pred, j);
        uid_t pid_i = sat_i->forig->m.ls.pid;
        const noll_pred_t *pred_i = noll_pred_getpred (pid_i);
        assert (NULL != pred_i);
        uid_t typ0_i = pred_i->typ->ptype0;

        uid_t alpha_i = sat_i->forig->m.ls.sid;
        uid_t pid_j = sat_j->forig->m.ls.pid;
        uid_t alpha_j = sat_j->forig->m.ls.sid;
        const noll_pred_t *pred_j = noll_pred_getpred (pid_j);
        assert (NULL != pred_j);
        uid_t typ0_j = pred_i->typ->ptype0;

        // the predicates have the same type at level 0
        if (typ0_i != typ0_j)
          continue;

        // find if they have common fields at level 0
        /* MS: change of info on fields */
        int flag = 0;
        for (uint_t fi = 0;
             fi < noll_vector_size (fields_array) && (flag == 0); fi++)
          {
            if (noll_pred_is_field (pid_i, fi, NOLL_PFLD_BORDER) &&
                noll_pred_is_field (pid_j, fi, NOLL_PFLD_BORDER))
              flag = 1;
          }
        if (flag == 0)
          continue;

        // pred_i and pred_j have a common field
        // iterate over variables used in phi, ignore nil
        for (uint_t x1 = 1; x1 < noll_vector_size (fsat->form->lvars); x1++)
          if (fsat->finfo->used_lvar[x1] == true)
            {
              for (uint_t x2 = 1; x2 <= x1; x2++)
                if ((fsat->finfo->used_lvar[x2] == true)
                    && (noll_var_record (fsat->form->lvars, x1)
                        == noll_var_record (fsat->form->lvars,
                                            x2))
                    && (noll_var_record (fsat->form->lvars, x1) == typ0_i))
                  {
                    // both variables used and of the same type, typ0_i
#ifndef NDEBUG
                    fprintf (stdout,
                             "---- Pred1: %s, Pred2: %s, Var1: %s, Var2: %s\n",
                             pred_i->pname, pred_j->pname,
                             noll_vector_at (fsat->form->lvars, x1)->vname,
                             noll_vector_at (fsat->form->lvars, x2)->vname);
#endif
                    uint_t bvar_eq_1_2 = noll2sat_get_bvar_eq (fsat, x1,
                                                               x2);
                    assert (bvar_eq_1_2 != 0);
                    uint_t bvar_in_1_i = noll2sat_get_bvar_in (fsat, x1,
                                                               alpha_i);
                    assert (bvar_in_1_i != 0);
                    uint_t bvar_in_2_j = noll2sat_get_bvar_in (fsat, x2,
                                                               alpha_j);
                    assert (bvar_in_2_j != 0);
                    /* fprintf (fsat->file, "-%d -%d -%d -%d -%d 0\n",
                             bvar_in_1_i, bvar_in_2_j, bvar_eq_1_2,
                             fsat->start_pred + i, fsat->start_pred + j); */
                    fprintf (fsat->file, "-%d -%d -%d 0\n",
                             bvar_eq_1_2, bvar_in_1_i, bvar_in_2_j);
                    nb_clauses++;
                    fprintf (fsat->file, "-%d -%d -%d 0\n",
                             bvar_eq_1_2, bvar_in_2_j, bvar_in_1_i);
                    nb_clauses++;
                  }
            }
      }
  return nb_clauses;
}

int
noll2sat_det (noll_sat_t * fsat)
{

  assert (fsat != NULL);
  assert (fsat->form != NULL);
  assert (fsat->file != NULL);

  int nb_clauses = 0;

#ifndef NDEBUG
  fprintf (stdout,
           "*******************0th step of Det: (a)pto with nil (last %d)*******************\n",
           nb_clauses);
#endif
  nb_clauses += noll2sat_det_apto_nil (fsat);
  nb_clauses += noll2sat_det_pto_nil (fsat);

#ifndef NDEBUG
  fprintf (stdout,
           "*******************1st step of Det: pto with pto (last %d)*******************\n",
           nb_clauses);
#endif
  //pairs of points-to
  nb_clauses += noll2sat_det_pto_pto (fsat);

#ifndef NDEBUG
  fprintf (stdout,
           "*******************2nd step of Det: apto with apto (last %d)*******************\n",
           nb_clauses);
#endif
  //pairs of anonymous dest points-to
  nb_clauses += noll2sat_det_apto_apto (fsat);

#ifndef NDEBUG
  fprintf (stdout,
           "*******************3rd step of Det: pto with apto (last %d)*******************\n",
           nb_clauses);
#endif
  //pairs of points-to and anonymous dest points-to
  nb_clauses += noll2sat_det_pto_apto (fsat);

#ifndef NDEBUG
  fprintf (stdout,
           "*******************4th step of Det: pto with pred (last %d)*******************\n",
           nb_clauses);
#endif
  //pairs of points-to and ls predicates
  nb_clauses += noll2sat_det_pto_pred (fsat);

#ifndef NDEBUG
  fprintf (stdout,
           "*******************5th step of Det: pred with pred (last %d)*******************\n",
           nb_clauses);
#endif
  //pairs of ls predicates
  nb_clauses += noll2sat_det_pred_pred (fsat);

  fsat->no_clauses += nb_clauses;
  return nb_clauses;
}

/**
 * write the boolean abstraction for the F(x in alpha) =
 *    - [x in alpha] ==> [P,alpha()] if type(x) in types(P)
 *    - [x in alpha] if alpha is not bound to a spatial constraint
 *    - false otherwise
 */
void
noll2sat_share_in (noll_sat_t * fsat, uid_t x, noll_sterm_array * t)
{

  uint_t ty_x = noll_var_record (fsat->form->lvars, x);

  for (uint_t tj = 0; tj < noll_vector_size (t); tj++)
    {
      noll_sterm_t *term = noll_vector_at (t, tj);
      if ((term->kind == NOLL_STERM_LVAR)
          && (ty_x == noll_var_record (fsat->form->lvars, term->lvar)))
        {
#ifndef NDEBUG
          fprintf (stdout, "%s = %s ",
                   noll_vector_at (fsat->form->lvars, x)->vname,
                   noll_vector_at (fsat->form->lvars, term->lvar)->vname);
#endif
          uint_t bvar_eq_x_tj = noll2sat_get_bvar_eq (fsat, x, term->lvar);
          assert (bvar_eq_x_tj != 0);
          fprintf (fsat->file, "%d ", bvar_eq_x_tj);
        }
      else if ((term->kind == NOLL_STERM_SVAR)
               && (type_in_pred_of_svar (fsat, ty_x, term->svar) == 1))
        {
#ifndef NDEBUG
          fprintf (stdout, "%s in %s ",
                   noll_vector_at (fsat->form->lvars, x)->vname,
                   noll_vector_at (fsat->form->svars, term->svar)->vname);
#endif
          uint_t bvar_in_x_tj = noll2sat_get_bvar_in (fsat, x, term->svar);
          assert (bvar_in_x_tj != 0);
          fprintf (fsat->file, "%d ", bvar_in_x_tj);
        }
      else if ((term->kind == NOLL_STERM_PRJ)
               && (type_in_pred_of_svar (fsat, ty_x, term->svar) == 1)
               && (ty_x == noll_var_record (fsat->form->lvars, term->lvar)))
        {
#ifndef NDEBUG
          fprintf (stdout, "%s in %s ",
                   noll_vector_at (fsat->form->lvars, x)->vname,
                   noll_vector_at (fsat->form->svars, term->svar)->vname);
#endif
          uint_t bvar_in_x_tj = noll2sat_get_bvar_in (fsat, x, term->svar);
          assert (bvar_in_x_tj != 0);
          fprintf (fsat->file, "%d ", bvar_in_x_tj);
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
#ifndef NDEBUG
  fprintf (stdout, "\n");
#endif
}

int
noll2sat_share (noll_sat_t * fsat)
{

  assert (fsat != NULL);
  assert (fsat->form != NULL);
  assert (fsat->file != NULL);

  int nb_clauses = 0;

  if (fsat->form->share == NULL)
    return 0;

  // translate each constraint
  for (uint_t sh_i = 0; sh_i < noll_vector_size (fsat->form->share); sh_i++)
    {
      //the case for a single inclusion
      noll_atom_share_t *atom = noll_vector_at (fsat->form->share, sh_i);
      switch (atom->kind)
        {
        case NOLL_SHARE_IN:
          {                     // x in t

            assert (atom->t_left->kind == NOLL_STERM_LVAR);
            noll2sat_share_in (fsat, atom->t_left->lvar, atom->t_right);
            // end clause
            fprintf (fsat->file, "0\n");
            nb_clauses++;
            break;
          }
        case NOLL_SHARE_NI:
          {                     // x not in t

            assert (atom->t_left->kind == NOLL_STERM_LVAR);
            uint_t x = atom->t_left->lvar;

            for (uint_t i = 0; i < noll_vector_size (atom->t_right); i++)
              {
                noll_sterm_t *ti = noll_vector_at (atom->t_right, i);
                if (ti->kind >= NOLL_STERM_SVAR)
                  {
                    // projection also dealt
#ifndef NDEBUG
                    fprintf (stdout, "++++++ %s not in %s\n ",
                             noll_vector_at (fsat->form->lvars, x)->vname,
                             noll_vector_at (fsat->form->svars,
                                             ti->svar)->vname);
#endif
                    uint_t bvar_in_x_ti = noll2sat_get_bvar_in (fsat, x,
                                                                ti->svar);
                    assert (bvar_in_x_ti != 0);
                    fprintf (fsat->file, "-%d 0\n", bvar_in_x_ti);
                    nb_clauses++;
                  }
                else
                  {
#ifndef NDEBUG
                    fprintf (stdout, "++++++ %s != %s\n ",
                             noll_vector_at (fsat->form->lvars, x)->vname,
                             noll_vector_at (fsat->form->lvars,
                                             ti->lvar)->vname);
#endif
                    uint_t bvar_eq_x_ti = noll2sat_get_bvar_eq (fsat, x,
                                                                ti->lvar);
                    assert (bvar_eq_x_ti != 0);
                    fprintf (fsat->file, "-%d 0\n", bvar_eq_x_ti);
                    nb_clauses++;
                  }
              }
            break;
          }
        default:
          {                     // alpha subsetof t
#ifndef NDEBUG
            fprintf (stdout, "noll2sat: share atom");
            noll_share_atom_fprint (stdout, fsat->form->lvars,
                                    fsat->form->svars, atom);
            fprintf (stdout, "\n");
#endif
            assert (atom->t_left->kind >= NOLL_STERM_SVAR);
            uint_t left_svar = atom->t_left->svar;
            uint_t ty_left =
              (atom->t_left->kind == NOLL_STERM_SVAR) ?
              UNDEFINED_ID : noll_var_record (fsat->form->lvars,
                                              atom->t_left->lvar);
            /*
             * for any variable vi, if vi in t_left then vi in one of the t_right
             * but only if vi is of type compatible with t_left and t_right
             */
            for (uint_t vi = 0; vi < noll_vector_size (fsat->form->lvars);
                 vi++)
              if (fsat->finfo->used_lvar[vi] == true)
                {
                  uint_t ty_vi = noll_var_record (fsat->form->lvars, vi);
                  if ((ty_left != UNDEFINED_ID) && (ty_left != ty_vi))
                    // ty_left is precise, but not equal to ty_vi
                    continue;
                  if ((ty_left == UNDEFINED_ID)
                      && (type_in_pred_of_svar (fsat, ty_vi, left_svar) == 0))
                    // ty_left is a set, but does not contain ty_vi
                    continue;
                  // here, vi and left_svar have compatible types
#ifndef NDEBUG
                  fprintf (stdout, "---- F (%s in %s) implies ",
                           noll_vector_at (fsat->form->lvars, vi)->vname,
                           noll_vector_at (fsat->form->svars,
                                           left_svar)->vname);
#endif
                  uint_t bvar_vi_in_t = noll2sat_get_bvar_in (fsat, vi,
                                                              left_svar);
                  assert (bvar_vi_in_t != 0);
                  // print \neg x \in \alpha_1
                  fprintf (fsat->file, "-%d ", bvar_vi_in_t);
                  // print disjunction of left terms for vi
                  noll2sat_share_in (fsat, vi, atom->t_right);
                  // end clause
                  fprintf (fsat->file, "0\n");
                  nb_clauses++;
                }

            /*
             * if t_left is associated to an ls predicate,
             * and t_left->lvar has the same type as the recursive type of the predicate
             * and if this predicate is not empty
             * then the source of this predicate belongs to one of the terms in t_right
             */
            uint_t lsi = 0;
            for (; lsi < noll_vector_size (fsat->var_pred); lsi++)
              {
                noll_sat_space_t *si = noll_vector_at (fsat->var_pred, lsi);
                if (si->forig->m.ls.sid == left_svar)
                  break;
              }
            if (lsi < noll_vector_size (fsat->var_pred))
              {
                noll_sat_space_t *si = noll_vector_at (fsat->var_pred, lsi);
                uid_t in_lsi = noll_vector_at (si->forig->m.ls.args, 0);
                // if t_left is a projection,
                // we generate the constraint only if the type of source
                // is the type of the projection
                if ((ty_left != UNDEFINED_ID)
                    && noll_var_record (fsat->form->lvars, in_lsi) != ty_left)
                  break;        // nothing to be done
                // else, generate the constraint
                // if [pi ...] true then
                fprintf (fsat->file, "-%d ", fsat->start_pred + lsi);
#ifndef NDEBUG
                fprintf (stdout, "---- F(pred-%d) implies ", lsi);
#endif
                // print disjunction for each term of t_right
                noll2sat_share_in (fsat, in_lsi, atom->t_right);
                // end clause
                fprintf (fsat->file, "0\n");
                nb_clauses++;
              }
            break;
          }
        }
    }

  fsat->no_clauses += nb_clauses;
  return nb_clauses;
}

/* ====================================================================== */
/* Calling Minisat and adding constraints */
/* ====================================================================== */

int
noll2sat_is_eq (noll_sat_t * fsat, uid_t x, uid_t y, noll_pure_op_t oper)
{

  int res = 0;

  size_t fname_len = strlen (fsat->fname);

  // print the prefix file with information about variables and clauses
  char *pre_fname = (char *) malloc ((5 + fname_len) * sizeof (char));
  memset (pre_fname, 0, (5 + fname_len) * sizeof (char));
  sprintf (pre_fname, "pre_%s", fsat->fname);
  FILE *out = fopen (pre_fname, "w");
  fprintf (out, "p cnf %d %d\n", fsat->no_vars - 1, fsat->no_clauses + 1);      // -1 on no_vars ?
#ifndef NDEBUG
  fprintf (stdout, "---- minisat query prefix: p cnf %d %d\n",
           fsat->no_vars - 1, fsat->no_clauses + 1);
#endif
  free (pre_fname);
  fclose (out);

  // print the suffix file with the equality to test
  char *eq_fname = (char *) malloc ((5 + fname_len) * sizeof (char));
  memset (eq_fname, 0, (5 + fname_len) * sizeof (char));
  sprintf (eq_fname, "eq_%s", fsat->fname);
  out = fopen (eq_fname, "w");
  free (eq_fname);

  //write a new clause in the DIMACS file
  uid_t bvar_eq_x_y = noll2sat_get_bvar_eq (fsat, x, y);
  if (oper == NOLL_PURE_EQ)
    {
      fprintf (out, "-%d 0\n", bvar_eq_x_y);
    }
  else if (oper == NOLL_PURE_NEQ)
    {
      fprintf (out, "%d 0\n", bvar_eq_x_y);
    }
  else
    {
      return -1;
    }
  fclose (out);

  // build the final file for sat using cat
  char *command = (char *) calloc ((100 + 4 * fname_len), sizeof (char));
  memset (command, 0, (100 + 4 * fname_len) * sizeof (char));
  sprintf (command,
           "cat pre_%s %s eq_%s 1> full_new_%s", fsat->fname, fsat->fname,
           fsat->fname, fsat->fname);
  if (system (command) != -1)
    assert (0);

  // print the minisat command
  memset (command, 0, (100 + 4 * fname_len) * sizeof (char));
  sprintf (command,
           "minisat_inc -verb=0 full_new_%s result.txt 1> msat_%s",
           fsat->fname, fsat->fname);
  if (system (command) != -1)
    {
      FILE *fres = fopen ("result.txt", "r");
      char s[10];
      fscanf (fres, "%s", s);
      fclose (fres);
      if (strcmp (s, "UNSAT") == 0)
        {
          res = 1;
        }
    }
  free (command);
  return res;
}

int
noll2sat_is_sat (noll_sat_t * fsat)
{

  int result = 1;

  size_t fname_len = strlen (fsat->fname);

  // print the prefix file for sat in file in the command
#ifndef NDEBUG
  fprintf (stdout, "---- minisat query prefix: p cnf %d %d\n",
           fsat->no_vars - 1, fsat->no_clauses);
#endif
  // build the final file for sat using echo and cat
  size_t command_len = 100 + 2 * fname_len;
  char *command = (char *) malloc (command_len * sizeof (char));
  memset (command, '\0', command_len * sizeof (char));
  sprintf (command,
           "echo \"p cnf %d %d\" | cat - %s 1> sat_%s", fsat->no_vars - 1,
           fsat->no_clauses, fsat->fname, fsat->fname);
  // execute cat
  if (system (command) != -1)
    {
      // print the minisat command
      memset (command, '\0', command_len * sizeof (char));
      sprintf (command,
               "minisat -verb=0 sat_%s drup_%s 1> result.txt", fsat->fname,
               fsat->fname);

      // call minisat
      if (system (command) != -1)
        {
          FILE *rfile = fopen ("result.txt", "r");
          char *line = NULL;
          size_t linelen = 0;
          /// read result of minisat with output for SAT-COMP
          while (getline (&line, &linelen, rfile) != -1)
            {
              if (line[0] != 's')
                continue;
#ifndef NDEBUG
              fprintf (stdout, "*********************%s**************\n",
                       line);
#endif
              if (strncmp (line, "s UNSAT", 7) == 0)
                {
#ifndef NDEBUG
                  fprintf (stdout,
                           "*******************UNSAT*******************\n");
#endif
                  result = 0;
                }
              break;
            }
          if (line != NULL)
            free (line);
        }
    }
  free (command);
  return result;
}

/**
 * Test if the boolean abstraction fsat implies [x in alpha]
 * with x and alpha valid location resp. set variables identifiers.
 * @return 0 is false, 1 if true, -1 if unknown
 */
int
noll2sat_is_in (noll_sat_t * fsat, uid_t x, uid_t alpha)
{

  assert (fsat != NULL);
  assert (fsat->form != NULL);
  assert (fsat->fname != NULL);
  assert (fsat->var_inset != NULL);
  assert (x < noll_vector_size (fsat->form->lvars));
  assert (alpha < noll_vector_size (fsat->form->svars));

  if (fsat->file != NULL)
    fclose (fsat->file);

  // Trivial cases:
  // - x or alpha not used in the formula ==> return -1
  if ((fsat->finfo->used_lvar[x] == false)
      || (fsat->finfo->used_svar[x] == false))
    return -1;

  // - x and alpha do not have compatible types ==> return 0
  uid_t typ_x = noll_var_record (fsat->form->lvars, x);
  if (type_in_pred_of_svar (fsat, typ_x, alpha) == 0)
    return 0;

  // Using sat case:
  // - find the boolean variable for this test
  uid_t bvar_x_in_alpha = noll2sat_get_bvar_in (fsat, x, alpha);
  assert (bvar_x_in_alpha != 0);

  // - write the query to sat
  size_t fname_len = strlen (fsat->fname);

  //     - print the prefix file with information about variables and clauses
  char *pre_fname = (char *) malloc ((5 + fname_len) * sizeof (char));
  memset (pre_fname, 0, (5 + fname_len) * sizeof (char));
  sprintf (pre_fname, "pre_%s", fsat->fname);
  FILE *out = fopen (pre_fname, "w");
  fprintf (out, "p cnf %d %d\n", fsat->no_vars - 1, fsat->no_clauses + 1);      // -1 on no_vars ?
#ifndef NDEBUG
  fprintf (stdout, "---- minisat query prefix: p cnf %d %d\n",
           fsat->no_vars - 1, fsat->no_clauses + 1);
#endif
  free (pre_fname);
  fclose (out);

  // test positive and negative case
  int res = -1;                 // unknown
  //    - filename for test [x in alpha]
  char *in_fname = (char *) malloc ((5 + fname_len) * sizeof (char));
  memset (in_fname, 0, (5 + fname_len) * sizeof (char));
  sprintf (in_fname, "in_%s", fsat->fname);

  //    - filename for cat command
  char *cat_command = (char *) calloc ((100 + 4 * fname_len), sizeof (char));
  memset (cat_command, 0, (100 + 4 * fname_len) * sizeof (char));
  sprintf (cat_command,
           "cat pre_%s %s in_%s 1> full_in_%s", fsat->fname, fsat->fname,
           fsat->fname, fsat->fname);

  //    - filename for minisat command
  char *msat_command = (char *) calloc ((100 + 4 * fname_len), sizeof (char));
  memset (msat_command, 0, (100 + 4 * fname_len) * sizeof (char));
  sprintf (msat_command,
           "minisat -verb=0 full_in_%s result.txt 1> msat_in_%s", fsat->fname,
           fsat->fname);
  // do the two test (positive and negative)
  for (int tst = 1; tst >= 0; tst--)
    {
      out = fopen (in_fname, "w");      // remove old content
      // write a new clause in the in_%s file
      fprintf (out, "%c%d 0\n", (tst == 1) ? '-' : ' ', bvar_x_in_alpha);
      fclose (out);

      // build the final file full_in_%s
      if (system (cat_command) != -1)
        assert (0);

      // print the minisat command and read result
      if (system (msat_command) != -1)
        {
          FILE *fres = fopen ("result.txt", "r");
          char s[10];
          fscanf (fres, "%s", s);
          fclose (fres);
          if (strcmp (s, "UNSAT") == 0)
            {
              res = tst;
            }
        }
    }
  free (in_fname);
  free (cat_command);
  free (msat_command);
  return res;
}
