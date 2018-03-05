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
 * Predicates for NOLL.
 */

#include "noll_preds.h"

NOLL_VECTOR_DEFINE (noll_pred_rule_array, noll_pred_rule_t *);

NOLL_VECTOR_DEFINE (noll_pred_array, noll_pred_t *);

/* ====================================================================== */
/* Globals */
/* ====================================================================== */

noll_pred_array *preds_array;

void
noll_pred_init ()
{
  preds_array = noll_pred_array_new ();
  noll_pred_array_reserve (preds_array, 4);
}

/* ====================================================================== */
/* Constructors/Destructors */
/* ====================================================================== */

noll_pred_rule_t *
noll_pred_rule_new (void)
{
  noll_pred_rule_t *r =
    (noll_pred_rule_t *) malloc (sizeof (noll_pred_rule_t));
  r->vars = NULL;
  r->fargs = 0;
  r->pure = NULL;
  r->pto = NULL;
  r->nst = NULL;
  r->rec = NULL;
  return r;
}

void
noll_pred_rule_delete (noll_pred_rule_t * r)
{
  if (r == NULL)
    return;
  if (r->vars != NULL)
    noll_var_array_delete (r->vars);
  if (r->pure != NULL)
    noll_pure_free (r->pure);
  if (r->pto != NULL)
    noll_space_free (r->pto);
  if (r->nst != NULL)
    noll_space_free (r->nst);
  if (r->rec != NULL)
    noll_space_free (r->rec);
  free (r);
}

noll_pred_binding_t *
noll_pred_binding_new (void)
{
  noll_pred_binding_t *pdef =
    (noll_pred_binding_t *) malloc (sizeof (noll_pred_binding_t));
  pdef->pargs = 0;
  pdef->fargs = 0;
  pdef->vars = NULL;
  pdef->sigma_0 = NULL;
  pdef->sigma_1 = NULL;
  pdef->base_rules = NULL;
  pdef->rec_rules = NULL;
  return pdef;
}

void
noll_pred_binding_delete (noll_pred_binding_t * pdef)
{
  if (pdef == NULL)
    return;
  if (pdef->vars != NULL)
    noll_var_array_delete (pdef->vars);
  if (pdef->sigma_0 != NULL)
    noll_space_free (pdef->sigma_0);
  if (pdef->sigma_1 != NULL)
    noll_space_free (pdef->sigma_1);
  if (pdef->base_rules != NULL)
    noll_pred_rule_array_delete (pdef->base_rules);
  if (pdef->rec_rules != NULL)
    noll_pred_rule_array_delete (pdef->rec_rules);
  free (pdef);
}

void
noll_pred_binding_push_rule (noll_pred_binding_t * def, noll_pred_rule_t * r,
                             bool isRec)
{
  assert (def != NULL);
  assert (r != NULL);
  noll_pred_rule_array *rules = NULL;
  if (isRec == true)
    {
      if (def->rec_rules == NULL)
        def->rec_rules = noll_pred_rule_array_new ();
      rules = def->rec_rules;
    }
  else
    {
      if (def->base_rules == NULL)
        def->base_rules = noll_pred_rule_array_new ();
      rules = def->base_rules;
    }
  noll_pred_rule_array_push (rules, r);
  if ((isRec == true) && (def->sigma_0 == NULL) && (r->rec != NULL))
    {
      def->vars = r->vars;      // TODO NEW: it is kept after that ? Yes, it seems
      def->sigma_0 = r->pto;
      def->sigma_1 = r->nst;
    }
}

noll_pred_t *
noll_pred_new (const char *name, uid_t pid, noll_pred_binding_t * def)
{
  noll_pred_t *p = (noll_pred_t *) malloc (sizeof (struct noll_pred_t));
  p->pname = strdup (name);
  p->pid = pid;
  p->def = def;
  p->typ = NULL;
  /* typing info is computed after syntax analysis, @see noll_pred_type */

  return p;
}

/* ====================================================================== */
/* Other methods */
/* ====================================================================== */

uid_t
noll_pred_array_find (const char *name)
{
  if (preds_array && (noll_vector_size (preds_array) > 0))
    {
      uint_t sz = noll_vector_size (preds_array);
      for (uint_t i = 0; i < sz; i++)
        if (noll_pred_getpred (i) && !strcmp (name,
                                              noll_pred_getpred (i)->pname))
          return i;
    }
  return UNDEFINED_ID;
}

uid_t
noll_pred_register (const char *pname, noll_pred_binding_t * def)
{
  assert (NULL != pname);

  uid_t pid = 0;
  for (; pid < noll_vector_size (preds_array); pid++)
    {
      noll_pred_t *pi = noll_vector_at (preds_array, pid);
      if (0 == strcmp (pname, pi->pname))
        {
          if (pi->def != NULL && def != NULL)
            {
              printf ("Warning: rewrite predicate definition '%s'!\n", pname);
            }
          if (def != NULL)
            pi->def = def;
          return pid;
        }
    }

  /* Warning: modified to support mutually recursive definitions */
  assert (pid == noll_vector_size (preds_array));
  noll_pred_t *p = noll_pred_new (pname, pid, def);
  noll_pred_array_push (preds_array, p);
  return pid;
}

uid_t
noll_pred_typecheck_call (uid_t pid, noll_type_array * actuals_ty)
{
  if (pid == UNDEFINED_ID)
    return UNDEFINED_ID;
  const noll_pred_t *p = noll_pred_getpred (pid);
  assert (NULL != p);
  if (noll_vector_size (actuals_ty) != p->def->fargs)
    {
      // TODO: make error message
      fprintf
        (stderr,
         "Predicate call `%s': called with %d parameters instead of %d.\n",
         p->pname, noll_vector_size (actuals_ty), p->def->fargs);
      return UNDEFINED_ID;
    }
  /// p->def->vars includes nil in position 0, 
  /// while actuals_ty does not
  for (uint_t i = 1; i < p->def->fargs; i++)
    {
      noll_var_t *fi = noll_vector_at (p->def->vars, i);
      noll_type_t *fi_ty = fi->vty;
      noll_type_t *ai_ty = noll_vector_at (actuals_ty, i - 1);  /* -1 for nil */
      if (noll_type_match (fi_ty, ai_ty) == false)
        {
          // TODO: make error message
          printf ("Predicate call `%s': bad type for parameter %s.\n",
                  p->pname, fi->vname);
          return UNDEFINED_ID;
        }
    }
  return pid;
}

const noll_pred_t *
noll_pred_getpred (uid_t pid)
{
  if (pid >= noll_vector_size (preds_array))
    {
      printf
        ("noll_pred_getpred: called with identifier %d not in the global environment.\n",
         pid);
      return NULL;
    }

  return noll_vector_at (preds_array, pid);
}

const char *
noll_pred_name (uid_t pid)
{
  const noll_pred_t *pred = NULL;
  if ((pred = noll_pred_getpred (pid)) == NULL)
    {
      return "unknown";
    }

  return pred->pname;
}

const noll_type_t *
noll_pred_gettype (uid_t pid)
{
  const noll_pred_t *pred = noll_pred_getpred (pid);
  assert (pred != NULL);

  const noll_var_t *fp1 = noll_vector_at (pred->def->vars, 1);
  assert (fp1 != NULL);

  return fp1->vty;
}

/** 
 * Total ordering of predicates using their call. 
 * Used the reverse ordering of identifiers, due
 * to the parsing.
 * @return true if not (rhs calls lhs)
 */
bool
noll_pred_order_lt (uid_t lhs, uid_t rhs)
{
  return lhs > rhs;
}

/**
 * Return true if pid uses nil internally and for the base case.
 * Information computed by the typing.
 */
bool
noll_pred_use_nil (uid_t pid)
{
  assert (pid < noll_vector_size (preds_array));

  noll_pred_t *pred = noll_vector_at (preds_array, pid);

  return (NULL != pred->typ) ? pred->typ->useNil : false;
}

bool
noll_pred_isUnaryLoc (uid_t pid)
{
  assert (pid < noll_vector_size (preds_array));

  noll_pred_t *pred = noll_vector_at (preds_array, pid);

  return (NULL != pred->typ) ? pred->typ->isUnaryLoc : false;
}

/**
 * Return true if pid is a one direction predicate.
 * Information computed by the typing.
 */
bool
noll_pred_is_one_dir (uid_t pid)
{
  assert (pid < noll_vector_size (preds_array));

  noll_pred_t *pred = noll_vector_at (preds_array, pid);

  return (NULL != pred->typ && pred->typ->isTwoDir) ? false : true;
}

/**
 * Search @p fid inside the fields of predicate @p pid with a role of
 * at most kind.
 * 
 * @param pid  procedd identifier in preds_array
 * @param fid  field identifier in fields_array
 * @param kind max kind to be found for @p fid
 * @return     true if fid has a role at least kind
 */
bool
noll_pred_is_field (uid_t pid, uid_t fid, noll_field_e kind)
{
  assert (pid < noll_vector_size (preds_array));
  assert (fid < noll_vector_size (fields_array));

  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  noll_field_e k = noll_vector_at (pred->typ->pfields, fid);
  return (k <= kind) && ((kind == NOLL_PFLD_NONE) || (k > NOLL_PFLD_NONE));
}

bool
noll_pred_is_null_field (uid_t pid, uid_t fid)
{
  assert (pid < noll_vector_size (preds_array));
  assert (fid < noll_vector_size (fields_array));

  noll_pred_t *pred = noll_vector_at (preds_array, pid);
  noll_field_e k = noll_vector_at (pred->typ->pfields, fid);
  return (k == NOLL_PFLD_NULL);
}

/**
 * Return true if @p fid is a backbone for some predicate.
 * Information computed at typing, @see noll_entl_type.
 */
bool
noll_pred_is_backbone_field (uid_t fid)
{

  assert (fid < noll_vector_size (fields_array));

  noll_field_t *f = noll_vector_at (fields_array, fid);

  assert (f->pid < noll_vector_size (preds_array));

  return noll_pred_is_field (f->pid, fid, NOLL_PFLD_BORDER);
}

bool
noll_pred_is_main_backbone_field (uid_t fid)
{
  assert (fid < noll_vector_size (fields_array));

  noll_field_t *f = noll_vector_at (fields_array, fid);
  assert (NULL != f);
  assert (f->pid < noll_vector_size (preds_array));

  return noll_pred_is_field (f->pid, fid, NOLL_PFLD_BCKBONE);
}

int noll_pred_type_init (noll_pred_t * p);

int noll_pred_type_args (noll_pred_t * p);

int noll_pred_type_rule (noll_pred_t * p, uint_t level,
                         noll_pred_rule_t * rule);

int noll_pred_type_args_ext (noll_pred_t * p);

int noll_pred_type_rule_ext (noll_pred_t * p, uint_t level,
                             noll_pred_rule_t * rule);

/**
 * Type the predicate definitions.
 * @return 0 for incorrect typing
 */
int
noll_pred_type ()
{
  assert (preds_array != NULL);
  assert (fields_array != NULL);
  assert (records_array != NULL);

  int res = 1;
  /* go through all predicates starting with the simpler ones */
  for (uint_t pid = 0;
       pid < noll_vector_size (preds_array) && (res == 1); pid++)
    {
      noll_pred_t *p = noll_vector_at (preds_array, pid);

      /* initialize the typing infos */
      res = noll_pred_type_init (p);
      if (res == 0)
        return 0;

      /* type the arguments */
#ifdef SPENEXT
      res = noll_pred_type_args_ext (p);
#else
      res = noll_pred_type_args (p);
#endif
      if (res == 0)
        return 0;

      /* go through the rules to fill the infos */
      uint_t size =
        (p->def->base_rules ==
         NULL) ? 0 : noll_vector_size (p->def->base_rules);
      for (uint_t ri = 0; ri < size; ri++)
        {
#ifdef SPENEXT
          res =
            noll_pred_type_rule_ext (p, 0,
                                     noll_vector_at (p->def->base_rules, ri));
#else
          res =
            noll_pred_type_rule (p, 0,
                                 noll_vector_at (p->def->base_rules, ri));
#endif
          if (res == 0)
            return 0;
        }
      /* TODO: no need for level 1 formulas? */
      size =
        (p->def->rec_rules ==
         NULL) ? 0 : noll_vector_size (p->def->rec_rules);
      for (uint_t ri = 0; ri < size; ri++)
        {
#ifdef SPENEXT
          res =
            noll_pred_type_rule_ext (p, 1,
                                     noll_vector_at (p->def->rec_rules, ri));
#else
          res =
            noll_pred_type_rule (p, 1,
                                 noll_vector_at (p->def->rec_rules, ri));
#endif
          if (res == 0)
            return 0;
        }
    }
  return res;
}

/**
 * Alloc the type structure and fill the fields with the default values
 * @param p     predicate
 * @return      1 if ok, 0 otherwise
 */
int
noll_pred_type_init (noll_pred_t * p)
{
  if (p == NULL)
    return 0;

  /* alloc typing info field */
  p->typ = (noll_pred_typing_t *) malloc (sizeof (struct noll_pred_typing_t));

  /* predicate type = type of the first parameter */
  p->typ->ptype0 = noll_var_record (p->def->vars, 1);

  /* types covered */
  p->typ->ptypes = noll_uint_array_new ();
  /* resize the array to cover all the records, filled with 0 */
  noll_uint_array_resize (p->typ->ptypes, noll_vector_size (records_array));
  noll_vector_at (p->typ->ptypes, p->typ->ptype0) = 1;

  /* fields used */
  p->typ->pfields = noll_uint_array_new ();
  /* resize the array to cover all the fields, filled with 0 = NOLL_PFLD_NONE */
  noll_uint_array_resize (p->typ->pfields, noll_vector_size (fields_array));

  /* kind of inductive definition */
  p->typ->pkind = NOLL_PRED_OTHER;

  /* flags -- by default values, may be changed by the analysis */
  p->typ->isUnaryLoc = false;
  p->typ->useNil = false;
  p->typ->isTwoDir = false;

  /* type of arguments */
  p->typ->argkind = noll_uid_array_new ();
  noll_uid_array_reserve (p->typ->argkind, p->def->fargs);

  /* predicates called */
  p->typ->ppreds = noll_uint_array_new ();
  /* resize the array to cover all the predicates called */
  noll_uint_array_resize (p->typ->ppreds, noll_vector_size (preds_array));

  return 1;
}

/**
 * Fill the information about the predicate arguments
 * @param p     predicate
 * @return      1 if ok, 0 otherwise
 */
int
noll_pred_type_args (noll_pred_t * p)
{
  if ((p == NULL) || (p->typ == NULL) || (p->typ->argkind == NULL))
    return 0;

  /* type of arguments */
  uint_t nbLoc = 0;             /// number of location args, to fill p->typ->isUnaryLoc
  uint_t nbBag = 0;
  uint_t nbInt = 0;
  for (uint_t i = 0; i < p->def->fargs; i++)
    {
      noll_var_t *ai = noll_vector_at (p->def->vars, i + 1);    // shift for nil
      switch (ai->vty->kind)
        {
        case NOLL_TYP_RECORD:
          {
            if (nbLoc == 0)
              noll_uid_array_push (p->typ->argkind, NOLL_ATYP_LROOT);
            else if (nbLoc == 1)
              // TODO: deal correctly with parent arguments
              noll_uid_array_push (p->typ->argkind, NOLL_ATYP_LPENDING);
            else
              noll_uid_array_push (p->typ->argkind, NOLL_ATYP_BORDER);
            nbLoc++;
            break;
          }
        case NOLL_TYP_BAGINT:
          {
            if ((nbBag == 0) || (nbLoc == 1))
              /// no bag seen before or still in the root part
              noll_uid_array_push (p->typ->argkind, NOLL_ATYP_BROOT);
            else if ((nbBag >= 1) && (nbLoc == 2))
              noll_uid_array_push (p->typ->argkind, NOLL_ATYP_BPENDING);
            else
              noll_uid_array_push (p->typ->argkind, NOLL_ATYP_BORDER);
            nbBag++;
            break;
          }
        case NOLL_TYP_INT:
          {
            if ((nbInt == 0) || (nbLoc == 1) || (nbBag == 1))
              /// no int seen before or still in the root part
              noll_uid_array_push (p->typ->argkind, NOLL_ATYP_IROOT);
            else if ((nbInt >= 1) && (nbLoc == 2))
              noll_uid_array_push (p->typ->argkind, NOLL_ATYP_IPENDING);
            else
              noll_uid_array_push (p->typ->argkind, NOLL_ATYP_BORDER);
            nbInt++;
            break;
          }
        default:
          break;
        }
    }
  /// this first guess is confirmed by typing rules

  /* only one location arg = unary predicate */
  if (nbLoc == 1)
    p->typ->isUnaryLoc = true;

  /* two direction predicate */
  /* TODO: better test using the predicate definition */
  p->typ->isTwoDir = (0 == strcmp (p->pname, "dll")) ? true : false;

  return 1;
}


/**
 * Fill the arguments flds and typs, if not null, with the
 * fields resp. record ids, obtained from formula form.
 * @param p      predicate 
 * @param level  level (0 -- base or 1 -- rec) of the analyzed formulas 
 * @param form   analyzed formula
 */
int
noll_pred_type_rule_pure (noll_pred_t * p, uint_t level, noll_pure_t * form)
{
  if (form == NULL)
    return 1;

  /// get indexes guessed for root and pending for location, bag and data
  uid_t vidLRoot = UNDEFINED_ID;
  uid_t vidLPend = UNDEFINED_ID;
  uid_t vidBRoot = UNDEFINED_ID;
  uid_t vidBPend = UNDEFINED_ID;
  uid_t vidIRoot = UNDEFINED_ID;
  uid_t vidIPend = UNDEFINED_ID;
  for (uint_t i = 0; i < p->def->fargs; i++)
    switch (noll_vector_at (p->typ->argkind, i))
      {
      case NOLL_ATYP_LROOT:
        vidLRoot = i + 1;
        break;
      case NOLL_ATYP_LPENDING:
        vidLPend = i + 1;
        break;
      case NOLL_ATYP_BROOT:
        vidBRoot = i + 1;
        break;
      case NOLL_ATYP_BPENDING:
        vidBPend = i + 1;
        break;
      case NOLL_ATYP_IROOT:
        vidIRoot = i + 1;
        break;
      case NOLL_ATYP_IPENDING:
        vidIPend = i + 1;
        break;
      default:
        break;
      }
  /* compute class using argument types */
  if (vidLRoot == UNDEFINED_ID)
    /* nothing to do, class NOLL_PRED_OTHER */
    return 0;
  /* there is a root, guess class NOLL_PRED_WS */
  p->typ->pkind = NOLL_PRED_WS;

  if ((vidLPend == UNDEFINED_ID) &&
      ((vidBPend != UNDEFINED_ID) || (vidIPend != UNDEFINED_ID)))
    return 0;
  if ((vidBRoot == UNDEFINED_ID) && (vidBPend != UNDEFINED_ID))
    return 0;
  if ((vidIRoot == UNDEFINED_ID) && (vidIPend != UNDEFINED_ID))
    return 0;
  /* all arguments are symmetric, guess class NOLL_PRED_COMP */
  p->typ->pkind = NOLL_PRED_COMP;


  /// check that pure includes (in-)equality between 
  ///  - root with 'nil' or root with pending  
  noll_pure_op_t op = NOLL_PURE_EQ;
  if (vidLPend == UNDEFINED_ID)
    op = noll_pure_matrix_at (form, 0, vidLRoot);       // 0 is nil
  else
    op = noll_pure_matrix_at (form, vidLRoot, vidLPend);
  if ((level == 0 && op != NOLL_PURE_EQ) ||
      (level >= 1 && op == NOLL_PURE_EQ))
    {
      p->typ->pkind = NOLL_PRED_WS;
      return 0;
    }

  if ((op != NOLL_PURE_EQ) || (level > 0))
    return 1;

  /// check that, if op is =,  
  /// then form includes the same think for msets and data pending      
  assert (level == 0 && op == NOLL_PURE_EQ);
  if ((vidBPend != UNDEFINED_ID) &&
      (noll_pure_matrix_at (form, vidBRoot, vidBPend) != op))
    {
      p->typ->pkind = NOLL_PRED_WS;
      return 0;
    }
  if ((vidIPend != UNDEFINED_ID) &&
      (noll_pure_matrix_at (form, vidIRoot, vidIPend) != op))
    {
      p->typ->pkind = NOLL_PRED_WS;
      return 0;
    }
  // TODO: check also data constraints
  return 1;
}

/**
 * Fill the arguments flds and typs, if not null, with the
 * fields resp. record ids, obtained from formula form.
 * @param p      predicate 
 * @param level  level (0 -- base or 1 -- rec) of the analyzed formulas 
 * @param form   analyzed formula
 */
int
noll_pred_type_rule_form (noll_pred_t * p, uint_t level,
                          noll_var_array * lvars, uint_t fargs,
                          noll_space_t * form)
{
  if ((form == NULL) || (form->kind == NOLL_SPACE_EMP))
    return 1;

  switch (form->kind)
    {
    case NOLL_SPACE_PTO:
      {
        //if (level == 1)  // TODO: check done at parsing?!
        //  return 0;             /* no pto in inner formulas! */

        //if (form->m.pto.sid != 1)  // TODO: allow for RBT
        /* only pto from first argument */
        //  return 0;             /* TODO: already checked? */

        for (uid_t i = 0; i < noll_vector_size (form->m.pto.fields); i++)
          {
            uid_t fid = noll_vector_at (form->m.pto.fields, i);
            uid_t dst = noll_vector_at (form->m.pto.dest, i);

            /* fill type infos with type of dst */
            uid_t dst_r = noll_var_record (lvars, dst);
            if (dst_r != UNDEFINED_ID)
              noll_vector_at (p->typ->ptypes, dst_r) = 1;

            /* fill field info depending on dst */
            /* dst is in 0 -- NULL -- to noll_vector_size(p->def->vars) */
            if (dst == 0)
              {
                /* dst == NULL */
                noll_vector_at (p->typ->pfields, fid) = NOLL_PFLD_NULL;
                p->typ->useNil = true;
              }
            else if (dst <= p->def->fargs)
              {
                /* to the arguments */
                noll_vector_at (p->typ->pfields, fid) = NOLL_PFLD_BORDER;
              }
            else if (dst == (fargs + 1))
              {
                /* dst == first existential var, then level 0 */
                noll_vector_at (p->typ->pfields, fid) = NOLL_PFLD_BCKBONE;
              }
            else if (dst_r == UNDEFINED_ID)
              {
                /* dst is a data variable */
                noll_vector_at (p->typ->pfields, fid) = NOLL_PFLD_DATA;
              }
            else
              {
                /* dst == other existentials */
                for (uint_t ex = fargs + 2;
                     ex < noll_vector_size (lvars); ex++)
                  if (dst == ex)
                    {
                      noll_vector_at (p->typ->pfields, fid) = NOLL_PFLD_INNER;
                      break;
                    }
              }
            if (noll_vector_at (p->typ->pfields, fid) == NOLL_PFLD_NONE)
              return 0;         /* the field info is not filled correctly */
          }
        break;
      }
    case NOLL_SPACE_LS:
      {
        uint_t cpid = form->m.ls.pid;
        const noll_pred_t *cp = noll_pred_getpred (cpid);
        /* if a recursive call, nothing to do */
        if (cpid == p->pid)
          return 1;
        /* fill pred info */
        noll_vector_at (p->typ->ppreds, cpid) = 1;
        if (cp && cp->typ)
          {
            // copy called pred information in the arrays
            if (cp->typ->pfields)
              for (uid_t fid = 0; fid < noll_vector_size (fields_array);
                   fid++)
                {
                  noll_field_e cpfkind =
                    noll_vector_at (cp->typ->pfields, fid);
                  noll_field_e pfkind = noll_vector_at (p->typ->pfields, fid);
                  if (cpfkind != NOLL_PFLD_NONE && cpfkind != NOLL_PFLD_NULL)
                    {
                      /* the field is used in cpid and 
                       * it shall not be reused as backbone (level 0) in caller pids */
                      if ((pfkind == NOLL_PFLD_BCKBONE) &&
                          (noll_option_is_checkTA () == true))
                        {
                          /* error, shared field between predicates : stop ! */
                          fprintf (stderr,
                                   "Error in predicate typing: shared backbone field fid-%d!\n",
                                   fid);
                          fprintf (stderr,
                                   "\t\t between predicates pid-%d < pid-%d\n",
                                   p->pid, cpid);
                          // TODO: put in form
                          return 0;
                        }
                      // set to nested only if the field has not another
                      // function in p
                      if (pfkind == NOLL_PFLD_NONE)
                        noll_vector_at (p->typ->pfields, fid) =
                          NOLL_PFLD_NESTED;
                    }
                }
            if (cp->typ->useNil)
              p->typ->useNil = true;
            if (cp->typ->ptypes)
              for (uid_t rid = 0; rid < noll_vector_size (records_array);
                   rid++)
                {
                  if (noll_vector_at (cp->typ->ptypes, rid) == 1)
                    noll_vector_at (p->typ->ptypes, rid) = 1;
                }
          }
        break;
      }
    default:
      {
        // separation formula
        for (uid_t i = 0; i < noll_vector_size (form->m.sep); i++)
          if (0 ==
              noll_pred_type_rule_form (p, level, lvars, fargs,
                                        noll_vector_at (form->m.sep, i)))
            return 0;
        break;
      }
    }
  return 1;
}

/**
 * Fill the arguments flds and typs, if not null, with the
 * fields resp. record ids, obtained from the rule.
 * @param p      predicate 
 * @param level  level (0 -- base or 1 -- rec) of the analyzed rule 
 * @param rule   analyzed rule
 */
int
noll_pred_type_rule (noll_pred_t * p, uint_t level, noll_pred_rule_t * rule)
{
  if (rule == NULL)
    return 1;

  int res =
    noll_pred_type_rule_pure (p, (rule->rec == NULL) ? 0 : 1, rule->pure);
  if (res == 0)
    return 0;
  res =
    noll_pred_type_rule_form (p, level, rule->vars, rule->fargs, rule->pto);
  if (res == 0)
    return 0;
  res =
    noll_pred_type_rule_form (p, level, rule->vars, rule->fargs, rule->nst);
  if (res == 0)
    return 0;
  res =
    noll_pred_type_rule_form (p, level, rule->vars, rule->fargs, rule->rec);
  return res;
}

/**
 * Order the fields using the predicate definitions.
 * @return 0 for incorrect ordering
 */
int
noll_field_order ()
{

  /* pre-analysis: 
   * go through the predicates and 
   * set owner for backbone fields */
  for (uint_t pid = 0; pid < noll_vector_size (preds_array); pid++)
    {
      noll_pred_t *p = noll_vector_at (preds_array, pid);
      /* search the backbones and set owner */
      for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
        if (noll_vector_at (p->typ->pfields, fid) == NOLL_PFLD_BCKBONE)
          {
            noll_field_t *f = noll_vector_at (fields_array, fid);
            if (f->pid == UNDEFINED_ID)
              f->pid = pid;
            else if (noll_option_is_checkTA () == true)
              {
#ifndef NDEBUG
                fprintf (stdout, "Error: shared backbone field %d!\n", fid);
#endif
                assert (false);
              }
          }
    }

  uint_t no = 0;
  /* go through the predicates, in reverse order,
   * and fill the infos on fields */
  for (uint_t pid = noll_vector_size (preds_array) - 1; (pid + 1) >= 1; pid--)
    {
      noll_pred_t *p = noll_vector_at (preds_array, pid);
      /* search the backbones and order them */
      for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
        if (noll_vector_at (p->typ->pfields, fid) == NOLL_PFLD_BCKBONE)
          {
            noll_field_t *f = noll_vector_at (fields_array, fid);
            if (f->order == UNDEFINED_ID)
              {                 /* test that it is not already filled ! */
                f->order = no++;
                f->kind = NOLL_PFLD_BCKBONE;
                f->pid = pid;
              }
#ifndef NDEBUG
            fprintf (stdout, "Field %s @(pid = %d, kind = %d) order=%d\n",
                     f->name, pid,
                     noll_vector_at (p->typ->pfields, fid), f->order);
#endif
          }
      /* search for inner fields */
      for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
        if (noll_vector_at (p->typ->pfields, fid) == NOLL_PFLD_INNER)
          {
            noll_field_t *f = noll_vector_at (fields_array, fid);
            if (f->order == UNDEFINED_ID && f->pid == UNDEFINED_ID)
              {                 /* test that it is not already filled ! */
                f->order = no++;
                f->pid = pid;
                f->kind = NOLL_PFLD_INNER;
              }
#ifndef NDEBUG
            fprintf (stdout, "Field %s @(pid = %d, kind = %d) order=%d\n",
                     f->name, pid,
                     noll_vector_at (p->typ->pfields, fid), f->order);
#endif
          }
      /* search for NULL fields */
      for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
        if (noll_vector_at (p->typ->pfields, fid) == NOLL_PFLD_NULL)
          {
            noll_field_t *f = noll_vector_at (fields_array, fid);
            if (f->order == UNDEFINED_ID && f->pid == UNDEFINED_ID)
              {
                /* test that it is not already filled ! */
                f->order = no++;
                f->pid = pid;
                f->kind = NOLL_PFLD_NULL;
              }
#ifndef NDEBUG
            fprintf (stdout, "Field %s @(pid = %d, kind = %d) order=%d\n",
                     f->name, pid,
                     noll_vector_at (p->typ->pfields, fid), f->order);
#endif
          }
      /* search for to border fields */
      for (uint_t fid = 0; fid < noll_vector_size (fields_array); fid++)
        if (noll_vector_at (p->typ->pfields, fid) == NOLL_PFLD_BORDER)
          {
            noll_field_t *f = noll_vector_at (fields_array, fid);
            if (f->order == UNDEFINED_ID && f->pid == UNDEFINED_ID)
              {
                /* test that it is not already filled ! */
                f->order = no++;
                f->pid = pid;
                f->kind = NOLL_PFLD_BORDER;
              }
#ifndef NDEBUG
            fprintf (stdout, "Field %s @(pid = %d, kind = %d) order=%d\n",
                     f->name, pid,
                     noll_vector_at (p->typ->pfields, fid), f->order);
#endif
          }
    }
#ifndef NDEBUG
#endif
  return 1;
}


uid_t
noll_pred_get_minfield (uid_t pid)
{
  const noll_pred_t *pred = noll_pred_getpred (pid);
  assert (NULL != pred);
  assert (NULL != pred->typ);
  const noll_uint_array *fields = pred->typ->pfields;
  assert (NULL != fields);

  uid_t minfield_candidate = (uid_t) - 1;
  for (size_t i = 0; i < noll_vector_size (fields); ++i)
    {
      if (1 == noll_vector_at (fields, i))
        {                       // if the field is used in the predicate
          if (((uid_t) - 1 == minfield_candidate)
              || noll_field_lt (i, minfield_candidate))
            {
              minfield_candidate = i;
            }
        }
    }

  // make sure that there was some minimum field
  assert ((uid_t) - 1 != minfield_candidate);

  return minfield_candidate;
}

/**
 * Build a formula from the matrix of the predicate.
 * Unfolds one time the matrix.
 * @param pid   predicate identifier
 * @param args  predicate actual argument
 * @result      a formula which contains the matrix of the predicate
 *              instantiated with the actual arguments
 */
noll_form_t *
noll_pred_get_matrix1 (uid_t pid)
{

  const noll_pred_t *pred = noll_pred_getpred (pid);
  assert (pred != NULL);

  /* pred->def->vars is an array built from
   * - nil (at entry 0 of the array)
   * - args (starting at entry 1 until pred->def->fargs
   * - existentially quantified variables 
   */

  /* Build and empty formula */
  noll_form_t *res = noll_form_new ();
  res->kind = NOLL_FORM_SAT;
  noll_var_array_copy (res->lvars, pred->def->vars);    // copy all from vars
  /* TODO: use svars for nested predicate calls */
  res->svars = noll_var_array_new ();   // Warning: do not use NULL
  res->share = noll_share_array_new (); // Warning: do not use NULL
  /* - build the pure part E != {F} U B */
  res->pure = noll_pure_new (noll_vector_size (pred->def->vars));
  noll_form_add_neq (res, 1, 0);
  for (size_t i = 2; i < noll_vector_size (pred->def->vars); i++)
    noll_form_add_neq (res, 1, i);

  /* - build the spatial part */
  if (pred->def->sigma_1 == NULL)
    res->space = pred->def->sigma_0;    // TODO: make a copy
  else
    {
      res->space = noll_space_new ();
      res->space->kind = NOLL_SPACE_SSEP;
      if (pred->def->sigma_1->kind == NOLL_SPACE_SSEP)
        {
          /* TODO: deal with loop */
          noll_space_array_copy (res->space->m.sep,
                                 pred->def->sigma_1->m.sep);
          noll_space_array_push (res->space->m.sep, pred->def->sigma_0);
        }
      else
        {
          res->space->m.sep = noll_space_array_new ();
          noll_space_array_push (res->space->m.sep, pred->def->sigma_0);
          /* TODO: deal with loop */
          noll_space_array_push (res->space->m.sep, pred->def->sigma_1);
        }
    }
  /* substitute formal arguments with actual arguments */
#ifndef NDEBUG
  fprintf (stderr, "\n- matrix formula \n");
  noll_form_fprint (stderr, res);
  fflush (stderr);
#endif

  return res;
}


/**
 * Build a formula from the matrix of the predicate.
 * Unfolds two times the matrix.
 * @param pid   predicate identifier
 * @param args  predicate actual argument
 * @result      a formula which contains the matrix of the predicate
 *              instantiated with the actual arguments
 */
noll_form_t *
noll_pred_get_matrix (uid_t pid)
{

  const noll_pred_t *pred = noll_pred_getpred (pid);
  assert (pred != NULL);

  /* pred->def->vars is an array built from
   * - nil (at entry 0 of the array)
   * - args (starting at entry 1 until pred->def->fargs
   * - existentially quantified variables 
   */

  /* Build and empty formula */
  noll_form_t *res = noll_form_new ();
  res->kind = NOLL_FORM_SAT;
  /* copy all from vars */
  noll_var_array_copy (res->lvars, pred->def->vars);
  /* insert a copy of existential variables from X_tl+1 ... */
  for (size_t i = pred->def->fargs + 2;
       i < noll_vector_size (pred->def->vars); i++)
    {
      noll_var_t *vi = noll_vector_at (pred->def->vars, i);
      noll_var_t *vip = noll_var_copy (vi);
      /* change the name by adding a p suffix */
      size_t nlen = strlen (vi->vname) + 2;     // p and \O
      vip->vname = (char *) realloc (vip->vname, nlen * sizeof (char));
      snprintf (vip->vname, nlen, "%sp", vi->vname);
      vip->vid =
        noll_vector_size (pred->def->vars) + i - pred->def->fargs - 2;
      noll_var_array_push (res->lvars, vip);
    }
#ifndef NDEBUG
  fprintf (stderr, "\n- new list of variables \n");
  noll_var_array_fprint (stderr, res->lvars, ", ");
  fflush (stderr);
#endif

  /* TODO: use svars for nested predicate calls */
  res->svars = noll_var_array_new ();   // Warning: do not use NULL
  res->share = noll_share_array_new (); // Warning: do not use NULL

  /* - build the pure part 
   *     E != {NULL, F} U B 
   *     X_tl != {NULL, F} U B
   *     TODO: E != X_tl is computed by normalisation 
   */
  res->pure = noll_pure_new (noll_vector_size (res->lvars));
  uid_t id_in = 1;
  uid_t id_x_tl = pred->def->fargs + 1;
  /* E != NULL, X_tl != NULL */
  noll_form_add_neq (res, id_in, 0);
  noll_form_add_neq (res, id_x_tl, 0);
  /* E != X_tl */
  noll_form_add_neq (res, id_x_tl, id_in);
  for (uid_t i = 1; i < pred->def->fargs; i++)
    {
      /* args in res->lvars are shifted by 1 to introduce NULL */
      noll_form_add_neq (res, id_in, i + 1);
      noll_form_add_neq (res, id_x_tl, i + 1);
    }

  /* - build the spatial part */
  uint_t res_size = 0;
  res->space = noll_space_new ();
  res->space->kind = NOLL_SPACE_SSEP;
  res->space->m.sep = noll_space_array_new ();
  /*    + push the first unfolding */
  noll_space_array_push (res->space->m.sep, pred->def->sigma_0);        // TODO: make a copy
  res_size++;
  if (pred->def->sigma_1 != NULL)
    {
      if (pred->def->sigma_1->kind == NOLL_SPACE_SSEP)
        {
          /* TODO: unfold the loop construct */
          for (uint_t i = 0;
               i < noll_vector_size (pred->def->sigma_1->m.sep); i++)
            {
              noll_space_array_push (res->space->m.sep,
                                     noll_vector_at (pred->def->sigma_1->m.
                                                     sep, i));
              res_size++;
            }
        }
      else
        {
          /* TODO: unfold the loop construct */
          noll_space_array_push (res->space->m.sep, pred->def->sigma_1);
          res_size++;
        }
    }

  /*    + push the second unfolding and substitute existentials by new vars */
  noll_uid_array *alpha = noll_uid_array_new ();
  noll_uid_array_push (alpha, 0);       // null unchanged
  noll_uid_array_push (alpha, id_x_tl); // E is replaced by X_tl
  for (uid_t i = 1; i < pred->def->fargs; i++)
    noll_uid_array_push (alpha, i + 1); // args are unchanged
  noll_uid_array_push (alpha, 2);       // X_tl is replaced by F
  /* the newly introduced vars replace the old ones */
  for (uid_t i = pred->def->fargs + 2;
       i < noll_vector_size (pred->def->vars); i++)
    {
      /* new existential variables substitute ones in the definition */

      noll_uid_array_push (alpha, noll_vector_size (pred->def->vars)
                           + i - pred->def->fargs - 2);
    }
#ifndef NDEBUG
  fprintf (stderr, "\n- substitution: ");
  for (uid_t i = 0; i < noll_vector_size (alpha); i++)
    fprintf (stderr, "%s -> %s, ",
             noll_var_name (res->lvars, i, NOLL_TYP_RECORD),
             noll_var_name (res->lvars, noll_vector_at (alpha, i),
                            NOLL_TYP_RECORD));
  fprintf (stderr, "\n");
  fflush (stderr);
#endif

  for (uint_t j = 0; j < res_size; j++)
    {
      noll_space_t *sj = noll_vector_at (res->space->m.sep, j);
      noll_space_t *sj_sub = noll_space_sub (sj, alpha);
#ifndef NDEBUG
      fprintf (stderr, "\n\tsub-%d formula \n", j);
      noll_space_fprint (stderr, res->lvars, NULL, sj_sub);
      fflush (stderr);
#endif
      noll_space_array_push (res->space->m.sep, sj_sub);
    }

  /* free allocated memory */
  noll_uid_array_delete (alpha);

#ifndef NDEBUG
  fprintf (stderr, "\n- matrix formula \n");
  noll_form_fprint (stderr, res);
  fflush (stderr);
#endif

  return res;
}


/* ====================================================================== */
/* Printing */
/* ====================================================================== */

void
noll_pred_type_fprint (FILE * f, noll_pred_typing_t * typ)
{
  if (typ == NULL)
    {
      fprintf (f, "NULL\n");
      return;
    }
  fprintf (f, " class=[");
  switch (typ->pkind)
    {
    case NOLL_PRED_LST_PAR:
      fprintf (f, "list-like, with parent");
      break;
    case NOLL_PRED_LST:
      fprintf (f, "list-like, one dir");
      break;
    case NOLL_PRED_COMP_PAR:
      fprintf (f, "compositional, with parent");
      break;
    case NOLL_PRED_COMP:
      fprintf (f, "compositional, one dir");
      break;
    case NOLL_PRED_WS:
      fprintf (f, "well structured");
      break;
    default:
      fprintf (f, "default");
      break;
    }
  fprintf (f, " argkind=[");
  for (uint_t i = 0; i < noll_vector_size (typ->argkind); i++)
    fprintf (f, "%d: %d,", i, noll_vector_at (typ->argkind, i));
  fprintf (f, "]\n");

  fprintf (f, " %s, ", noll_record_name (typ->ptype0));
  fprintf (f, "\n\t\tall types [");
  if (typ->ptypes != NULL)
    for (uint_t ti = 0; ti < noll_vector_size (typ->ptypes); ti++)
      if (noll_vector_at (typ->ptypes, ti) == 1)
        fprintf (f, "%s, ", noll_record_name (ti));
  fprintf (f, "], ");
  fprintf (f, "\n\t\trec fields [");
  if (typ->pfields != NULL)
    for (uint_t fi = 0; fi < noll_vector_size (typ->pfields); fi++)
      fprintf (f, "%s(kind-%d), ", noll_field_name (fi),
               noll_vector_at (typ->pfields, fi));
  fprintf (f, "]\n");

}

void
noll_pred_rule_fprint (FILE * f, noll_pred_rule_t * rule)
{
  fprintf (f, "\nrule: ");
  noll_var_array_fprint (f, rule->vars, "exists ");
  fprintf (f, ". \n\t(pure) ");
  noll_pure_fprint (f, rule->vars, rule->pure);
  fprintf (f, "\n\t & (pto) ");
  noll_space_fprint (f, rule->vars, NULL, rule->pto);
  fprintf (f, "\n\t  * (nst) ");
  noll_space_fprint (f, rule->vars, NULL, rule->nst);
  fprintf (f, "\n\t  * (rec) ");
  noll_space_fprint (f, rule->vars, NULL, rule->rec);
}

void
noll_pred_fprint (FILE * f, uid_t pid)
{
  assert (pid < noll_vector_size (preds_array));

  noll_pred_t *pi = noll_vector_at (preds_array, pid);
  fprintf (f, "pred-%d: %s(%d args) ", pi->pid, pi->pname, pi->def->fargs);
  fprintf (f, "of type ");
  noll_pred_type_fprint (f, pi->typ);

  fprintf (f, "of rules ");
  if (pi->def == NULL)
    {
      fprintf (f, "NULL\n");
      return;
    }
  assert (pi->def->base_rules != NULL);
  for (uint_t ri = 0; ri < noll_vector_size (pi->def->base_rules); ri++)
    noll_pred_rule_fprint (f, noll_vector_at (pi->def->base_rules, ri));
  assert (pi->def->rec_rules != NULL);
  for (uint_t ri = 0; ri < noll_vector_size (pi->def->rec_rules); ri++)
    noll_pred_rule_fprint (f, noll_vector_at (pi->def->rec_rules, ri));
}

void
noll_pred_array_fprint (FILE * f, noll_pred_array * a, const char *msg)
{
  fprintf (f, "\n%s: ", msg);
  fflush (f);
  if (!a)
    {
      fprintf (f, "null\n");
      return;
    }
  fprintf (f, "[");
  uint_t length_a = noll_vector_size (a);
  for (uint_t i = 0; i < length_a; i++)
    {
      noll_pred_fprint (f, i);
      fprintf (f, "\n");
    }
  fprintf (f, " - ]");
  fflush (f);
}
