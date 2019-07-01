/**************************************************************************/
/*                                                                        */
/*  SPEN decision procedure                                               */
/*                                                                        */
/*  you can redistribute it and/or modify it under the terms of the GNU   */
/*  Lesser General Public License as published by the Free Software       */
/*  Foundation, version 3.                                                */
/*                                                                        */
/*  It is distributed in the hope that it will be useful,                 */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the         */
/*  GNU Lesser General Public License for more details.                   */
/*                                                                        */
/*  See the GNU Lesser General Public License version 3.                  */
/*  for more details (enclosed in the file LICENSE).                      */
/*                                                                        */
/**************************************************************************/

#include <stdio.h>
#include "smtlib2noll.h"
#include "noll_option.h"
#include "noll_ta_symbols.h"

/* ====================================================================== */
/* MAIN/Main/main */
/* ====================================================================== */

/**
 * Print informations on usage.
 */
void
print_help (void)
{
  printf ("spen: decision procedure for SLRD, version 1.1\n");
  printf ("Usage: spen [options] file [output]\n");
  noll_option_print (stdout);
  printf ("  file   input file in SMTLIB2 format\n");
  printf ("  output proof of sat/unsat\n");
  printf
    ("See http://www.liafa.univ-paris-diderot.fr/spen for more details.\n");
}

/**
 * Entry of the decision procedure.
 * @requires: only one problem per file
 *
 * Call: spen [-n|-b|-o|-o1|-o2] file.smt
 */
int
main (int argc, char **argv)
{
  // Step 0: Check the arguments
  if (argc <= 1)
    {
      print_help ();
      return 1;
    }
  int arg_file = 1;
  while (arg_file < argc)
    {
      int opt = noll_option_set (argv[arg_file]);
      if (opt == 1)
        arg_file++;
      else if (opt == -1)
        {
          print_help ();
          return 1;
        }
      else
        break;
    }
  if (arg_file >= argc)
    {

      printf ("no input file\n");
      print_help ();
      return 1;
    }

  if (noll_option_get_verb () > 0)
    fprintf (stdout, "spen on file %s\n", argv[arg_file]);

  // Step 1: Parse the file and initialize the problem
  // pre: the file shall exists.
  FILE *f = fopen (argv[arg_file], "r");
  if (!f)
    {
      printf ("File %s not found!\nquit.", argv[arg_file]);
      return 1;
    }

  // initialize the TA symbol database
  noll_ta_symbol_init ();

  // initialize the problem
  noll_entl_init ();
  noll_entl_set_fname (argv[arg_file]);
  if ((arg_file + 1) < argc)
    noll_entl_set_foutput (argv[arg_file + 1]);

  if (noll_option_get_verb () > 0)
    fprintf (stdout, "  > parse file %s\n", argv[arg_file]);
  // call the parser
  smtlib2_noll_parser *sp = smtlib2_noll_parser_new ();
  smtlib2_abstract_parser_parse ((smtlib2_abstract_parser *) sp, f);

  // Step 2: call the solving execute the commands in the file (check-sat)
  // done in (noll.c) noll_check
  // also sets the smtlib2 parser result

  // Step 3: finish (free memory, etc.)
  smtlib2_noll_parser_delete (sp);
  fclose (f);
  noll_entl_free ();
  noll_ta_symbol_destroy ();    // destroy the TA symbol database

  return 0;
}
