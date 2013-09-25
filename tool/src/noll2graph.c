/**************************************************************************/
/*                                                                        */
/*  NOLL decision procedure                                               */
/*                                                                        */
/*  Copyright (C) 2012-2013                                               */
/*    LIAFA (University of Paris Diderot and CNRS)                        */
/*                                                                        */
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

/**
 * Translation of formulas to graphs.
 */

#include "noll2graph.h"
#include "noll2bool.h"

/**
 * Compute the number of nodes from the equalities in the pure formula.
 * @param phi input formula
 * @param vars array of size locs_array, giving the labeling of variables
 * @return number of nodes = number of equivalence classes
 */
uint_t noll_nodes_of_form(noll_form_t* phi, uint_t* vars) {
	uint_t nodes_size = 0;
	if (phi->pure) {
		for (uint_t i = 0; i < phi->pure->size; i++) {
			// search the first variable equal to this one
			uint_t min = 0;
			for (min = 0; min < i; min++)
				if (phi->pure->m[min][i - min] == NOLL_PURE_EQ)
					break;
			if (min == i) {
				// set node in the locs_vars
				vars[i] = nodes_size;
				nodes_size++;
			} else
				vars[i] = vars[min];
		}
	} else {
		// there are no equalities, set to number of variables
		nodes_size = noll_vector_size (phi->lvars);
		// each variable is associated to a node
		for (uint_t i = 0; i < noll_vector_size (phi->lvars); i++)
			vars[i] = i;
	}
	return nodes_size;
}

uint_t noll_atom_of_form(noll_space_t* phi, noll_space_op_t op) {
	uint_t res = 0;
	if (!phi)
		return res;
	if (op == phi->kind && op == NOLL_SPACE_PTO)
		return noll_vector_size (phi->m.pto.fields);
	if (op == phi->kind && op == NOLL_SPACE_LS) {
		uint_t src = noll_vector_at(phi->m.ls.args,0);
		uint_t dst = noll_vector_at(phi->m.ls.args,1);
		// remove ls edges between equal variables
		return (src == dst) ? 0 : 1;
	}
	if (phi->kind != NOLL_SPACE_WSEP && phi->kind != NOLL_SPACE_SSEP)
		return res;
	// else recursive call over separated formula
	if (phi->m.sep) {
		for (uint_t i = 0; i < noll_vector_size (phi->m.sep); i++)
			res += noll_atom_of_form(noll_vector_at (phi->m.sep, i), op);
	}
	return res;
}

/**
 * Compute the edges and the strong separation information.
 * @param phi    formulas to be translated
 * @param g      graph to be filled
 * @param nedge  start id to be assigned to edges in this formula
 * @return array of identifiers of edges generated from phi
 */
noll_uid_array*
noll_graph_of_space(noll_space_t* phi, noll_graph_t* g, uint_t nedges) {
	noll_uid_array* res = NULL;
	if (!phi)
		return res;

	switch (phi->kind) {
	case NOLL_SPACE_PTO: {
		res = noll_uid_array_new();
		noll_uid_array_reserve(res, noll_vector_size (phi->m.pto.fields));
		// source node
		uint_t nsrc = g->var2node[phi->m.pto.sid];
		// to each pto formula correspond several edges
		for (uint_t i = 0; i < noll_vector_size (phi->m.pto.fields); i++) {
			uint_t fi = noll_vector_at (phi->m.pto.fields, i);
			uint_t ndst = g->var2node[noll_vector_at (phi->m.pto.dest, i)];
			assert(ndst < g->nodes_size);
			// build the edge
			noll_edge_t* e = noll_edge_alloc(NOLL_EDGE_PTO, nsrc, ndst, fi);
			e->id = nedges + i;
			// push edge in graph
			noll_edge_array_push(g->edges, e);
			// push its identifier in the result
			noll_uid_array_push(res, e->id);
			// push the edge id in the matrix at entry nsrc
			noll_uid_array* src_edges = g->mat[nsrc];
			if (src_edges == NULL) {
				src_edges = g->mat[nsrc] = noll_uid_array_new();
			}
			noll_uid_array_push(src_edges, e->id);
			// push the edge id in the reverse matrix at entry ndst
			noll_uid_array* dst_edges = g->rmat[ndst];
			if (dst_edges == NULL) {
				dst_edges = g->rmat[ndst] = noll_uid_array_new();
			}
			noll_uid_array_push(dst_edges, e->id);
		}
		break;
	}
	case NOLL_SPACE_LS: {
		res = noll_uid_array_new();
		noll_uid_array_reserve(res, noll_vector_size (phi->m.pto.fields));
		// source node
		uint_t nsrc = g->var2node[noll_vector_at (phi->m.ls.args, 0)];
		assert(nsrc < g->nodes_size);
		// destination node
		// TODO: for dll
		uint_t ndst = g->var2node[noll_vector_at (phi->m.ls.args, 1)];
		assert(ndst < g->nodes_size);
		if (nsrc == ndst)
			return res; // no edge is built
		// build the edge
		noll_edge_t* e = noll_edge_alloc(NOLL_EDGE_PRED,
				g->var2node[noll_vector_at (phi->m.ls.args, 0)],
				g->var2node[noll_vector_at (phi->m.ls.args, 1)], phi->m.ls.pid);
		for (uint_t i = 2; i < noll_vector_size (phi->m.ls.args); i++)
			noll_uid_array_push(e->args,
					g->var2node[noll_vector_at (phi->m.ls.args, i)]);
		e->id = nedges;
		// put the edge in graph
		noll_edge_array_push(g->edges, e);
		// push its identifier in the result
		noll_uid_array_push(res, e->id);
		// push the edgeid in the matrix at entry nsrc
		noll_uid_array* src_edges = g->mat[nsrc];
		if (src_edges == NULL) {
			src_edges = g->mat[nsrc] = noll_uid_array_new();
		}
		noll_uid_array_push(src_edges, e->id);
		// push the edgeid in the reverse matrix at entry ndst
		noll_uid_array* dst_edges = g->rmat[ndst];
		if (dst_edges == NULL) {
			dst_edges = g->rmat[ndst] = noll_uid_array_new();
		}
		noll_uid_array_push(dst_edges, e->id);
		// fill the bounded sloc variable
		e->bound_svar = phi->m.ls.sid;
		break;
	}
	case NOLL_SPACE_WSEP:
	case NOLL_SPACE_SSEP: {
		// allocate the result
		res = noll_uid_array_new();
		noll_uid_array_reserve(res, noll_vector_size (phi->m.sep));
		// collect edges from each sub-formula and update the nedges
		uint_t new_nedges = nedges;
		for (uint_t i = 0; i < noll_vector_size (phi->m.sep); i++) {
			noll_uid_array* ri = noll_graph_of_space(
					noll_vector_at (phi->m.sep, i), g, new_nedges);
			// update the number of edges
			new_nedges += (ri) ? noll_vector_size (ri) : 0;
			// update the separation constraints
			if (ri && phi->kind == NOLL_SPACE_SSEP) {
				// add the separation constraints
				// between the collected edges and the new edges
				for (uint_t j = 0; j < noll_vector_size (res); j++) {
					uint_t ej = noll_vector_at (res, j);
					noll_edge_t* edge_j = noll_vector_at(g->edges, ej);
					for (uint_t k = 0; k < noll_vector_size (ri); k++) {
						uint_t ek = noll_vector_at (ri, k);
						noll_edge_t* edge_k = noll_vector_at(g->edges, ek);
						noll_uid_array_push(edge_j->ssep, ek);
						noll_uid_array_push(edge_k->ssep, ej);
					}
				}
			}
			// update the result vector
			if (ri) {
				for (uint_t k = 0; k < noll_vector_size (ri); k++)
					noll_uid_array_push(res, noll_vector_at (ri, k));
				// free the intermediate result
				noll_uid_array_delete(ri);
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
 * Fill with the inequality edges the adj matrix of g.
 * @param phi
 * @param g
 */
void noll_graph_of_pure(noll_pure_t* phi, noll_graph_t* g) {
	assert(phi);
	assert(g);
	for (uint_t i = 0; i < phi->size; i++) {
		uint_t ni = g->var2node[i];
		for (uint_t j = i + 1; j < phi->size; j++) {
			uint_t nj = g->var2node[j];
			if (phi->m[i][j - i] == NOLL_PURE_NEQ) {
				if (ni <= nj)
					g->diff[nj][ni] = true;
				else
					g->diff[ni][nj] = true;
			}

		}
	}
}

noll_graph_t*
noll_graph_of_form(noll_form_t* phi) {
	if (!phi || phi->kind == NOLL_FORM_UNSAT)
		return NULL;

	// the result graph
	noll_graph_t* res = NULL;

	// compute the number of nodes from the pure part
	uint_t* vars = (uint_t*) malloc(noll_vector_size (phi->lvars)
			* sizeof(uint_t));
	uint_t nsize = noll_nodes_of_form(phi, vars);

	// count edges pto and pred
	uint_t max_pto = noll_atom_of_form(phi->space, NOLL_SPACE_PTO);
	uint_t max_ls = noll_atom_of_form(phi->space, NOLL_SPACE_LS);
	res = noll_graph_alloc(phi->lvars, phi->svars, nsize, max_pto + max_ls,
			vars);

	// go through the space formula,
	// assign identifiers to edges, and
	// fill information in the graph
	res->is_precise = phi->space->is_precise;
	noll_uid_array* r = noll_graph_of_space(phi->space, res, 0);
	if (r == NULL) { // error
		noll_graph_free(res);
		return NULL;
	} else
		noll_uid_array_delete(r);

	// go through pure constraints to obtain distinct edges
	noll_graph_of_pure(phi->pure, res);

	// aliasing of sharing constraints in the graph
	noll_share_array_copy(res->share, phi->share);

	// TODO: sort variables and
	// TODO: apply permutation obtained on
	//       - edges (for list segments indexed by svars)
	//       - sharing constraints
	return res;
}