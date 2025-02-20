use std::{collections::{HashMap, HashSet}, rc::Rc};

use log::debug;

use crate::{rules::EOrderRule, sorter::GraphData};



/// newtype that allows matrices to be accessed as a tuple, so the weird indexing math only needs to happen in one place
/// It corresponds to the matrix representation of the Zeta function of a category
/// It is a bit expensive to construct, but once constructed it lets us check if two objects lie in a cycle in O(1) time.
/// this is useful for building the skeleton
#[derive(Debug, Clone)]
struct ZetaMatrix{
	matr: Box<[bool]>,
	n: usize,
}

impl ZetaMatrix {
	/// Create a new matrix, with everything filled with zeros.
	/// `n` must be small enough that `n.pow(2) <= usize::MAX`.
	fn new(n: usize) -> Self {
		Self{
			matr: std::iter::repeat_n(false, n.pow(2)).collect(),
			n
		}
	}
}
// implement indexing traits to allow indexing with a tuple
impl std::ops::Index<(usize, usize)> for ZetaMatrix {
	type Output = bool;
	#[inline]
	fn index(&self, (i, j): (usize, usize)) -> &Self::Output {
		&self.matr[i * self.n + j]
	}

	
}
impl std::ops::IndexMut<(usize, usize)> for ZetaMatrix {
	#[inline]
	fn index_mut(&mut self, (i, j): (usize, usize)) -> &mut Self::Output {
		&mut self.matr[i * self.n + j]
	}
}

pub const CMP_MAX_ITERS: usize = 100;


pub fn sort(data: &GraphData) -> Vec<&str> {

	let num_nodes = data.index_dict.len();
	let mut zeta_mat = ZetaMatrix::new(num_nodes);
	
	let edges = data.edges.as_slice();

	for &e in edges {
		zeta_mat[e] = true;
	}


	// Fill out the transitivity information for the matrix.
	// There is probably a way to do this without a quadruple `for` loop. Oh well!
	// Besides, we aren't doing any expensive computations in the loop so it's probably okay for now.
	// This outer loop should only run at most 15-20 times
	for _ in 0 .. CMP_MAX_ITERS {
		let mut made_a_change = false;
		// iterate over all pairs
		for a in 0 .. num_nodes {
			for b in 0 .. num_nodes {
				if !zeta_mat[(a,b)] { continue; }

				for c in 0 .. num_nodes {
					if zeta_mat[(b,c)] && !zeta_mat[(a,c)] {
						made_a_change = true;
						zeta_mat[(a,c)] = true;
					}
				}
			}
		}
		if !made_a_change {
			break;
		}
	}

	let mut equivalence_classes: Vec<Box<[usize]>> = Vec::with_capacity(num_nodes);
	let mut reps: Vec<usize> = Vec::with_capacity(num_nodes);
	// hashset to prevent us from adding the same element twice
	let mut seen_elems: HashSet<usize> = HashSet::new();
	for a in 0 .. num_nodes {
		// already added this node? then skip it
		if seen_elems.contains(&a) { 
			continue; 
		}
		let mut cls = vec![a];
		// for all b != a
		for b in (0.. a-1).chain(a+1 .. num_nodes) {
			// if a <= b and b <= a
			// i.e., if `a` and `b` lie in a cycle.
			if zeta_mat[(a,b)] && zeta_mat[(b,a)] {
				cls.push(b);
			}
		}
		// mark every item in this equivalence class as seen
		seen_elems.extend(&cls);
		equivalence_classes.push(cls.into_boxed_slice());
		// mark `a` as the chosen representative.
		reps.push(a);
	}

	// now, do a topological sort on the equivalence classes.
	// fml

	// reset the collection of seen elements so we can reuse it without canibalizing the order matrix.
	seen_elems.clear();

	
	// NOTE: Now that we have constructed the collection of representatives, we can can canibalize the zeta matrix.
	// We'll use the zeta matrix to do a shittier topological sort.
	// We can't do a proper topological sort since the zeta matrix stores transitivity information.

	// Runtime performance could possibly be improved by also storing a non-transitive matrix.
	// However, we can't use the initial set of edges for this, so we'd have to make our own.

	#[cfg(debug_assertions)]
	{
		debug!("Printing cycles...");
		for (cls_num, cls) in equivalence_classes.iter().enumerate() {
			let mut cycle_mod_names = vec![];
			for i in cls {
				cycle_mod_names.push(data.index_dict_rev[i].as_str());
			}
			debug!("\t{cls_num}: {cycle_mod_names:?}");
		}
	}

	let mut sorted_mods = Vec::with_capacity(num_nodes);

	let mut initial_rep_indices = Vec::new();

	// initialize initial representatives and kill the symmetry of zeta.
	'outer: for (i, &a_rep) in reps.iter().enumerate() {
		zeta_mat[(a_rep, a_rep)] = false;
		// check if a is initial, if not, then bail
		for &b_rep in &reps {
			if zeta_mat[(b_rep, a_rep)] {
				continue 'outer;
			}
		}
		initial_rep_indices.push(i);
	}

	while let Some(i) = initial_rep_indices.pop() {
		// add all equivalent elements
		for idx in &equivalence_classes[i] {
			sorted_mods.push(data.index_dict_rev[idx].as_str());
		}
		let a_rep = reps[i];
		seen_elems.insert(a_rep);

		// delete all edges from `a`, and then add initial objects
		'outer: for &b_rep in &reps {
			if seen_elems.contains(&b_rep) { continue; }
			zeta_mat[(a_rep, b_rep)] = false;

			for &c_rep in &reps {
				if seen_elems.contains(&c_rep) { continue; }
				if zeta_mat[(c_rep, b_rep)] { continue 'outer; }
				
				initial_rep_indices.insert(c_rep);

			}

			
		}

	}
	while sorted_mods.len() < num_nodes {
		'outer: for (i, &a_rep) in reps.iter().enumerate() {
			// we're only dealing with a representative of each equivalence class.
			// this is because everything in `equivalence_classes[i]` will lie in the same cycle,
			// so they will all follow the exact same order rules.
			if seen_elems.contains(&a_rep) {
				continue;
			}

			// check if a is initial, if not, then bail
			for &b_rep in reps[.. i-1].iter().chain(&reps[i+1 ..]) {
				if zeta_mat[(b_rep, a_rep)] {
					continue 'outer;
				}
			}
			// delete all edges from `a`
			for &b_rep in reps[.. i-1].iter().chain(&reps[i+1 ..]) {
				zeta_mat[(a_rep, b_rep)] = false;
			}
			// mark `a` as seen.
			seen_elems.insert(a_rep);

			// add in all elements from this equivalence class
			for idx in &equivalence_classes[i] {
				sorted_mods.push(data.index_dict_rev[idx].as_str());
			}
			// sorted_equiv_classes.push(equivalence_classes[i].clone());
		}
	}

	sorted_mods


}

