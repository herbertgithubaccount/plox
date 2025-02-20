use std::{collections::HashSet, rc::Rc};

use log::debug;

use crate::sorter::GraphData;



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

/// Sorts graph data using topological sort, even if it contains cycles.
/// 
/// ...
/// 
/// At least, that's the goal. This is still a work in progress.
/// In particular, this function does not yet care about `NearStart` and `NearEnd` rules.
/// But this could be extended to handle those directly in one fell swoop. (I think.)
pub fn sort(data: &GraphData) -> Vec<&str> {

	let num_nodes = data.index_dict.len();
	let mut zeta = ZetaMatrix::new(num_nodes);
	
	let edges = data.edges.as_slice();

	for &e in edges {
		zeta[e] = true;
	}


	// Fill out the transitivity information for the matrix.
	// There is probably a way to do this without a quadruple `for` loop. Oh well!
	// Besides, we aren't doing any expensive computations in the loop so it's probably okay for now.
	// If the longest chain/cycle has length `m`, then this outer loop is guaranteed to run fewer than `m` times.
	// Since a bunch of transitivity information was already given in `data.edges`, it seems likely that this loop
	// will end up running fewer than 20 times.
	for _ in 1 ..= CMP_MAX_ITERS {
		let mut made_a_change = false;
		// iterate over all pairs
		for a in 0 .. num_nodes {
			for b in 0 .. num_nodes {
				if !zeta[(a,b)] { continue; }
				// past this point we know `a <= b`.

				for c in 0 .. num_nodes {
					// if `b <= c`, and if we haven't yet recorded that `a <= c`
					if zeta[(b,c)] && !zeta[(a,c)] {
						// add in the transitivity information for `a <= c`, and 
						// record that we've made a change.
						made_a_change = true;
						zeta[(a,c)] = true;
					}
				}
			}
		}
		// if we've gone through all triples and found no new information, we can exit the loop early.
		if !made_a_change {
			break;
		}
	}
	// Each equivalence class corresponds to a cycle in the graph.
	// From now on, we'll be operating on the graph of equivalences classes.
	// This graph will be acyclic, so we can do a topological sort on it.
	// Using Rc makes it easier to do checks using pointer equality
	let mut equivalence_classes: Vec<Rc<[usize]>> = Vec::with_capacity(num_nodes);
	// hashset to prevent us from adding the same element twice
	let mut seen_elems: HashSet<usize> = HashSet::new();

	for a in 0 .. num_nodes {
		// already added this node? then skip it
		if seen_elems.contains(&a) { 
			continue; 
		}
		// `cls` consists of at least `a`.
		let mut cls = vec![a];
		// for all b != a
		for b in (0.. a-1).chain(a+1 .. num_nodes) {
			// if a <= b and b <= a
			// i.e., if `a` and `b` lie in a cycle.
			if zeta[(a,b)] && zeta[(b,a)] {
				cls.push(b);
			}
		}
		// mark every item in this equivalence class as seen
		seen_elems.extend(&cls);
		equivalence_classes.push(Rc::from(cls));
	}

	// Now that we have identified and grouped all the cycles, we'll perform a topological sort 
	//		on the graph formed by the equivalence classes (i.e. cycles).
	// Notice that this is possible because the graph formed by the equivalences classes is guaranteed to be acyclic.
	// Ater topologically sorting the equivalence classes, we can expand out each equivalence class to obtain
	// 		an ordering on all the mods. The things within each equivalence class will be in a random order, 
	//		but they will all be sorted relative to all other cycles.


	// NOTE: We'll be performing the topological sort by identifying each equivalence class with its first element
	//		(i.e., the element at index `0`).
	// This means that we no longer care about any information stored the rows/columns of the zeta matrix that do not 
	//		correspond to the first element of some equivalence class.

	// if debugging, print out all the cycles.
	#[cfg(debug_assertions)]
	{
		debug!("Printing cycles...");
		for (i, cls) in equivalence_classes.iter().enumerate() {

			let cycle_mod_names: Vec<&str> = cls
				.iter()
				.map(|a| data.index_dict_rev[a].as_str())
				.collect();

			debug!("\t{i}: {cycle_mod_names:?}");
		}
	}


	// all of the initial equivalence classes
	// (recall that an element is "iniital" if there is no edge to that element.)
	let mut initial_classes = Vec::new();

	// initialize the initial representatives and kill the symmetry of zeta.
	// killing the symmetry of zeta means we dont have to do fancy index math to only compare unequal indices

	for a_cls in &equivalence_classes {
		let a_rep = a_cls[0];
		zeta[(a_rep, a_rep)] = false;
		// check if `a_cls` is initial, if not, then bail
		if equivalence_classes.iter().any(|b_cls| zeta[(b_cls[0], a_rep)]) {
			continue;
		}
		initial_classes.push(Rc::clone(&a_cls));
	}

	let mut sorted_mods = Vec::with_capacity(num_nodes);

	while let Some(a_cls) = initial_classes.pop() {
		// add all equivalent elements
		for a in a_cls.iter() {
			sorted_mods.push(data.index_dict_rev[a].as_str());
		}
		let a_rep = a_cls[0];

		// remove `a_cls` from the vector of all equivalence classes
		equivalence_classes.remove(
			equivalence_classes.iter()
				.position(|cls| *cls == a_cls)
				.expect("Error: {a_cls:?} was not present in equivalences classes while iterating.")
		);

		// delete all edges from `a`, and then add initial objects
		for b_cls in &equivalence_classes {
			let b_rep = b_cls[0];
			// if these equivalence classes aren't comparable, move on
			if !zeta[(a_rep, b_rep)] {
				continue;
			}
			zeta[(a_rep, b_rep)] = false;

			// if `b` is already an initial class, skip
			if initial_classes.contains(b_cls) {
				continue;
			}
			// check if `b_cls` is initial, if not, then bail
			if equivalence_classes.iter().any(|c_cls| zeta[(c_cls[0], b_rep)]) {
				continue;
			}
			initial_classes.push(Rc::clone(&b_cls));
		}

	}

	sorted_mods
}

