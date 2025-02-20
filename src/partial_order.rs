use std::{collections::{HashMap, HashSet}, rc::Rc};

use crate::rules::EOrderRule;



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


pub fn sort_order_rules(rules: &[EOrderRule]) -> Vec<Rc<str>> {
	// set of all distinct mod names
	let distinct_mod_names: HashSet<Rc<str>> = 
		rules.iter()
		.flat_map(|r| match r {
			EOrderRule::Order(order) => &order.names,
			EOrderRule::NearStart(near_start) =>  &near_start.names,
			EOrderRule::NearEnd(near_end) =>  &near_end.names,
		})
		.map(|s| Rc::from(s.to_lowercase()))
		.collect();

	// vector of all distinct mod names
	let mod_names: Box<[Rc<str>]> = distinct_mod_names.into_iter().collect();
	// map that gives the index given a mod name.
	// from now on, we will pretty much only interact with things by index, until we create the sorted 
	// vector at the very end
	let mut index_by_mod_name: HashMap<Rc<str>, usize> = HashMap::with_capacity(mod_names.len());

	for (i, s) in mod_names.iter().enumerate() {
		// let s = std::ptr::from_ref(s.as_ref())
		// let s: *const str = &**s;
		index_by_mod_name.insert(Rc::clone(s), i);
	}

	let mut zeta_mat =  ZetaMatrix::new(mod_names.len());
	


	for rule in rules.iter() {
		// TODO: make this sorting algorithm care about near start and near end rules.
		let names = match rule {
			EOrderRule::Order(order) => &order.names,
			EOrderRule::NearStart(near_start) =>  &near_start.names,
			EOrderRule::NearEnd(near_end) =>  &near_end.names,
		};
		// the indices of all mods in this `rule`
		let mut indices = Vec::with_capacity(names.len());
		for name in names {
			indices.push(*index_by_mod_name.get(name.as_str()).unwrap());
		}
		// all of this transitivity information would be added later on,
		// so we could skip the double for loop here and instead only add immediate successors,
		// but there is a lot more information density here, so doing the double `for` loop would result in
		// fewer iterations later on.
		for (i, &a) in indices.iter().enumerate() {
			for &b in &indices[(i+ 1)..] {
				zeta_mat[(a, b)] = true;
			}
		}
	}


	// fill out the transitivity information for the matrix
	// there is probably a way to do this without a quadruple `for` loop. oh well!
	// besides, we aren't doing any expensive computations in the loop so it's probably okay for now.
	// this outer loop should only run at most 15-20 times
	for _ in 0 .. CMP_MAX_ITERS {
		let mut made_a_change = false;
		// iterate over all pairs
		for a in 0 .. zeta_mat.n {
			for b in 0 .. zeta_mat.n {
				// the graph should be fairly sparse, so this should skip a lot of stuff
				if !zeta_mat[(a,b)] { continue; }

				for c in 0..zeta_mat.n {
					if zeta_mat[(b,c)] {
						if !zeta_mat[(a,c)] {
							made_a_change = true;
						}
						zeta_mat[(a,c)] = true;
					}
				}
			}
		}
		if !made_a_change {
			break;
		}
	}

	let n = zeta_mat.n;
	let mut equivalence_classes: Vec<Box<[usize]>> = Vec::with_capacity(n);
	// hashset to prevent us from adding the same element twice
	let mut seen_elems: HashSet<usize> = HashSet::new();
	for a in 0 .. n {
		if seen_elems.contains(&a) { 
			continue; 
		}
		let mut cls = vec![a];
		// seen_elems.insert(a);

		for b in (0.. a - 1).chain(a+1..n) {
			if zeta_mat[(a,b)] {
				// seen_elems.insert(b);
				cls.push(b);
			}
		}
		seen_elems.extend(&cls);
		equivalence_classes.push(cls.into_boxed_slice());

	}
	// let equivalence_classes = equivalence_classes.into_boxed_slice();

	// now, do a topological sort on the equivalence classes.
	// fml

	// reset the collection of seen elements so we can reuse it without canibalizing the order matrix.
	seen_elems = HashSet::new();

	let mut zeta_matrix_clone = zeta_mat.clone();
	
	// do a shittier topological sort since i didnt a non-transitive matrix.
	// runtime performance could probably be improved by also storing a non-transitive matrix.

	let mut sorted_mods = Vec::with_capacity(n);

	while sorted_mods.len() < zeta_mat.n {
		for i in 0 .. equivalence_classes.len() {
			// we're only dealing with a representative of each equivalence class.
			// this is because everything in `equivalence_classes[i]` will lie in the same cycle,
			// so they will all follow the exact same order rules.
			let a_rep = equivalence_classes[i][0];
			if seen_elems.contains(&a_rep) {
				continue;
			}

			// check if a is initial, if not, then bail
			let mut a_is_initial = true;
			for j in (0 ..  i-1).chain(i+1 .. equivalence_classes.len()) {
				let b_rep = equivalence_classes[j][0];
				if zeta_matrix_clone[(b_rep, a_rep)] {
					a_is_initial = false;
					break
				}
			}
			if !a_is_initial {
				continue;
			}
			for j in (0 ..  i-1).chain(i+1 .. equivalence_classes.len()) {
				let b_rep = equivalence_classes[j][0];
				zeta_matrix_clone[(a_rep, b_rep)] = false;
			}
			seen_elems.insert(a_rep);
			for idx in &equivalence_classes[i] {
				sorted_mods.push(Rc::clone(&mod_names[*idx]));
			}
			// sorted_equiv_classes.push(equivalence_classes[i].clone());
		}
	}

	sorted_mods


}

