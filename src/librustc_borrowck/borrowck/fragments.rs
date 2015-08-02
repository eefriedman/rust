// Copyright 2012-2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Helper routines used for fragmenting structural paths due to moves for
//! tracking drop obligations. Please see the extensive comments in the
//! section "Structural fragments" in `README.md`.

use borrowck::InteriorKind::{InteriorField, InteriorElement};
use borrowck::{self, LoanPath};
use borrowck::LoanPathKind::{LpVar, LpUpvar, LpDowncast, LpExtend};
use borrowck::LoanPathElem::{LpDeref, LpInterior};
use borrowck::move_data::InvalidMovePathIndex;
use borrowck::move_data::{MoveData, MovePathIndex};
use rustc::middle::ty;
use rustc::middle::ty::FragmentRepr;
use rustc::middle::mem_categorization as mc;
use rustc::util::nodemap::FnvHashMap;

use std::mem;
use std::rc::Rc;
use syntax::ast;
use syntax::attr::AttrMetaMethods;
use syntax::codemap::Span;

pub fn build_unfragmented_map(this: &mut borrowck::BorrowckCtxt,
                              move_data: &MoveData,
                              id: ast::NodeId) {
    let fr = &move_data.fragments.borrow();

    // For now, don't care about other kinds of fragments; the precise
    // classfication of all paths for non-zeroing *drop* needs them,
    // but the loose approximation used by non-zeroing moves does not.
    let moved_leaf_paths = &fr.moved_leaf_paths;
    let assigned_leaf_paths = &fr.assigned_leaf_paths;
    let parents_of_fragments = &fr.parents_of_fragments;
    let unmoved_fragments = &fr.unmoved_fragments;

    let mut fragment_map = FnvHashMap::<ast::NodeId, FragmentRepr>();

    fn find_var_id(move_data: &MoveData,
                   move_path_index: MovePathIndex,
                   id: ast::NodeId)
                   -> ast::NodeId {
        let mut lp = &*move_data.path_loan_path(move_path_index);
        loop {
            match lp.kind {
                LpVar(var_id) => return var_id,
                LpUpvar(ty::UpvarId { var_id, closure_expr_id }) => {
                    // The `var_id` is unique *relative to* the current function.
                    // (Check that we are indeed talking about the same function.)
                    assert_eq!(id, closure_expr_id);
                    return var_id
                }
                LpDowncast(ref sub_lp, _) | LpExtend(ref sub_lp, _, _) => {
                    lp = sub_lp;
                }
            }
        }
    }

    let paths = moved_leaf_paths.iter()
                .chain(assigned_leaf_paths.iter())
                .chain(unmoved_fragments.iter());

    for &move_path_index in paths {
        let var_id = find_var_id(move_data, move_path_index, id);
        let mut lp = &*move_data.path_loan_path(move_path_index);
        let mut entry = fragment_map.entry(var_id).or_insert(FragmentRepr::Whole);
        loop {
            match lp.kind {
                LpVar(_) | LpUpvar(_) => break,
                LpDowncast(ref sub_lp, variant_def_id) => {
                    if let FragmentRepr::Whole = *entry {
                        let discrs = Vec::new();
                        *entry = FragmentRepr::Enum(discrs);
                    }
                    let mut discrs = if let FragmentRepr::Enum(ref mut discrs) = *entry {
                        discrs
                    } else {
                        this.tcx.sess.bug("Inconsistent FragmentRepr");
                    };
                    entry = &mut discrs.iter_mut().find(|e| e.0 == variant_def_id).unwrap().1;
                    lp = sub_lp;
                }
                LpExtend(ref sub_lp, _, LpDeref(_)) => {
                    if let FragmentRepr::Whole = *entry {
                        *entry = FragmentRepr::Boxed(Box::new((FragmentRepr::Whole)));
                    }
                    entry = if let FragmentRepr::Boxed(ref mut contents) = *entry {
                        contents
                    } else {
                        this.tcx.sess.bug("Inconsistent FragmentRepr");
                    };
                    lp = sub_lp;
                }
                LpExtend(ref sub_lp, _, LpInterior(InteriorField(f))) => {
                    if let FragmentRepr::Whole = *entry {
                        let fields = Vec::new();
                        *entry = FragmentRepr::Fields(fields);
                    }
                    let mut fields = if let FragmentRepr::Fields(ref mut fields) = *entry {
                        fields
                    } else {
                        this.tcx.sess.bug("Inconsistent FragmentRepr");
                    };
                    let f_pos = match f {
                        mc::NamedField(n) => {
                            let did;
                            let fields = this.tcx.lookup_struct_fields(did);
                            fields.iter().position(|f| f.name == n).unwrap()
                        },
                        mc::PositionalField(n) => n,
                    };
                    entry = &mut fields[f_pos];
                    lp = sub_lp;
                }
                LpExtend(_, _, LpInterior(InteriorElement(_))) => {
                    this.tcx.sess.bug("Unexpected loan path");
                }
            }
        }
    }

    let mut fragment_infos = Vec::with_capacity(moved_leaf_paths.len());

    let mut fraginfo_map = this.tcx.fragment_infos.borrow_mut();
    let fn_did = ast::DefId { krate: ast::LOCAL_CRATE, node: id };
    let prev = fraginfo_map.insert(fn_did, fragment_infos);
    assert!(prev.is_none());
}

pub struct FragmentSets {
    /// During move_data construction, `moved_leaf_paths` tracks paths
    /// that have been used directly by being moved out of.  When
    /// move_data construction has been completed, `moved_leaf_paths`
    /// tracks such paths that are *leaf fragments* (e.g. `a.j` if we
    /// never move out any child like `a.j.x`); any parent paths
    /// (e.g. `a` for the `a.j` example) are moved over to
    /// `parents_of_fragments`.
    moved_leaf_paths: Vec<MovePathIndex>,

    /// `assigned_leaf_paths` tracks paths that have been used
    /// directly by being overwritten, but is otherwise much like
    /// `moved_leaf_paths`.
    assigned_leaf_paths: Vec<MovePathIndex>,

    /// `parents_of_fragments` tracks paths that are definitely
    /// parents of paths that have been moved.
    ///
    /// FIXME(pnkfelix) probably do not want/need
    /// `parents_of_fragments` at all, if we can avoid it.
    ///
    /// Update: I do not see a way to to avoid it.  Maybe just remove
    /// above fixme, or at least document why doing this may be hard.
    parents_of_fragments: Vec<MovePathIndex>,

    /// During move_data construction (specifically the
    /// fixup_fragment_sets call), `unmoved_fragments` tracks paths
    /// that have been "left behind" after a sibling has been moved or
    /// assigned.  When move_data construction has been completed,
    /// `unmoved_fragments` tracks paths that were *only* results of
    /// being left-behind, and never directly moved themselves.
    unmoved_fragments: Vec<MovePathIndex>,
}

impl FragmentSets {
    pub fn new() -> FragmentSets {
        FragmentSets {
            unmoved_fragments: Vec::new(),
            moved_leaf_paths: Vec::new(),
            assigned_leaf_paths: Vec::new(),
            parents_of_fragments: Vec::new(),
        }
    }

    pub fn moved_leaf_paths(&self) -> &[MovePathIndex] {
        &self.moved_leaf_paths
    }

    pub fn assigned_leaf_paths(&self) -> &[MovePathIndex] {
        &self.assigned_leaf_paths
    }

    pub fn add_move(&mut self, path_index: MovePathIndex) {
        self.moved_leaf_paths.push(path_index);
    }

    pub fn add_assignment(&mut self, path_index: MovePathIndex) {
        self.assigned_leaf_paths.push(path_index);
    }
}

pub fn instrument_move_fragments<'tcx>(this: &MoveData<'tcx>,
                                       tcx: &ty::ctxt<'tcx>,
                                       sp: Span,
                                       id: ast::NodeId) {
    let span_err = tcx.map.attrs(id).iter()
                          .any(|a| a.check_name("rustc_move_fragments"));
    let print = tcx.sess.opts.debugging_opts.print_move_fragments;

    if !span_err && !print { return; }

    let instrument_all_paths = |kind, vec_rc: &Vec<MovePathIndex>| {
        for (i, mpi) in vec_rc.iter().enumerate() {
            let lp = || this.path_loan_path(*mpi);
            if span_err {
                tcx.sess.span_err(sp, &format!("{}: `{}`", kind, lp()));
            }
            if print {
                println!("id:{} {}[{}] `{}`", id, kind, i, lp());
            }
        }
    };

    let instrument_all_fragments = |kind, vec_rc: &Vec<MovePathIndex>| {
        for (i, mpi) in vec_rc.iter().enumerate() {
            let render = || this.path_loan_path(*mpi);
            if span_err {
                tcx.sess.span_err(sp, &format!("{}: `{}`", kind, render()));
            }
            if print {
                println!("id:{} {}[{}] `{}`", id, kind, i, render());
            }
        }
    };

    let fragments = this.fragments.borrow();
    instrument_all_paths("moved_leaf_path", &fragments.moved_leaf_paths);
    instrument_all_fragments("unmoved_fragment", &fragments.unmoved_fragments);
    instrument_all_paths("parent_of_fragments", &fragments.parents_of_fragments);
    instrument_all_paths("assigned_leaf_path", &fragments.assigned_leaf_paths);
}

/// Normalizes the fragment sets in `this`; i.e., removes duplicate entries, constructs the set of
/// parents, and constructs the left-over fragments.
///
/// Note: "left-over fragments" means paths that were not directly referenced in moves nor
/// assignments, but must nonetheless be tracked as potential drop obligations.
pub fn fixup_fragment_sets<'tcx>(this: &MoveData<'tcx>, tcx: &ty::ctxt<'tcx>) {

    let mut fragments = this.fragments.borrow_mut();

    // Swap out contents of fragments so that we can modify the fields
    // without borrowing the common fragments.
    let mut unmoved = mem::replace(&mut fragments.unmoved_fragments, vec![]);
    let mut parents = mem::replace(&mut fragments.parents_of_fragments, vec![]);
    let mut moved = mem::replace(&mut fragments.moved_leaf_paths, vec![]);
    let mut assigned = mem::replace(&mut fragments.assigned_leaf_paths, vec![]);

    let path_lps = |mpis: &[MovePathIndex]| -> Vec<String> {
        mpis.iter().map(|mpi| format!("{:?}", this.path_loan_path(*mpi))).collect()
    };

    // First, filter out duplicates
    moved.sort();
    moved.dedup();
    debug!("fragments 1 moved: {:?}", path_lps(&moved[..]));

    assigned.sort();
    assigned.dedup();
    debug!("fragments 1 assigned: {:?}", path_lps(&assigned[..]));

    // Second, build parents from the moved and assigned.
    for m in &moved {
        let mut p = this.path_parent(*m);
        while p != InvalidMovePathIndex {
            parents.push(p);
            p = this.path_parent(p);
        }
    }
    for a in &assigned {
        let mut p = this.path_parent(*a);
        while p != InvalidMovePathIndex {
            parents.push(p);
            p = this.path_parent(p);
        }
    }

    parents.sort();
    parents.dedup();
    debug!("fragments 2 parents: {:?}", path_lps(&parents[..]));

    // Third, filter the moved and assigned fragments down to just the non-parents
    moved.retain(|f| non_member(*f, &parents[..]));
    debug!("fragments 3 moved: {:?}", path_lps(&moved[..]));

    assigned.retain(|f| non_member(*f, &parents[..]));
    debug!("fragments 3 assigned: {:?}", path_lps(&assigned[..]));

    // Fourth, build the leftover from the moved, assigned, and parents.
    for m in &moved {
        let lp = this.path_loan_path(*m);
        add_fragment_siblings(this, tcx, &mut unmoved, lp, None);
    }
    for a in &assigned {
        let lp = this.path_loan_path(*a);
        add_fragment_siblings(this, tcx, &mut unmoved, lp, None);
    }
    for p in &parents {
        let lp = this.path_loan_path(*p);
        add_fragment_siblings(this, tcx, &mut unmoved, lp, None);
    }

    unmoved.sort();
    unmoved.dedup();
    debug!("fragments 4 unmoved: {:?}", path_lps(&unmoved[..]));

    // Fifth, filter the leftover fragments down to its core.
    unmoved.retain(|&mpi| non_member(mpi, &parents[..]) &&
            non_member(mpi, &moved[..]) &&
            non_member(mpi, &assigned[..])
    );
    debug!("fragments 5 unmoved: {:?}", path_lps(&unmoved[..]));

    // Swap contents back in.
    fragments.unmoved_fragments = unmoved;
    fragments.parents_of_fragments = parents;
    fragments.moved_leaf_paths = moved;
    fragments.assigned_leaf_paths = assigned;

    return;

    fn non_member(elem: MovePathIndex, set: &[MovePathIndex]) -> bool {
        match set.binary_search(&elem) {
            Ok(_) => false,
            Err(_) => true,
        }
    }
}

/// Adds all of the precisely-tracked siblings of `lp` as potential move paths of interest. For
/// example, if `lp` represents `s.x.j`, then adds moves paths for `s.x.i` and `s.x.k`, the
/// siblings of `s.x.j`.
fn add_fragment_siblings<'tcx>(this: &MoveData<'tcx>,
                               tcx: &ty::ctxt<'tcx>,
                               gathered_fragments: &mut Vec<MovePathIndex>,
                               lp: Rc<LoanPath<'tcx>>,
                               origin_id: Option<ast::NodeId>) {
    match lp.kind {
        LpVar(_) | LpUpvar(..) => {} // Local variables have no siblings.

        // Consuming a downcast is like consuming the original value, so propage inward.
        LpDowncast(ref loan_parent, _) => {
            add_fragment_siblings(this, tcx, gathered_fragments, loan_parent.clone(), origin_id);
        }

        // *LV for Unique consumes the contents of the box (at
        // least when it is non-copy...), so propagate inward.
        LpExtend(ref loan_parent, _, LpDeref(mc::Unique)) => {
            add_fragment_siblings(this, tcx, gathered_fragments, loan_parent.clone(), origin_id);
        }

        // *LV for unsafe and borrowed pointers do not consume their loan path, so stop here.
        LpExtend(_, _, LpDeref(mc::UnsafePtr(..)))   |
        LpExtend(_, _, LpDeref(mc::Implicit(..)))    |
        LpExtend(_, _, LpDeref(mc::BorrowedPtr(..))) => {}

        LpExtend(_, _, LpInterior(InteriorElement(..))) => {
            // It's impossible to actually move out of an array at the moment.
            panic!("Unexpected loan path");
        }

        // field access LV.x and tuple access LV#k are the cases
        // we are interested in
        LpExtend(ref loan_parent, mc,
                 LpInterior(InteriorField(ref field_name))) => {
            let enum_variant_info = match loan_parent.kind {
                LpDowncast(ref loan_parent_2, variant_def_id) =>
                    Some((variant_def_id, loan_parent_2.clone())),
                LpExtend(..) | LpVar(..) | LpUpvar(..) =>
                    None,
            };
            add_fragment_siblings_for_extension(
                this,
                tcx,
                gathered_fragments,
                loan_parent, mc, field_name, &lp, origin_id, enum_variant_info);
        }
    }
}

/// We have determined that `origin_lp` destructures to LpExtend(parent, original_field_name).
/// Based on this, add move paths for all of the siblings of `origin_lp`.
fn add_fragment_siblings_for_extension<'tcx>(this: &MoveData<'tcx>,
                                             tcx: &ty::ctxt<'tcx>,
                                             gathered_fragments: &mut Vec<MovePathIndex>,
                                             parent_lp: &Rc<LoanPath<'tcx>>,
                                             mc: mc::MutabilityCategory,
                                             origin_field_name: &mc::FieldName,
                                             origin_lp: &Rc<LoanPath<'tcx>>,
                                             origin_id: Option<ast::NodeId>,
                                             enum_variant_info: Option<(ast::DefId,
                                                                        Rc<LoanPath<'tcx>>)>) {
    let parent_ty = parent_lp.to_type();

    let mut add_fragment_sibling_local = |field_name, variant_did| {
        add_fragment_sibling_core(
            this, tcx, gathered_fragments, parent_lp.clone(), mc, field_name, origin_lp,
            variant_did);
    };

    match (&parent_ty.sty, enum_variant_info) {
        (&ty::TyTuple(ref v), None) => {
            let tuple_idx = match *origin_field_name {
                mc::PositionalField(tuple_idx) => tuple_idx,
                mc::NamedField(_) =>
                    panic!("tuple type {:?} should not have named fields.",
                           parent_ty),
            };
            let tuple_len = v.len();
            for i in 0..tuple_len {
                if i == tuple_idx { continue }
                let field_name = mc::PositionalField(i);
                add_fragment_sibling_local(field_name, None);
            }
        }

        (&ty::TyStruct(def_id, ref _substs), None) => {
            let fields = tcx.lookup_struct_fields(def_id);
            match *origin_field_name {
                mc::NamedField(ast_name) => {
                    for f in &fields {
                        if f.name == ast_name {
                            continue;
                        }
                        let field_name = mc::NamedField(f.name);
                        add_fragment_sibling_local(field_name, None);
                    }
                }
                mc::PositionalField(tuple_idx) => {
                    for (i, _f) in fields.iter().enumerate() {
                        if i == tuple_idx {
                            continue
                        }
                        let field_name = mc::PositionalField(i);
                        add_fragment_sibling_local(field_name, None);
                    }
                }
            }
        }

        (&ty::TyEnum(enum_def_id, substs), ref enum_variant_info) => {
            let variant_info = {
                let mut variants = tcx.substd_enum_variants(enum_def_id, substs);
                match *enum_variant_info {
                    Some((variant_def_id, ref _lp2)) =>
                        variants.iter()
                        .find(|variant| variant.id == variant_def_id)
                        .expect("enum_variant_with_id(): no variant exists with that ID")
                        .clone(),
                    None => {
                        assert_eq!(variants.len(), 1);
                        variants.pop().unwrap()
                    }
                }
            };
            match *origin_field_name {
                mc::NamedField(ast_name) => {
                    let variant_arg_names = variant_info.arg_names.as_ref().unwrap();
                    for &variant_arg_name in variant_arg_names {
                        if variant_arg_name == ast_name {
                            continue;
                        }
                        let field_name = mc::NamedField(variant_arg_name);
                        add_fragment_sibling_local(field_name, Some(variant_info.id));
                    }
                }
                mc::PositionalField(tuple_idx) => {
                    let variant_arg_types = &variant_info.args;
                    for (i, _variant_arg_ty) in variant_arg_types.iter().enumerate() {
                        if tuple_idx == i {
                            continue;
                        }
                        let field_name = mc::PositionalField(i);
                        add_fragment_sibling_local(field_name, None);
                    }
                }
            }
        }

        ref sty_and_variant_info => {
            let msg = format!("type {:?} ({:?}) is not fragmentable",
                              parent_ty, sty_and_variant_info);
            let opt_span = origin_id.and_then(|id|tcx.map.opt_span(id));
            tcx.sess.opt_span_bug(opt_span, &msg[..])
        }
    }
}

/// Adds the single sibling `LpExtend(parent, new_field_name)` of `origin_lp` (the original
/// loan-path).
fn add_fragment_sibling_core<'tcx>(this: &MoveData<'tcx>,
                                   tcx: &ty::ctxt<'tcx>,
                                   gathered_fragments: &mut Vec<MovePathIndex>,
                                   parent: Rc<LoanPath<'tcx>>,
                                   mc: mc::MutabilityCategory,
                                   new_field_name: mc::FieldName,
                                   origin_lp: &Rc<LoanPath<'tcx>>,
                                   enum_variant_did: Option<ast::DefId>) -> MovePathIndex {
    let opt_variant_did = match parent.kind {
        LpDowncast(_, variant_did) => Some(variant_did),
        LpVar(..) | LpUpvar(..) | LpExtend(..) => enum_variant_did,
    };

    let loan_path_elem = LpInterior(InteriorField(new_field_name));
    let new_lp_type = match new_field_name {
        mc::NamedField(ast_name) =>
            tcx.named_element_ty(parent.to_type(), ast_name, opt_variant_did),
        mc::PositionalField(idx) =>
            tcx.positional_element_ty(parent.to_type(), idx, opt_variant_did),
    };
    let new_lp_variant = LpExtend(parent, mc, loan_path_elem);
    let new_lp = LoanPath::new(new_lp_variant, new_lp_type.unwrap());
    debug!("add_fragment_sibling_core(new_lp={:?}, origin_lp={:?})",
           new_lp, origin_lp);
    let mp = this.move_path(tcx, Rc::new(new_lp));

    // Do not worry about checking for duplicates here; we will sort
    // and dedup after all are added.
    gathered_fragments.push(mp);

    mp
}
