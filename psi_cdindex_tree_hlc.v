(* psi_cdindex_tree_hlc.v — Backwards-compatibility re-export.               *)
(*                                                                            *)
(* Original heavy proofs (has_left_child_order_iso, behead_rank_shift_…,     *)
(* has_left_child_psi) were superseded by the tree-shape refactor and now    *)
(* live in psi_cdindex_tree_shape.v.  This file is kept only so that the     *)
(* existing import sites in psi_cdindex_tree.v / psi_cdindex_core.v continue *)
(* to resolve.                                                                *)

From mathcomp Require Import all_ssreflect.
Require Export psi_cdindex_tree_shape.
