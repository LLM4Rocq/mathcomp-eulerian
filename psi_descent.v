(* psi_descent.v — compatibility wrapper.                                    *)
(*                                                                            *)
(* The original monolithic descent-effect development was replaced by the     *)
(* verified split files below.  Keep this module as a stable import name for  *)
(* older scripts that still use [Require Import psi_descent].                 *)

From mathcomp Require Import all_ssreflect.
Require Export psi_descent_v2 psi_descent_thms.
