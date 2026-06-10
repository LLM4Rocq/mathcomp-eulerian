(* Worpitzky's identity (Stanley EC1 §1.4):                                  *)
(*                                                                            *)
(*    (m+1)^(n+1) = \sum_(k <= n) A(n,k) * 'C(m + n + 1 - k, n + 1)           *)
(*                                                                            *)
(* where A(n,k) = eulerian n k counts the permutations of n+1 letters with    *)
(* k descents.  Proved by induction on n from the Eulerian recurrence         *)
(* [eulerian_rec] (eulerian.v), via a Pascal-style splitting of               *)
(* (m+1) * 'C(m+n+1-k, n+1)  [worpitzky_bin_step].                            *)
(*                                                                            *)
(* Also provides [coef_eul_pol]: the coefficients of the Eulerian polynomial  *)
(* eul_pol (qeul.v) are the Eulerian numbers, at every index.                 *)
(*                                                                            *)
(* This file is AXIOM-FREE (part of the combinatorial core).  The             *)
(* generating-function form (Stanley's \sum_m (m+1)^n x^m =                   *)
(* A_n(x)/(1-x)^(n+1)) lives in stanley_ogf.v, on top of mathcomp_fps.        *)

From mathcomp Require Import all_ssreflect all_algebra fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress descent.
From mathcomp_eulerian Require Import eulerian qfact qeul.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.

(* ========================================================================= *)
(* The binomial splitting step                                               *)
(* ========================================================================= *)

(** (m+1) C(m+N-k, N) = (k+1) C(m+N+1-k, N+1) + (N-k) C(m+N-k, N+1):          *)
(* the engine of the inductive step (both sides vanish when m < k).           *)
Lemma worpitzky_bin_step (N k m : nat) : (k <= N)%N ->
  (m.+1 * 'C(m + N - k, N)
   = k.+1 * 'C((m + N - k).+1, N.+1) + (N - k) * 'C(m + N - k, N.+1))%N.
Proof.
move=> le_kN; set t := (m + N - k)%N.
case: (leqP k m) => [le_km | lt_mk]; last first.
  have lt_tN : (t < N)%N.
    by rewrite /t ltn_subLR ?(leq_trans le_kN) ?leq_addl // ltn_add2r.
  rewrite !bin_small ?muln0 //; last by rewrite ltnS ltnW.
rewrite binS mulnDr addnAC -mulnDl.
have -> : (k.+1 + (N - k))%N = N.+1 by rewrite addSn subnKC.
rewrite mul_bin_left -mulnDl; congr (_ * _)%N.
have -> : (t - N)%N = (m - k)%N.
  by rewrite /t addnC -subnDA addnC subnDr.
by rewrite addnS subnK.
Qed.

(* ========================================================================= *)
(* Worpitzky's identity                                                      *)
(* ========================================================================= *)

(** Stanley EC1 §1.4: every power (m+1)^(n+1) is a positive combination of    *)
(* binomial coefficients weighted by the Eulerian numbers.                    *)
Theorem worpitzky (n m : nat) :
  ((m.+1) ^ n.+1
   = \sum_(k < n.+1) eulerian n k * 'C(m + n.+1 - k, n.+1))%N.
Proof.
elim: n => [|n IHn].
  by rewrite big_ord1 eulerian_n_0 mul1n expn1 subn0 addn1 bin1.
rewrite expnS IHn big_distrr /=.
under eq_bigr => k _ do
  rewrite mulnCA (worpitzky_bin_step _ (ltnW (ltn_ord k))) mulnDr.
rewrite big_split /=.
rewrite [in RHS]big_ord_recl /= eulerian_n_0 mul1n subn0.
under [in RHS]eq_bigr => j _ do rewrite eulerian_rec mulnDl.
rewrite big_split /=.
under [X in (_ = _ + (X + _))%N]eq_bigr => i _ do
  rewrite /bump /= add1n addnS subSS -mulnA mulnCA.
under [X in (_ = _ + (_ + X))%N]eq_bigr => i _ do
  rewrite /bump /= add1n addnS subSS -mulnA mulnCA.
rewrite addnA; congr (_ + _)%N.
rewrite big_ord_recl /= eulerian_n_0 subn0 !mul1n -addnS.
rewrite [in RHS]big_ord_recr /=.
rewrite (eulerian_out_of_range (ltnSn n)) mul0n addn0.
congr (_ + _)%N.
under eq_bigr => i _ do
  rewrite /bump /= add1n
          -(subSn (leq_trans (ltn_ord i)
                     (leq_trans (leqnSn n) (leq_addl m n.+1))))
          subSS.
by [].
Qed.

(* ========================================================================= *)
(* Coefficients of the Eulerian polynomial                                   *)
(* ========================================================================= *)

(** The coefficients of eul_pol n (qeul.v) are the Eulerian numbers — at      *)
(* every index, using eulerian_out_of_range beyond degree n.                  *)
Lemma coef_eul_pol n k : (eul_pol n)`_k = (eulerian n k)%:R :> int.
Proof.
rewrite /eul_pol coef_sum.
under eq_bigr => j _ do rewrite -polyC_natr coefCM coefXn.
case: (ltnP k n.+1) => [lt_kn | lt_nk].
  rewrite (bigD1 (Ordinal lt_kn)) //= eqxx mulr1 big1 ?addr0 //.
  move=> j neq_jk.
  by move: neq_jk; rewrite -val_eqE /= eq_sym => /negbTE ->; rewrite mulr0.
rewrite eulerian_out_of_range // big1 // => j _.
have -> : (k == j :> nat) = false.
  by apply/negbTE; rewrite neq_ltn (leq_trans (ltn_ord j) lt_nk) orbT.
by rewrite mulr0.
Qed.
