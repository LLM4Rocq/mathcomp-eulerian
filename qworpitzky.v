(* Carlitz's q-analogue of Worpitzky's identity (Stanley EC1 §1.4):          *)
(*                                                                            *)
(*    ([m+1]_q)^(n+1) = \sum_(k <= n) B(n,k) [m + n + 1 - k, n + 1]_q         *)
(*                                                                            *)
(* where B(n,k) = q_eulerian n k (qeul_rec.v) and [t, N]_q = qbin t N is the  *)
(* Gaussian binomial (qbin.v).  Mirrors worpitzky.v: induction on n from the  *)
(* q-Eulerian recurrence [q_eulerian_rec], via a q-Pascal-style splitting of  *)
(* [m+1]_q * qbin (m+N-k) N  [q_bin_step].  The splitting rests on the        *)
(* complementary absorption identity [qbin_absorbC]:                          *)
(*                                                                            *)
(*    [k+1]_q [n, k+1]_q = [n-k]_q [n, k]_q.                                  *)
(*                                                                            *)
(* Also provides [coef_q_eul_pol]: the coefficients of the q-Eulerian         *)
(* polynomial q_eul_pol (qeul.v) are the q-Eulerian numbers.                  *)
(*                                                                            *)
(* This file is AXIOM-FREE (part of the combinatorial core).  The             *)
(* generating-function form (Carlitz's q-analogue of Stanley §1.4) lives in   *)
(* carlitz.v, on top of mathcomp_fps.                                         *)

From mathcomp Require Import all_ssreflect all_algebra fingroup perm.
From mathcomp_eulerian Require Import ordinal_reindex perm_compress descent.
From mathcomp_eulerian Require Import eulerian reflection inversions.
From mathcomp_eulerian Require Import qfact qeul qbin qeul_rec.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(* ========================================================================= *)
(* q-integer and Gaussian-binomial calculus                                   *)
(* ========================================================================= *)

(** Splitting a q-integer: [a+b] = [a] + q^a [b]. *)
Lemma q_intD (a b : nat) : q_int (a + b)%N = q_int a + 'X^a * q_int b.
Proof.
rewrite /q_int big_split_ord /=; congr (_ + _).
rewrite big_distrr /=; apply: eq_bigr => i _.
by rewrite -exprD.
Qed.

Lemma qbin_n1 n : qbin n 1 = q_int n.
Proof.
elim: n => [|n IHn]; first by rewrite qbin_0S /q_int big_ord0.
by rewrite qbinS qbin_n0 IHn expr1 q_intS.
Qed.

(** Complementary absorption: [k+1] [n, k+1] = [n-k] [n, k]. *)
Lemma qbin_absorbC n k :
  q_int k.+1 * qbin n k.+1 = q_int (n - k)%N * qbin n k.
Proof.
elim: n k => [|n IHn] k.
  by rewrite qbin_0S mulr0 sub0n /q_int big_ord0 mul0r.
case: k => [|k].
  by rewrite subn0 qbin_n0 mulr1 qbin_n1 /q_int big_ord1 expr0 mul1r.
case: (leqP n k) => [le_nk | lt_kn].
  rewrite (qbin_small (_ : (n.+1 < k.+2)%N)) ?ltnS //.
  rewrite (_ : (n.+1 - k.+1)%N = 0%N) ?mulr0; last first.
    by apply/eqP; rewrite subn_eq0 ltnS.
  by rewrite /q_int big_ord0 mul0r.
rewrite subSS qbinS [in RHS]qbinS !mulrDr.
rewrite mulrCA IHn.
rewrite -[in RHS]IHn.
rewrite !mulrA -!mulrDl; congr (_ * _).
rewrite -q_intD [in RHS]mulrC -q_intD.
congr q_int.
have -> : (k.+2 + (n - k.+1))%N = n.+1 by rewrite addSn subnKC.
by rewrite addSn subnKC // ltnW.
Qed.

(** [m+1] qbin (m+N-k) N = [k+1] qbin (m+N-k+1) N+1                          *)
(*                          + q^(k+1) [N-k] qbin (m+N-k) N+1:                 *)
(* the engine of the inductive step (both sides vanish when m < k).          *)
Lemma q_bin_step (N k m : nat) : (k <= N)%N ->
  q_int m.+1 * qbin (m + N - k)%N N
  = q_int k.+1 * qbin (m + N - k).+1 N.+1
    + 'X^(k.+1) * (q_int (N - k)%N * qbin (m + N - k)%N N.+1).
Proof.
move=> le_kN; set t := (m + N - k)%N.
case: (leqP k m) => [le_km | lt_mk]; last first.
  have lt_tN : (t < N)%N.
    by rewrite /t ltn_subLR ?(leq_trans le_kN) ?leq_addl // ltn_add2r.
  rewrite !qbin_small ?ltnS ?(ltnW lt_tN) ?(ltn_trans lt_tN (ltnSn N)) //.
  by rewrite !mulr0 addr0.
have tNE : (t - N)%N = (m - k)%N.
  by rewrite /t addnC -subnDA addnC subnDr.
rewrite qbinS mulrDr -addrA.
rewrite [q_int k.+1 * ('X^(N.+1) * _)]mulrCA.
rewrite ['X^(N.+1) * (q_int k.+1 * _)]mulrA
        ['X^(k.+1) * (q_int (N - k)%N * _)]mulrA.
rewrite -mulrDl.
have coefE : 'X^(N.+1) * q_int k.+1 + 'X^(k.+1) * q_int (N - k)%N
           = 'X^(k.+1) * q_int N.+1.
  rewrite (_ : N.+1 = ((N - k) + k.+1)%N); last by rewrite addnS subnK.
  rewrite q_intD mulrDr mulrA -exprD.
  by rewrite addrC [(N - k + k.+1)%N]addnC.
rewrite coefE -mulrA qbin_absorbC tNE.
rewrite (_ : m.+1 = (k.+1 + (m - k))%N); last by rewrite addSn subnKC.
by rewrite q_intD mulrDl mulrA.
Qed.

(* ========================================================================= *)
(* The q-Worpitzky identity                                                   *)
(* ========================================================================= *)

(** Carlitz: every power of a q-integer is a positive combination of          *)
(* Gaussian binomials weighted by the q-Eulerian numbers.                     *)
Theorem q_worpitzky (n m : nat) :
  q_int m.+1 ^+ n.+1
  = \sum_(k < n.+1) q_eulerian n k * qbin (m + n.+1 - k)%N n.+1.
Proof.
elim: n => [|n IHn].
  by rewrite big_ord1 q_eulerian_n_0 mul1r expr1 subn0 addn1 qbin_n1.
rewrite exprS IHn big_distrr /=.
under eq_bigr => k _ do
  rewrite mulrCA (q_bin_step _ (ltnW (ltn_ord k))) mulrDr.
rewrite big_split /=.
rewrite [in RHS]big_ord_recl /= q_eulerian_n_0 mul1r subn0.
under [in RHS]eq_bigr => j _ do rewrite q_eulerian_rec mulrDl.
rewrite big_split /=.
under [X in _ = _ + (X + _)]eq_bigr => i _ do
  rewrite /bump /= add1n addnS subSS -mulrA mulrCA.
under [X in _ = _ + (_ + X)]eq_bigr => i _ do
  rewrite /bump /= add1n addnS subSS -mulrA mulrCA.
rewrite addrA; congr (_ + _).
  rewrite big_ord_recl /= q_eulerian_n_0 subn0 mul1r.
  rewrite (_ : q_int 1 = 1) ?mul1r; last by rewrite /q_int big_ord1.
  rewrite [in RHS]addnS [in RHS]big_ord_recr /=.
  rewrite (q_eulerian_out_of_range (ltnSn n)) mul0r addr0.
  congr (_ + _).
  apply: eq_bigr => i _.
  rewrite /bump /= add1n !addnS subSS.
  by rewrite (subSn (ltnW (leq_trans (ltn_ord i) (leq_addl m n)))).
apply: eq_bigr => i _.
by rewrite ['X^(i.+1) * (q_int _ * _)]mulrCA mulrA
           [q_int _ * q_eulerian n i]mulrC.
Qed.

(* ========================================================================= *)
(* Coefficients of the q-Eulerian polynomial                                  *)
(* ========================================================================= *)

(** The coefficients of q_eul_pol n (qeul.v) are the q-Eulerian numbers —     *)
(* at every index, using q_eulerian_out_of_range beyond degree n.             *)
Lemma coef_q_eul_pol n k : (q_eul_pol n)`_k = q_eulerian n k.
Proof.
rewrite /q_eul_pol coef_sum /q_eulerian.
rewrite (bigID (fun s : {perm 'I_n.+1} => des s == k)) /=.
rewrite [X in _ + X]big1 ?addr0; last first.
  by move=> s /negbTE Hs; rewrite coefCM coefXn eq_sym Hs mulr0.
apply: eq_bigr => s /eqP Hs.
by rewrite coefCM coefXn Hs eqxx mulr1.
Qed.
