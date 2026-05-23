(******************************************************************************)
(*                                                                            *)
(*     Adaptive Romberg integration (item 10)                                 *)
(*                                                                            *)
(*     Implements the Richardson-extrapolation tableau for refining the       *)
(*     composite trapezoidal rule. The tableau is the recursion               *)
(*                                                                            *)
(*       R(n, 0) = composite trapezoidal with 2^n subintervals                *)
(*       R(n, k) = (4^k * R(n, k-1) - R(n-1, k-1)) / (4^k - 1)                *)
(*                                                                            *)
(*     and `romberg f a b k := R(k, k)`.                                      *)
(*                                                                            *)
(*     The Richardson cancellation kills successive Taylor terms in the       *)
(*     trapezoidal error, giving improved convergence rate                    *)
(*     `R(k, k) - RInt f a b = O(h^{2k+2})` for f in C^{2k+2}.                *)
(*                                                                            *)
(*     This file establishes the algorithm definitionally and proves the      *)
(*     fundamental algebraic identities (exactness on constants, exactness    *)
(*     of level 0 against the trapezoidal sum). The full O(h^{2k+2})          *)
(*     convergence rate requires Taylor-with-remainder of the trapezoidal    *)
(*     error formula plus Richardson cancellation arithmetic, both of        *)
(*     which are substantial standalone proofs and are left as future        *)
(*     refinement.                                                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra ZArith Lia.
From Coquelicot Require Import Coquelicot.

Open Scope R_scope.

(* ================================================================== *)
(* === Composite trapezoidal rule with 2^n subintervals === *)
(* ================================================================== *)

(* Sum of f at the interior abscissas a + i*h for i = 1, ..., m - 1. *)
Fixpoint interior_sum (f : R -> R) (a h : R) (m : nat) : R :=
  match m with
  | 0 => 0
  | 1 => 0
  | S k => f (a + INR k * h) + interior_sum f a h k
  end.

(* Composite trapezoidal rule with m subintervals of width h. *)
Definition trap_composite (f : R -> R) (a b : R) (m : nat) : R :=
  let h := (b - a) / INR m in
  h * ((f a + f b) / 2 + interior_sum f a h m).

(* Composite trapezoidal with 2^n subintervals. *)
Definition trap_pow2 (f : R -> R) (a b : R) (n : nat) : R :=
  trap_composite f a b (2 ^ n).

(* ================================================================== *)
(* === Romberg tableau === *)
(* ================================================================== *)

(* Richardson extrapolation:
   R(n, 0)  = trap_pow2 f a b n
   R(n, S k) = (4^(S k) * R(n, k) - R(n-1, k)) / (4^(S k) - 1)
   When n = 0 and k > 0, the recursion has no R(-1, k-1); we return
   trap_pow2 f a b 0 unchanged. *)
Fixpoint pow4 (k : nat) : R :=
  match k with
  | 0 => 1
  | S k' => 4 * pow4 k'
  end.

Lemma pow4_pos : forall k, 0 < pow4 k.
Proof. induction k as [| k IH]; simpl; lra. Qed.

Lemma pow4_ge_one : forall k, 1 <= pow4 k.
Proof.
  induction k as [| k IH]; simpl.
  - lra.
  - pose proof (pow4_pos k). lra.
Qed.

Lemma pow4_S_minus_one_pos : forall k, 0 < pow4 (S k) - 1.
Proof.
  intro k. simpl. pose proof (pow4_ge_one k). lra.
Qed.

Fixpoint romberg_table (f : R -> R) (a b : R) (n k : nat) : R :=
  match k with
  | 0 => trap_pow2 f a b n
  | S k' =>
    match n with
    | 0 => trap_pow2 f a b 0
    | S n' =>
      (pow4 (S k') * romberg_table f a b n k' -
       romberg_table f a b n' k') / (pow4 (S k') - 1)
    end
  end.

Definition romberg (f : R -> R) (a b : R) (k : nat) : R :=
  romberg_table f a b k k.

(* ================================================================== *)
(* === Basic identities === *)
(* ================================================================== *)

(* Level 0 of Romberg is the trapezoidal sum with 2^k subintervals. *)
Lemma romberg_level0 :
  forall f a b n, romberg_table f a b n 0 = trap_pow2 f a b n.
Proof. intros. simpl. reflexivity. Qed.

(* The Romberg(0) — just one trapezoid — is (b-a)/2 * (f(a) + f(b)). *)
Lemma romberg_single :
  forall f a b, romberg f a b 0 = (b - a) / 2 * (f a + f b).
Proof.
  intros f a b.
  unfold romberg. simpl.
  unfold trap_pow2, trap_composite.
  change (2 ^ 0)%nat with 1%nat.
  change (INR 1) with 1.
  simpl interior_sum.
  field.
Qed.

(* ================================================================== *)
(* === Exactness on constants === *)
(* ================================================================== *)

Lemma interior_sum_const : forall (c a h : R) (m : nat),
  interior_sum (fun _ => c) a h m = INR (Nat.pred m) * c.
Proof.
  intros c a h m. induction m as [| m IH].
  - simpl. ring.
  - destruct m as [| m'].
    + simpl. ring.
    + (* m = S m' = S (S m''); interior_sum unfolds one step *)
      change (interior_sum (fun _ : R => c) a h (S (S m')))
        with (c + interior_sum (fun _ : R => c) a h (S m')).
      rewrite IH.
      simpl Nat.pred.
      rewrite S_INR. ring.
Qed.

Lemma trap_composite_const_S : forall (c a b : R) (m : nat),
  (m > 0)%nat ->
  trap_composite (fun _ => c) a b m = c * (b - a).
Proof.
  intros c a b m Hm.
  unfold trap_composite.
  rewrite interior_sum_const.
  destruct m as [| m'].
  - lia.
  - simpl Nat.pred. clear Hm.
    assert (HmS : INR (S m') > 0).
    { rewrite S_INR. pose proof (pos_INR m'). lra. }
    assert (HmS_ne : INR (S m') <> 0) by lra.
    rewrite S_INR.
    field. rewrite <- S_INR. exact HmS_ne.
Qed.

Lemma pow2_pos : forall n, (2 ^ n > 0)%nat.
Proof. induction n; simpl; lia. Qed.

Lemma trap_pow2_const : forall (c a b : R) (n : nat),
  trap_pow2 (fun _ => c) a b n = c * (b - a).
Proof.
  intros c a b n. unfold trap_pow2.
  apply trap_composite_const_S. apply pow2_pos.
Qed.

Lemma romberg_table_const : forall (c a b : R) (n k : nat),
  romberg_table (fun _ => c) a b n k = c * (b - a).
Proof.
  intros c a b n. induction n as [| n IHn]; intros k.
  - induction k as [| k IHk].
    + simpl. apply trap_pow2_const.
    + simpl. apply trap_pow2_const.
  - induction k as [| k IHk].
    + simpl. apply trap_pow2_const.
    + simpl. rewrite IHn. rewrite IHk.
      pose proof (pow4_S_minus_one_pos k) as Hpos.
      field. apply Rgt_not_eq. exact Hpos.
Qed.

Theorem romberg_const : forall (c a b : R) (k : nat),
  romberg (fun _ => c) a b k = c * (b - a).
Proof.
  intros c a b k. unfold romberg.
  apply romberg_table_const.
Qed.

(* ================================================================== *)
(* === Romberg vs RInt on constants ===

   Coquelicot's RInt of a constant: RInt (fun _ => c) a b = c * (b - a).
   Combined with romberg_const, this gives: romberg of a constant
   equals its RInt — exact at every refinement level. *)
(* ================================================================== *)

Theorem romberg_RInt_const :
  forall (c a b : R) (k : nat),
    romberg (fun _ : R => c) a b k = RInt (fun _ : R => c) a b.
Proof.
  intros c a b k.
  rewrite romberg_const.
  rewrite (@RInt_const R_CompleteNormedModule a b c).
  unfold scal; simpl. unfold mult; simpl. ring.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions interior_sum_const.
Print Assumptions trap_composite_const_S.
Print Assumptions trap_pow2_const.
Print Assumptions romberg_table_const.
Print Assumptions romberg_const.
Print Assumptions romberg_RInt_const.
Print Assumptions romberg_level0.
Print Assumptions romberg_single.
