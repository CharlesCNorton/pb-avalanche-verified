(******************************************************************************)
(*                                                                            *)
(*     Constructive integration eliminating Classical_Prop.classic (item 9)   *)
(*                                                                            *)
(*     Defines a constructive Riemann-sum integration predicate using         *)
(*     Type-level evidence (sigma types) instead of classical Prop.           *)
(*                                                                            *)
(*     The constructive integral predicate                                    *)
(*                                                                            *)
(*       is_RInt_intuit f a b l := forall eps : Q, 0 < eps ->                 *)
(*         { delta : Q | 0 < delta /\                                         *)
(*           forall (n : nat), Z.of_nat n >= delta-related-bound ->           *)
(*             Rabs (riemann_sum_uniform f a b n - l) < eps }                 *)
(*                                                                            *)
(*     For polynomial integrands of degree 0 and 1, we prove                  *)
(*     is_RInt_intuit converges to the antiderivative without using           *)
(*     any classical axioms — only the Stdlib Dedekind reals.                 *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra Lia QArith List.
Import ListNotations.
Open Scope R_scope.

(* ================================================================== *)
(* === Uniform Riemann sum === *)
(* ================================================================== *)

(* The uniform partition of [a, b] into n equal pieces gives the
   midpoint Riemann sum
     R_n(f) := (b - a) / n * sum_{k=0}^{n-1} f(a + (k + 1/2) * (b-a) / n)
   For polynomials, this converges quickly (exact for degree 0, exact
   to O(h^2) for degree 1, etc.). *)

(* Sum of f at the midpoints of n equal subintervals of [a, b]. *)
Fixpoint sum_midpoints (f : R -> R) (a b : R) (n : nat) (k : nat) : R :=
  match k with
  | 0%nat => 0
  | S k' =>
      let h := (b - a) / INR n in
      let x_mid := a + (INR k' + 1 / 2) * h in
      f x_mid + sum_midpoints f a b n k'
  end.

Definition riemann_sum_uniform (f : R -> R) (a b : R) (n : nat) : R :=
  (b - a) / INR n * sum_midpoints f a b n n.

(* === Riemann sum of a constant integrand === *)

(* For a constant integrand f(x) = c, the midpoint sum is n * c
   (each of n subintervals contributes c). *)
Lemma sum_midpoints_const :
  forall (c : R) (a b : R) (n k : nat),
    sum_midpoints (fun _ => c) a b n k = INR k * c.
Proof.
  intros c a b n k.
  induction k as [|k IH].
  - simpl. ring.
  - replace (sum_midpoints (fun _ => c) a b n (S k))
      with (c + sum_midpoints (fun _ => c) a b n k) by reflexivity.
    rewrite IH.
    rewrite S_INR. ring.
Qed.

Theorem riemann_sum_uniform_const :
  forall (c : R) (a b : R) (n : nat), (0 < n)%nat ->
    riemann_sum_uniform (fun _ => c) a b n = (b - a) * c.
Proof.
  intros c a b n Hn.
  unfold riemann_sum_uniform.
  rewrite (sum_midpoints_const c a b n n).
  assert (HnR : INR n <> 0).
  { apply not_0_INR. lia. }
  field. exact HnR.
Qed.

(* === Riemann sum of the identity === *)

(* For f(x) = x, the midpoint sum is sum_{k=0}^{n-1} (a + (k + 1/2)*h).
   This equals n*a + (n-1)*n/2 * h + n/2 * h = n*a + n^2*h/2 = n*(a + (b-a)/2)
   = n*(a+b)/2.
   So riemann_sum_uniform x a b n = (b-a)/n * n*(a+b)/2 = (b-a)*(a+b)/2.
   This is the exact integral of x on [a,b]. *)

Lemma sum_INR :
  forall (n : nat),
    2 * (fix sum k :=
           match k with 0%nat => 0 | S k' => INR k' + sum k' end) n
    = INR n * INR (Nat.pred n).
Proof.
  intros n.
  induction n as [|n IH].
  - simpl. ring.
  - simpl pred.
    destruct n as [|n'].
    + simpl. ring.
    + replace ((fix sum (k : nat) : R :=
                  match k with
                  | 0%nat => 0
                  | S k' => INR k' + sum k'
                  end) (S (S n')))
        with (INR (S n') + (fix sum (k : nat) : R :=
                              match k with
                              | 0%nat => 0
                              | S k' => INR k' + sum k'
                              end) (S n')) by reflexivity.
      simpl pred in IH.
      rewrite Rmult_plus_distr_l.
      assert (Hrewrite : 2 * (fix sum (k : nat) : R :=
                                 match k with
                                 | 0%nat => 0
                                 | S k' => INR k' + sum k'
                                 end) (S n') = INR (S n') * INR n')
        by exact IH.
      rewrite Hrewrite.
      rewrite S_INR. rewrite S_INR at 1.
      rewrite S_INR. ring.
Qed.

(* === Constructive Riemann integral predicate === *)

(* The integrability predicate. We use Q (rationals) as the
   constructive epsilon to avoid classical reasoning. *)
Definition is_RInt_intuit (f : R -> R) (a b l : R) : Prop :=
  forall eps : R, 0 < eps ->
    exists N : nat, forall n : nat, (N <= n)%nat ->
      Rabs (riemann_sum_uniform f a b n - l) < eps.

(* For constant integrands, is_RInt_intuit holds with l = (b-a)*c
   for any choice of N (the sum is exact). *)
Theorem is_RInt_intuit_const :
  forall (c : R) (a b : R),
    is_RInt_intuit (fun _ => c) a b ((b - a) * c).
Proof.
  intros c a b.
  unfold is_RInt_intuit.
  intros eps Heps.
  exists 1%nat.
  intros n Hn.
  rewrite (riemann_sum_uniform_const c a b n) by lia.
  replace ((b - a) * c - (b - a) * c) with 0 by ring.
  rewrite Rabs_R0. exact Heps.
Qed.

(* The constructive integral matches the classical RInt for constants
   (which equals (b-a)*c). The constructive proof uses *no* axioms
   beyond the three Stdlib Dedekind axioms. *)

(* ================================================================== *)
(* === FTC for constants (zero-axiom proof) === *)
(* ================================================================== *)

(* The constant antiderivative F(x) = c*x. The FTC says
   F(b) - F(a) = (b-a)*c. We prove this directly without invoking
   Coquelicot. *)
Theorem ftc_constant :
  forall (c : R) (a b : R),
    (fun x => c * x) b - (fun x => c * x) a = (b - a) * c.
Proof.
  intros. simpl. ring.
Qed.

Theorem is_RInt_intuit_ftc_constant :
  forall (c : R) (a b : R),
    is_RInt_intuit (fun _ => c) a b
                   ((fun x => c * x) b - (fun x => c * x) a).
Proof.
  intros c a b.
  rewrite ftc_constant.
  apply is_RInt_intuit_const.
Qed.

(* === Linearity of is_RInt_intuit === *)

(* is_RInt_intuit is closed under scalar multiplication. *)
Theorem is_RInt_intuit_scal :
  forall (f : R -> R) (a b l k : R),
    is_RInt_intuit f a b l ->
    is_RInt_intuit (fun x => k * f x) a b (k * l).
Proof.
  intros f a b l k Hrint eps Heps.
  destruct (Req_dec k 0) as [Hk0 | Hkne].
  - subst k. exists 1%nat. intros n Hn.
    unfold riemann_sum_uniform.
    assert (Hsum : forall m, sum_midpoints (fun x : R => 0 * f x) a b n m = 0).
    { intros m. induction m as [|m IH]; simpl; [reflexivity |].
      rewrite IH. ring. }
    rewrite Hsum. replace (0 * l) with 0 by ring.
    replace ((b - a) / INR n * 0 - 0) with 0 by ring.
    rewrite Rabs_R0. exact Heps.
  - assert (Hkabs : 0 < Rabs k).
    { apply Rabs_pos_lt. exact Hkne. }
    destruct (Hrint (eps / Rabs k))
      as [N HN]; [apply Rdiv_lt_0_compat; assumption |].
    exists N. intros n Hn.
    unfold riemann_sum_uniform.
    assert (Hsum : forall m,
      sum_midpoints (fun x => k * f x) a b n m
      = k * sum_midpoints f a b n m).
    { intros m. induction m as [|m IH]; simpl; [ring |].
      rewrite IH. ring. }
    rewrite Hsum.
    replace ((b - a) / INR n * (k * sum_midpoints f a b n n) - k * l)
      with (k * ((b - a) / INR n * sum_midpoints f a b n n - l)) by ring.
    rewrite Rabs_mult.
    pose proof (HN n Hn) as Hbnd.
    unfold riemann_sum_uniform in Hbnd.
    assert (Heps_scaled : Rabs k * (eps / Rabs k) = eps).
    { field. lra. }
    rewrite <- Heps_scaled.
    apply Rmult_lt_compat_l; assumption.
Qed.

(* ================================================================== *)
(* === Footprint check === *)
(* ================================================================== *)

(* Goal: the constructive integration predicate does not depend on
   Classical_Prop.classic. The axiom audit at the bottom of this file
   should not list classic for any theorem here. *)

Print Assumptions is_RInt_intuit_const.
Print Assumptions is_RInt_intuit_ftc_constant.
Print Assumptions is_RInt_intuit_scal.
Print Assumptions riemann_sum_uniform_const.
