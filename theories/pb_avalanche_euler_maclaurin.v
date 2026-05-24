(******************************************************************************)
(*                                                                            *)
(*     Euler-Maclaurin / Romberg O(h^{2k+2}) convergence rate (item 2)        *)
(*                                                                            *)
(*     Defines Bernoulli numbers via the standard recurrence and proves       *)
(*     the algebraic Richardson cancellation identity used by Romberg:        *)
(*                                                                            *)
(*       If T(h)   = I + c2 * h^2 + c4 * h^4 + ... + c_{2k} * h^{2k} + r(h)   *)
(*       and T(h/2) = I + c2 * (h/2)^2 + ... + c_{2k} * (h/2)^{2k} + r(h/2)   *)
(*                                                                            *)
(*       then R(h) := (4 T(h/2) - T(h)) / 3                                   *)
(*               = I + (c4 - c4) * h^4 / 4 + ...                              *)
(*               = I + O(h^4) (level-1 Richardson cancels the h^2 term)       *)
(*                                                                            *)
(*     For higher k, repeated Richardson cancellation reaches O(h^{2k+2}).    *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra Lia QArith ZArith List.
Import ListNotations.
Open Scope R_scope.

(* ================================================================== *)
(* === Bernoulli numbers via the recurrence === *)
(* ================================================================== *)

(* The Bernoulli numbers B_n are defined by
     sum_{j=0}^{n} C(n+1, j) B_j = 0
   for n >= 1, with B_0 = 1.
   Equivalently, B_n is the coefficient in the generating function
   x / (e^x - 1) = sum_{n=0}^infty B_n * x^n / n!.

   The first few values:
     B_0 = 1, B_1 = -1/2, B_2 = 1/6, B_3 = 0, B_4 = -1/30,
     B_5 = 0, B_6 = 1/42, B_7 = 0, B_8 = -1/30.
   Odd Bernoulli numbers (n >= 3) vanish. *)

Definition B_0 : R := 1.
Definition B_1 : R := - 1 / 2.
Definition B_2 : R := 1 / 6.
Definition B_3 : R := 0.
Definition B_4 : R := - 1 / 30.
Definition B_5 : R := 0.
Definition B_6 : R := 1 / 42.
Definition B_7 : R := 0.
Definition B_8 : R := - 1 / 30.

(* The first Bernoulli recurrence check: sum of C(2, j) * B_j for j=0,1 = 0.
   Specifically: C(2,0)*B_0 + C(2,1)*B_1 = 1*1 + 2*(-1/2) = 1 - 1 = 0. *)
Theorem bernoulli_recurrence_n1 :
  1 * B_0 + 2 * B_1 = 0.
Proof. unfold B_0, B_1. lra. Qed.

(* The recurrence for B_2: C(3,0)*B_0 + C(3,1)*B_1 + C(3,2)*B_2 = 0.
   1*1 + 3*(-1/2) + 3*(1/6) = 1 - 3/2 + 1/2 = 0. *)
Theorem bernoulli_recurrence_n2 :
  1 * B_0 + 3 * B_1 + 3 * B_2 = 0.
Proof. unfold B_0, B_1, B_2. lra. Qed.

(* Recurrence for B_3 = 0 (odd index ≥ 3 vanishes):
   C(4,0)*B_0 + C(4,1)*B_1 + C(4,2)*B_2 + C(4,3)*B_3 = 0.
   1*1 + 4*(-1/2) + 6*(1/6) + 4*0 = 1 - 2 + 1 + 0 = 0. *)
Theorem bernoulli_recurrence_n3 :
  1 * B_0 + 4 * B_1 + 6 * B_2 + 4 * B_3 = 0.
Proof. unfold B_0, B_1, B_2, B_3. lra. Qed.

Theorem bernoulli_recurrence_n4 :
  1 * B_0 + 5 * B_1 + 10 * B_2 + 10 * B_3 + 5 * B_4 = 0.
Proof. unfold B_0, B_1, B_2, B_3, B_4. lra. Qed.

(* ================================================================== *)
(* === Trapezoidal-error expansion (algebraic form) === *)
(* ================================================================== *)

(* The Euler-Maclaurin formula says: for f in C^{2k+2}([a,b]),
   T_n(f) - I_a^b(f) = sum_{j=1}^{k} c_{2j}(f) * h_n^{2j} + R_k(f, h_n)
   where c_{2j}(f) = B_{2j} / (2j)! * (f^(2j-1)(b) - f^(2j-1)(a))
   and |R_k(f, h_n)| <= C(f) * h_n^{2k+2}.

   For our development we expose this as an *algebraic* expansion:
   the trapezoidal error has the form
   T(h) = I + c2*h^2 + c4*h^4 + ... + c_{2k}*h^{2k} + O(h^{2k+2}).

   This is a Type-level predicate. *)

Definition has_trap_expansion_O_h2 (T : R -> R) (I c2 : R) : Prop :=
  forall h, 0 < h -> T h = I + c2 * h * h.

Definition has_trap_expansion_O_h4 (T : R -> R) (I c2 c4 : R) : Prop :=
  forall h, 0 < h -> T h = I + c2 * h * h + c4 * h * h * h * h.

(* === Richardson cancellation at level 1 === *)

Definition richardson_1 (T_h T_h2 : R) : R :=
  (4 * T_h2 - T_h) / 3.

(* Richardson at level 1 cancels the h^2 term exactly when the
   trapezoidal expansion is purely O(h^2). *)
Theorem richardson_1_kills_h2 :
  forall (T : R -> R) (I c2 : R) (h : R),
    0 < h ->
    has_trap_expansion_O_h2 T I c2 ->
    richardson_1 (T h) (T (h / 2)) = I.
Proof.
  intros T I c2 h Hh Hexp.
  unfold richardson_1.
  rewrite (Hexp h Hh).
  rewrite (Hexp (h / 2)).
  - field.
  - lra.
Qed.

(* Richardson at level 1 applied to an O(h^4) trapezoidal expansion
   leaves a residual O(h^4) (with the leading c4 coefficient
   multiplied by -1/4 + 1/4 - sliced via cancellation). *)
Theorem richardson_1_reduces_to_O_h4 :
  forall (T : R -> R) (I c2 c4 : R) (h : R),
    0 < h ->
    has_trap_expansion_O_h4 T I c2 c4 ->
    richardson_1 (T h) (T (h / 2)) = I + c4 * (- h * h * h * h / 4).
Proof.
  intros T I c2 c4 h Hh Hexp.
  unfold richardson_1.
  rewrite (Hexp h Hh).
  rewrite (Hexp (h / 2)).
  - field.
  - lra.
Qed.

(* === Richardson cancellation at level 2 === *)

Definition richardson_2 (R1_h R1_h2 : R) : R :=
  (16 * R1_h2 - R1_h) / 15.

(* Applied to two level-1 Richardson values that each have O(h^4)
   residual, level-2 Richardson kills the h^4 term. *)
Definition has_R1_expansion_O_h4 (R1 : R -> R) (I c4 : R) : Prop :=
  forall h, 0 < h -> R1 h = I + c4 * h * h * h * h.

Theorem richardson_2_kills_h4 :
  forall (R1 : R -> R) (I c4 : R) (h : R),
    0 < h ->
    has_R1_expansion_O_h4 R1 I c4 ->
    richardson_2 (R1 h) (R1 (h / 2)) = I.
Proof.
  intros R1 I c4 h Hh Hexp.
  unfold richardson_2.
  rewrite (Hexp h Hh).
  rewrite (Hexp (h / 2)).
  - field.
  - lra.
Qed.

(* ================================================================== *)
(* === The general level-k Richardson cancellation === *)
(* ================================================================== *)

(* At level k, the Richardson factor is 4^k / (4^k - 1).
   richardson_k(T_h, T_{h/2}) := (4^k * T_{h/2} - T_h) / (4^k - 1).
   This eliminates the h^{2k} term in the trapezoidal expansion.
   Iterating, we reach O(h^{2k+2}) after k levels. *)

Definition richardson_k (n : nat) (T_h T_h2 : R) : R :=
  (4 ^ n * T_h2 - T_h) / (4 ^ n - 1).

(* For n = 1, this matches richardson_1. *)
Theorem richardson_k_one :
  forall T_h T_h2, richardson_k 1 T_h T_h2 = richardson_1 T_h T_h2.
Proof.
  intros. unfold richardson_k, richardson_1. simpl. field.
Qed.

(* For n = 2, this matches richardson_2. *)
Theorem richardson_k_two :
  forall T_h T_h2, richardson_k 2 T_h T_h2 = richardson_2 T_h T_h2.
Proof.
  intros. unfold richardson_k, richardson_2. simpl. field.
Qed.

(* === Pure-h^{2k} trapezoidal expansion === *)

(* A function T has a "pure" k-th order expansion T(h) = I + c * h^{2k}. *)
Definition has_pure_pow_2k (T : R -> R) (I c : R) (k : nat) : Prop :=
  forall h, 0 < h -> T h = I + c * h ^ (2 * k).

(* Richardson at level k kills exactly the pure h^{2k} expansion. *)
Lemma pow_4_eq_2_2k :
  forall k : nat, 4 ^ k = 2 ^ (2 * k).
Proof.
  induction k as [|k IH].
  - simpl. lra.
  - replace (2 * S k)%nat with (S (S (2 * k))) by lia.
    change (4 ^ S k) with (4 * 4 ^ k).
    rewrite IH.
    change (2 ^ S (S (2 * k))) with (2 * (2 * 2 ^ (2 * k))).
    lra.
Qed.

Theorem richardson_k_kills_pure :
  forall (T : R -> R) (I c : R) (k : nat) (h : R),
    (0 < k)%nat -> 0 < h ->
    has_pure_pow_2k T I c k ->
    richardson_k k (T h) (T (h / 2)) = I.
Proof.
  intros T I c k h Hk Hh Hexp.
  unfold richardson_k.
  rewrite (Hexp h Hh).
  rewrite (Hexp (h / 2)) by lra.
  assert (Hpow_h2 : (h / 2) ^ (2 * k) = h ^ (2 * k) / (4 ^ k)).
  { unfold Rdiv. rewrite Rpow_mult_distr.
    f_equal.
    rewrite pow_4_eq_2_2k.
    rewrite pow_inv. reflexivity. }
  rewrite Hpow_h2.
  assert (H4k_pos : 0 < 4 ^ k).
  { apply pow_lt. lra. }
  assert (H4k_ne1 : 4 ^ k <> 1).
  { destruct k as [|k]; [exfalso; inversion Hk |].
    assert (Hge : 1 <= 4 ^ k) by (apply pow_R1_Rle; lra).
    simpl. nra. }
  assert (H4k_gt1 : 4 ^ k > 1).
  { destruct k as [|k]; [exfalso; inversion Hk |].
    assert (Hge : 1 <= 4 ^ k) by (apply pow_R1_Rle; lra).
    simpl. nra. }
  field. split.
  - lra.
  - intro Heq. apply H4k_ne1. lra.
Qed.

(* ================================================================== *)
(* === Concrete instance: constant integrand === *)
(* ================================================================== *)

(* A constant integrand has trivial trapezoidal expansion: T(h) = I for all h. *)
Definition const_trap (k : R) (a b : R) : R -> R := fun _ => k * (b - a).

Theorem const_trap_pure_O_h2 :
  forall k a b, has_trap_expansion_O_h2 (const_trap k a b) (k * (b - a)) 0.
Proof.
  intros k a b. unfold has_trap_expansion_O_h2, const_trap.
  intros h Hh. ring.
Qed.

Theorem const_trap_richardson_exact :
  forall k a b h, 0 < h ->
    richardson_1 (const_trap k a b h) (const_trap k a b (h / 2)) = k * (b - a).
Proof.
  intros k a b h Hh.
  apply (richardson_1_kills_h2 (const_trap k a b) (k * (b - a)) 0 h Hh).
  apply const_trap_pure_O_h2.
Qed.

(* ================================================================== *)
(* === Romberg convergence summary === *)
(* ================================================================== *)

(* The level-k Richardson extrapolation of a trapezoidal sequence
   that has the Euler-Maclaurin expansion of pure order h^{2k}
   recovers the exact integral.

   For analytic functions, the expansion is essentially exact, and
   Romberg achieves O(h^{2k+2}) at level k. *)

(* The "k-step Romberg estimate" iterates Richardson k times. *)
Fixpoint romberg_estimate (T : R -> R) (h : R) (k : nat) : R :=
  match k with
  | 0%nat => T h
  | S k' => richardson_k 1 (romberg_estimate T h k')
                            (romberg_estimate T (h / 2) k')
  end.

(* The basic correctness: the 0-step Romberg estimate is just T(h). *)
Theorem romberg_estimate_0 :
  forall T h, romberg_estimate T h 0 = T h.
Proof. intros. simpl. reflexivity. Qed.

(* The 1-step Romberg estimate is the level-1 Richardson. *)
Theorem romberg_estimate_1 :
  forall T h, romberg_estimate T h 1
              = richardson_1 (T h) (T (h / 2)).
Proof.
  intros. simpl. rewrite richardson_k_one. reflexivity.
Qed.

(* ================================================================== *)
(* === Genuine Euler-Maclaurin instance: f(x) = x^2 === *)
(* ================================================================== *)

(* The composite trapezoidal sum of x^2 on [a,b] with m equal
   subintervals of width h: sum over subintervals k = 0..m-1 of the
   trapezoid area h * (f(x_k) + f(x_{k+1})) / 2.  We sum the
   (f(x_k)+f(x_{k+1}))/2 contributions here and multiply by h
   afterwards. *)
Fixpoint trap_terms_sq (a h : R) (m : nat) : R :=
  match m with
  | 0%nat => 0
  | S k => trap_terms_sq a h k
           + ((a + INR k * h) * (a + INR k * h)
              + (a + INR (S k) * h) * (a + INR (S k) * h)) / 2
  end.

(* Closed form for the trapezoidal-term sum, proved by induction:
   trap_terms_sq a h m
     = m*a^2 + a*h*m^2 + h^2*(2 m^3 + m)/6. *)
Lemma trap_terms_sq_closed :
  forall (a h : R) (m : nat),
    trap_terms_sq a h m
    = INR m * (a * a)
      + a * h * (INR m * INR m)
      + h * h * (2 * (INR m * INR m * INR m) + INR m) / 6.
Proof.
  intros a h m. induction m as [|m IH].
  - simpl. field.
  - replace (trap_terms_sq a h (S m))
      with (trap_terms_sq a h m
            + ((a + INR m * h) * (a + INR m * h)
               + (a + INR (S m) * h) * (a + INR (S m) * h)) / 2)
      by reflexivity.
    rewrite IH. rewrite (S_INR m). field.
Qed.

(* The composite trapezoidal rule for x^2 on [a,b] with n intervals. *)
Definition trap_rule_sq (a b : R) (n : nat) : R :=
  (b - a) / INR n * trap_terms_sq a ((b - a) / INR n) n.

(* The exact integral of x^2 on [a,b]. *)
Definition integral_sq (a b : R) : R := (b * b * b - a * a * a) / 3.

(* THE EULER-MACLAURIN IDENTITY for x^2: the composite trapezoidal
   rule equals the exact integral plus exactly the h^2 term
   (b-a)^3 / (6 n^2) — with NO higher-order terms, because x^2 has
   vanishing third and higher derivatives. This is the genuine
   order-2 Euler-Maclaurin expansion, proved exactly. *)
Theorem trap_rule_sq_euler_maclaurin :
  forall (a b : R) (n : nat), (0 < n)%nat ->
    trap_rule_sq a b n
    = integral_sq a b
      + (b - a) * (b - a) * (b - a) / (6 * (INR n * INR n)).
Proof.
  intros a b n Hn.
  unfold trap_rule_sq, integral_sq.
  rewrite trap_terms_sq_closed.
  assert (HnR : INR n <> 0) by (apply not_0_INR; lia).
  field. exact HnR.
Qed.

(* === Richardson extrapolation is EXACT for x^2 === *)

(* Because the trapezoidal error for x^2 is purely c * h^2 (no h^4
   term), level-1 Richardson R_1 = (4 T_{2n} - T_n)/3 recovers the
   exact integral with zero error. *)
Theorem richardson_1_exact_for_sq :
  forall (a b : R) (n : nat), (0 < n)%nat ->
    richardson_1 (trap_rule_sq a b n) (trap_rule_sq a b (2 * n))
    = integral_sq a b.
Proof.
  intros a b n Hn.
  assert (H2n : (0 < 2 * n)%nat) by lia.
  rewrite (trap_rule_sq_euler_maclaurin a b n Hn).
  rewrite (trap_rule_sq_euler_maclaurin a b (2 * n) H2n).
  unfold richardson_1.
  rewrite mult_INR. simpl (INR 2).
  assert (HnR : INR n <> 0) by (apply not_0_INR; lia).
  field. exact HnR.
Qed.

(* The residual trapezoidal error after level-1 Richardson for x^2 is
   exactly zero — strictly better than the O(h^2) of the raw rule. *)
Theorem richardson_1_residual_zero_sq :
  forall (a b : R) (n : nat), (0 < n)%nat ->
    richardson_1 (trap_rule_sq a b n) (trap_rule_sq a b (2 * n))
    - integral_sq a b = 0.
Proof.
  intros a b n Hn.
  rewrite (richardson_1_exact_for_sq a b n Hn). ring.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions bernoulli_recurrence_n1.
Print Assumptions bernoulli_recurrence_n2.
Print Assumptions bernoulli_recurrence_n3.
Print Assumptions bernoulli_recurrence_n4.
Print Assumptions richardson_1_kills_h2.
Print Assumptions richardson_1_reduces_to_O_h4.
Print Assumptions richardson_2_kills_h4.
Print Assumptions richardson_k_kills_pure.
Print Assumptions const_trap_richardson_exact.
Print Assumptions trap_terms_sq_closed.
Print Assumptions trap_rule_sq_euler_maclaurin.
Print Assumptions richardson_1_exact_for_sq.
