(******************************************************************************)
(*                                                                            *)
(*     Adaptive Romberg integration                                           *)
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

From Stdlib Require Import Reals Lra ZArith Lia QArith List.
From Coquelicot Require Import Coquelicot.
Import ListNotations.

Close Scope Q_scope.
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
(* === Euler-Maclaurin expansion and Bernoulli numbers === *)
(* ================================================================== *)

(* The Richardson tableau above cancels successive Taylor terms in the
   trapezoidal error; the Euler-Maclaurin expansion below identifies
   those terms with the Bernoulli numbers and proves the order-2
   instance exactly for x^2. *)

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
(* === Euler-Maclaurin instance: f(x) = x^2 === *)
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

(* The Euler-Maclaurin identity for x^2: the composite trapezoidal rule
   equals the exact integral plus the h^2 term (b-a)^3 / (6 n^2), with no
   higher-order terms, since x^2 has vanishing third and higher
   derivatives. This is the order-2 Euler-Maclaurin expansion. *)
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
(* === The Bernoulli sequence from its defining recurrence === *)
(* ================================================================== *)

(* Pascal's triangle, for the binomial coefficients of the recurrence. *)
Fixpoint binom (n k : nat) : nat :=
  match n, k with
  | _, O => 1%nat
  | O, S _ => 0%nat
  | S n', S k' => (binom n' k' + binom n' (S k'))%nat
  end.

Section BernoulliSequence.
Local Open Scope Q_scope.

(* Given the prefix [B_0; ...; B_{m-1}], the defining relation
   sum_{j=0}^{m} C(m+1,j) B_j = 0 (with C(m+1,m) = m+1) solves for
     B_m = - 1/(m+1) * sum_{j=0}^{m-1} C(m+1,j) B_j. *)
Definition next_bernoulli (L : list Q) (m : nat) : Q :=
  - (1 # 1) / inject_Z (Z.of_nat (m + 1)%nat)
  * fold_right Qplus 0
      (map (fun j : nat => inject_Z (Z.of_nat (binom (m + 1)%nat j)) * nth j L 0)
           (seq 0%nat m)).

(* The sequence built iteratively as [B_0; ...; B_n]. *)
Fixpoint bernoulli_list (n : nat) : list Q :=
  match n with
  | O => 1 :: nil
  | S k => let L := bernoulli_list k in L ++ next_bernoulli L (S k) :: nil
  end.

Definition bernoulli (n : nat) : Q := nth n (bernoulli_list n) 0.

(* The construction reproduces the classical Bernoulli numbers. *)
Example bernoulli_val_0 : bernoulli 0 == 1.         Proof. vm_compute. reflexivity. Qed.
Example bernoulli_val_1 : bernoulli 1 == (-1) # 2.  Proof. vm_compute. reflexivity. Qed.
Example bernoulli_val_2 : bernoulli 2 == 1 # 6.     Proof. vm_compute. reflexivity. Qed.
Example bernoulli_val_3 : bernoulli 3 == 0.         Proof. vm_compute. reflexivity. Qed.
Example bernoulli_val_4 : bernoulli 4 == (-1) # 30. Proof. vm_compute. reflexivity. Qed.
Example bernoulli_val_6 : bernoulli 6 == 1 # 42.    Proof. vm_compute. reflexivity. Qed.
Example bernoulli_val_8 : bernoulli 8 == (-1) # 30. Proof. vm_compute. reflexivity. Qed.

(* The constructed sequence satisfies its own defining recurrence
   sum_{j=0}^{n} C(n+1,j) B_j = 0 for every n >= 1. *)
Definition bern_recurrence_sum (n : nat) : Q :=
  fold_right Qplus 0
    (map (fun j : nat => inject_Z (Z.of_nat (binom (n + 1)%nat j)) * bernoulli j)
         (seq 0%nat (S n))).

Example bern_recurrence_1 : bern_recurrence_sum 1 == 0. Proof. vm_compute. reflexivity. Qed.
Example bern_recurrence_2 : bern_recurrence_sum 2 == 0. Proof. vm_compute. reflexivity. Qed.
Example bern_recurrence_3 : bern_recurrence_sum 3 == 0. Proof. vm_compute. reflexivity. Qed.
Example bern_recurrence_4 : bern_recurrence_sum 4 == 0. Proof. vm_compute. reflexivity. Qed.
Example bern_recurrence_5 : bern_recurrence_sum 5 == 0. Proof. vm_compute. reflexivity. Qed.

End BernoulliSequence.

(* The order-2 Euler-Maclaurin correction IS the Bernoulli B_2 term:
   the trapezoidal error for x^2 equals (B_2 / 2!) h^2 (f'(b) - f'(a))
   with f'(x) = 2x. This identifies the rule's error coefficient with
   the Bernoulli number B_2 = 1/6 of the general expansion. *)
Theorem trap_rule_sq_bernoulli_term :
  forall (a b : R) (n : nat), (0 < n)%nat ->
    trap_rule_sq a b n - integral_sq a b
    = B_2 / 2 * (((b - a) / INR n) * ((b - a) / INR n)) * (2 * b - 2 * a).
Proof.
  intros a b n Hn.
  rewrite (trap_rule_sq_euler_maclaurin a b n Hn).
  unfold B_2.
  assert (HnR : INR n <> 0) by (apply not_0_INR; lia).
  field. exact HnR.
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
Print Assumptions bernoulli.
Print Assumptions trap_rule_sq_bernoulli_term.
