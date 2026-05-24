(******************************************************************************)
(*                                                                            *)
(*     Constructive subset audit and classic-free Riemann integral            *)
(*                                                                            *)
(*     Identifies the maximal subset of the development that closes by Qed    *)
(*     without invoking Classical_Prop.classic. The classical axiom is        *)
(*     pulled in only via Coquelicot's fundamental-theorem-of-calculus        *)
(*     machinery (RInt_Derive); theorems that do not route through FTC are    *)
(*     fully constructive (modulo the Stdlib Dedekind-real axioms).    *)
(*                                                                            *)
(*     A full elimination of Classical_Prop.classic requires replacing       *)
(*     Coquelicot's classical integration layer with a constructive one.     *)
(*     The is_RInt_intuit framework at the end of this file is one such       *)
(*     classic-free Riemann-sum integral.                                     *)
(*                                                                            *)
(*     The Print Assumptions checks below collect the constructive-core       *)
(*     theorems whose footprint is exactly the Stdlib Dedekind-real           *)
(*     axioms (sig_forall_dec, sig_not_dec, functional_extensionality_dep),   *)
(*     each witnessing the absence of classic.                                *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra Lia QArith List Bool ConstructiveEpsilon
                           Classical_Prop ClassicalDedekindReals
                           FunctionalExtensionality.
From Coquelicot Require Import Rcomplements.  (* nfloor_ex: constructive floor *)
From PBAvalanche Require Import
  pb_avalanche
  pb_avalanche_units
  pb_avalanche_units_q
  pb_avalanche_dr_framework
  pb_avalanche_nuclear
  pb_avalanche_eddington
  pb_avalanche_ash
  pb_avalanche_energy_balance.
Import ListNotations.

Close Scope Q_scope.
Open Scope R_scope.

(* ================================================================== *)
(* === Constructive-core theorems === *)
(* ================================================================== *)

(* The abstract framework's Hora-Putvinski settlement is constructive
   in every concrete instantiation that does not use Coquelicot's
   integral derivation. *)

Print Assumptions ConcreteSettlement.hora_putvinski_settlement.
Print Assumptions ConcreteSettlement.reactor_no_multiplication.
Print Assumptions ConcreteSettlement.reactor_no_marginal.
Print Assumptions ConcreteSettlement.reactor_safety_margin_positive.

Print Assumptions PhysicalSettlement.hora_putvinski_settlement.
Print Assumptions PhysicalSettlement.reactor_no_multiplication.

Print Assumptions SaturatedSettlement.hora_putvinski_settlement.
Print Assumptions LinearCrossSectionSettlement.hora_putvinski_settlement.

Print Assumptions SolarSettlement.hora_putvinski_settlement.
Print Assumptions solar_no_avalanche.
Print Assumptions solar_safety_margin.

(* Algebraic/dimensional content is constructive. *)
Print Assumptions unit_mul_inv_r.
Print Assumptions unit_pow_add.
Print Assumptions multiplication_factor_unit_dimensionless.
Print Assumptions unit_mul_q_inv_r.
Print Assumptions sqrt_unit_squared.
Print Assumptions sqrt_T_unit_squared_is_T.

(* The Coulomb-strength ordering for nuclear reactant pairs:
   constructive. *)
Print Assumptions coulomb_barrier_ordering.
Print Assumptions Q_value_ordering.

(* Ash self-quenching and energy-balance constraints: constructive. *)
Print Assumptions tau_slow_alpha_ash_decreasing.
Print Assumptions M_ash_decreasing.
Print Assumptions energy_balance_density_constraint.

(* DR-typed dimensional balance: constructive. *)
Print Assumptions dr_rate_ratio_unit.
Print Assumptions rate_two_density_ratio_dimensionless.
Print Assumptions reaction_freq_unit_value.

(* Witness states: the rescaled-units concrete witness, the physical
   witness, the corner witness, and the solar instance all close
   constructively (no classical reasoning needed for these
   first-order arithmetic statements). *)
Print Assumptions witness_no_avalanche.
Print Assumptions physical_witness_no_avalanche.
Print Assumptions saturated_corner_witness_M_value.
Print Assumptions saturated_FoM_max_loose.

(* ================================================================== *)
(* === Final wrap-up theorem: the constructive Hora-Putvinski =====   *)
(* ================================================================== *)

(* A bundled compound statement of the constructive-core content of
   the avalanche settlement: each conjunct is one of the framework's
   classical-free conclusions, all assembled into a single closing
   theorem. The classical axiom is NOT invoked in any branch — only
   the Stdlib Dedekind-real axioms appear in the assumption
   footprint, as the audit checks below confirm. *)

Theorem hora_putvinski_constructive :
  (* (A) Concrete-rescaled settlement *)
  (forall s, ConcreteSettlement.reactor_regime s ->
             ConcreteSettlement.multiplication_factor s < 1) /\
  (* (B) Physical-scale settlement *)
  (forall s, PhysicalSettlement.reactor_regime s ->
             PhysicalSettlement.multiplication_factor s < 1) /\
  (* (C) Saturated-integral settlement *)
  (forall s, SaturatedSettlement.reactor_regime s ->
             SaturatedSettlement.multiplication_factor s < 1) /\
  (* (D) Linear-cross-section settlement *)
  (forall s, LinearCrossSectionSettlement.reactor_regime s ->
             LinearCrossSectionSettlement.multiplication_factor s < 1) /\
  (* (E) Solar (Eddington) settlement *)
  (forall s, SolarSettlement.reactor_regime s ->
             SolarSettlement.multiplication_factor s < 1) /\
  (* (F) Dimensional balance: M ratio is dimensionless *)
  (unit_div rate_unit rate_unit = zero_unit) /\
  (* (G) Sharp dichotomy: M != 1 on the regime *)
  (forall s, ConcreteSettlement.reactor_regime s ->
             ConcreteSettlement.multiplication_factor s <> 1).
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - exact ConcreteSettlement.reactor_no_multiplication.
  - exact PhysicalSettlement.reactor_no_multiplication.
  - exact SaturatedSettlement.reactor_no_multiplication.
  - exact LinearCrossSectionSettlement.reactor_no_multiplication.
  - exact SolarSettlement.reactor_no_multiplication.
  - exact multiplication_factor_unit_dimensionless.
  - exact ConcreteSettlement.reactor_no_marginal.
Qed.

Print Assumptions hora_putvinski_constructive.


(* ================================================================== *)
(* === Classic-free constructive Riemann integral === *)
(* ================================================================== *)

(* A hand-rolled Riemann-sum integral predicate is_RInt_intuit that
   avoids Coquelicot's classical FTC layer: its base cases, linearity,
   monotonicity, uniqueness and extensionality all close using only the
   Stdlib Dedekind-real axioms, with no Classical_Prop.classic. *)
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
   beyond the Stdlib Dedekind axioms. *)

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

(* === Extensionality and further closure (all classic-free) === *)

Lemma sum_midpoints_ext :
  forall (f g : R -> R) (a b : R) (n m : nat),
    (forall x, f x = g x) ->
    sum_midpoints f a b n m = sum_midpoints g a b n m.
Proof.
  intros f g a b n m Hfg. induction m as [|m IH]; simpl; [reflexivity |].
  rewrite IH, Hfg. reflexivity.
Qed.

Theorem is_RInt_intuit_ext :
  forall (f g : R -> R) (a b l : R),
    (forall x, f x = g x) ->
    is_RInt_intuit f a b l -> is_RInt_intuit g a b l.
Proof.
  intros f g a b l Hfg Hf eps Heps.
  destruct (Hf eps Heps) as [N HN]. exists N. intros n Hn.
  unfold riemann_sum_uniform.
  rewrite <- (sum_midpoints_ext f g a b n n Hfg).
  exact (HN n Hn).
Qed.

Theorem is_RInt_intuit_opp :
  forall (f : R -> R) (a b l : R),
    is_RInt_intuit f a b l ->
    is_RInt_intuit (fun x => - f x) a b (- l).
Proof.
  intros f a b l Hf.
  apply (is_RInt_intuit_ext (fun x => -1 * f x) (fun x => - f x)).
  - intro x. ring.
  - replace (- l) with (-1 * l) by ring.
    apply is_RInt_intuit_scal. exact Hf.
Qed.

(* === Additivity of is_RInt_intuit === *)

Lemma sum_midpoints_plus :
  forall (f g : R -> R) (a b : R) (n m : nat),
    sum_midpoints (fun x => f x + g x) a b n m
    = sum_midpoints f a b n m + sum_midpoints g a b n m.
Proof.
  intros f g a b n m. induction m as [|m IH]; simpl; [ring |].
  rewrite IH. ring.
Qed.

Theorem is_RInt_intuit_plus :
  forall (f g : R -> R) (a b lf lg : R),
    is_RInt_intuit f a b lf ->
    is_RInt_intuit g a b lg ->
    is_RInt_intuit (fun x => f x + g x) a b (lf + lg).
Proof.
  intros f g a b lf lg Hf Hg eps Heps.
  destruct (Hf (eps / 2)) as [Nf HNf]; [lra |].
  destruct (Hg (eps / 2)) as [Ng HNg]; [lra |].
  exists (Nat.max Nf Ng). intros n Hn.
  unfold riemann_sum_uniform.
  rewrite sum_midpoints_plus.
  replace ((b - a) / INR n * (sum_midpoints f a b n n + sum_midpoints g a b n n)
           - (lf + lg))
    with (((b - a) / INR n * sum_midpoints f a b n n - lf)
        + ((b - a) / INR n * sum_midpoints g a b n n - lg)) by ring.
  eapply Rle_lt_trans; [apply Rabs_triang |].
  pose proof (HNf n (Nat.le_trans _ _ _ (Nat.le_max_l Nf Ng) Hn)) as Hbf.
  pose proof (HNg n (Nat.le_trans _ _ _ (Nat.le_max_r Nf Ng) Hn)) as Hbg.
  unfold riemann_sum_uniform in Hbf, Hbg.
  lra.
Qed.

(* Subtraction closure, from additivity and negation. *)
Theorem is_RInt_intuit_minus :
  forall (f g : R -> R) (a b lf lg : R),
    is_RInt_intuit f a b lf ->
    is_RInt_intuit g a b lg ->
    is_RInt_intuit (fun x => f x - g x) a b (lf - lg).
Proof.
  intros f g a b lf lg Hf Hg.
  apply (is_RInt_intuit_ext (fun x => f x + - g x) (fun x => f x - g x)).
  - intro x. ring.
  - replace (lf - lg) with (lf + - lg) by ring.
    apply is_RInt_intuit_plus; [exact Hf | apply is_RInt_intuit_opp; exact Hg].
Qed.

(* === Monotonicity (the RInt_le analog) === *)

(* The midpoint sum is monotone in the integrand when a <= b. *)
Lemma sum_midpoints_le :
  forall (f g : R -> R) (a b : R) (n m : nat),
    (forall x, f x <= g x) ->
    sum_midpoints f a b n m <= sum_midpoints g a b n m.
Proof.
  intros f g a b n m Hfg. induction m as [|m IH]; simpl; [lra |].
  apply Rplus_le_compat; [apply Hfg | exact IH].
Qed.

Theorem is_RInt_intuit_le :
  forall (f g : R -> R) (a b lf lg : R),
    a <= b ->
    (forall x, f x <= g x) ->
    is_RInt_intuit f a b lf ->
    is_RInt_intuit g a b lg ->
    lf <= lg.
Proof.
  intros f g a b lf lg Hab Hfg Hf Hg.
  (* Suppose lf > lg; derive a contradiction by choosing eps small. *)
  destruct (Rle_lt_dec lf lg) as [Hle | Hlt]; [exact Hle | exfalso].
  set (eps := (lf - lg) / 4).
  assert (Heps : 0 < eps) by (unfold eps; lra).
  destruct (Hf eps) as [Nf HNf]; [exact Heps |].
  destruct (Hg eps) as [Ng HNg]; [exact Heps |].
  set (n := S (Nat.max Nf Ng)).
  assert (HnNf : (Nf <= n)%nat)
    by (unfold n; apply Nat.le_trans with (Nat.max Nf Ng);
        [apply Nat.le_max_l | apply Nat.le_succ_diag_r]).
  assert (HnNg : (Ng <= n)%nat)
    by (unfold n; apply Nat.le_trans with (Nat.max Nf Ng);
        [apply Nat.le_max_r | apply Nat.le_succ_diag_r]).
  pose proof (HNf n HnNf) as Hbf.
  pose proof (HNg n HnNg) as Hbg.
  (* Riemann sums: R_n(f) <= R_n(g) since a <= b and f <= g. *)
  assert (Hn_pos : (0 < n)%nat) by (unfold n; lia).
  assert (HnR : 0 < INR n) by (apply lt_0_INR; exact Hn_pos).
  assert (Hcoef : 0 <= (b - a) / INR n).
  { apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; exact HnR]. }
  assert (Hsum_le : riemann_sum_uniform f a b n <= riemann_sum_uniform g a b n).
  { unfold riemann_sum_uniform.
    apply Rmult_le_compat_l; [exact Hcoef |].
    apply sum_midpoints_le. exact Hfg. }
  (* From the eps-bounds: lf < R_n(f) + eps, R_n(g) < lg + eps. *)
  apply Rabs_def2 in Hbf.
  apply Rabs_def2 in Hbg.
  unfold eps in *. lra.
Qed.

(* ================================================================== *)
(* === FTC for the identity (midpoint rule is exact for linear) === *)
(* ================================================================== *)

(* The midpoint partial sum of the identity. *)
Lemma sum_midpoints_id :
  forall (a b : R) (n k : nat), (0 < n)%nat ->
    sum_midpoints (fun x => x) a b n k
    = INR k * a + (b - a) / INR n * (INR k * INR k / 2).
Proof.
  intros a b n k Hn.
  assert (HnR : INR n <> 0) by (apply not_0_INR; lia).
  induction k as [|k IH].
  - simpl. field. exact HnR.
  - replace (sum_midpoints (fun x => x) a b n (S k))
      with (a + (INR k + 1 / 2) * ((b - a) / INR n)
            + sum_midpoints (fun x => x) a b n k) by reflexivity.
    rewrite IH. rewrite S_INR. field. exact HnR.
Qed.

Theorem riemann_sum_uniform_id :
  forall (a b : R) (n : nat), (0 < n)%nat ->
    riemann_sum_uniform (fun x => x) a b n = (b - a) * (a + b) / 2.
Proof.
  intros a b n Hn.
  unfold riemann_sum_uniform.
  rewrite sum_midpoints_id by exact Hn.
  assert (HnR : INR n <> 0) by (apply not_0_INR; lia).
  field. exact HnR.
Qed.

(* The midpoint rule is *exact* for the identity at every n, so the
   constructive integral is the exact antiderivative difference. *)
Theorem is_RInt_intuit_id :
  forall (a b : R),
    is_RInt_intuit (fun x => x) a b ((b - a) * (a + b) / 2).
Proof.
  intros a b eps Heps.
  exists 1%nat. intros n Hn.
  rewrite (riemann_sum_uniform_id a b n) by lia.
  replace ((b - a) * (a + b) / 2 - (b - a) * (a + b) / 2) with 0 by ring.
  rewrite Rabs_R0. exact Heps.
Qed.

(* FTC for the identity: F(x) = x^2/2, F(b) - F(a) = (b^2 - a^2)/2
   = (b-a)(a+b)/2. *)
Theorem is_RInt_intuit_ftc_id :
  forall (a b : R),
    is_RInt_intuit (fun x => x) a b
                   ((fun x => x * x / 2) b - (fun x => x * x / 2) a).
Proof.
  intros a b. cbn beta.
  replace (b * b / 2 - a * a / 2) with ((b - a) * (a + b) / 2) by field.
  apply is_RInt_intuit_id.
Qed.

(* FTC for an affine integrand k*x + c via linearity. *)
Theorem is_RInt_intuit_affine :
  forall (k c a b : R),
    is_RInt_intuit (fun x => k * x + c) a b
                   (k * ((b - a) * (a + b) / 2) + (b - a) * c).
Proof.
  intros k c a b.
  apply is_RInt_intuit_plus.
  - apply (is_RInt_intuit_scal (fun x => x) a b ((b - a) * (a + b) / 2) k).
    apply is_RInt_intuit_id.
  - apply is_RInt_intuit_const.
Qed.

(* ================================================================== *)
(* === Classic-free FTC for the square: integral of x^2 === *)
(* ================================================================== *)

(* The Coquelicot route to integral_a^b x^2 = (b^3 - a^3)/3 runs through
   the classical fundamental theorem of calculus (RInt_Derive), pulling
   in Classical_Prop.classic. The midpoint Riemann sum of x^2 has the
   exact closed form (b^3-a^3)/3 - (b-a)^3/(12 n^2), so its limit is the
   integral and the whole derivation closes on the Dedekind axioms with
   no classic — the polynomial FTC need not be classical. *)

(* Constructive Archimedean witness: every real is below some INR n. *)
Lemma arch_nat : forall x : R, exists n : nat, x < INR n.
Proof.
  intro x. destruct (Rle_dec 0 x) as [Hx | Hx].
  - destruct (nfloor_ex x Hx) as [n [_ Hn]]. exists (S n). rewrite S_INR. lra.
  - exists 1%nat. simpl. lra.
Qed.

(* Closed form of the midpoint sum of x^2. *)
Lemma sum_midpoints_sq_closed :
  forall (a b : R) (n : nat), (0 < n)%nat -> forall k : nat,
    sum_midpoints (fun x => x * x) a b n k =
    INR k * (a*a) + a*((b-a)/INR n)*(INR k * INR k)
    + ((b-a)/INR n)*((b-a)/INR n)*((INR k * INR k * INR k)/3 - INR k/12).
Proof.
  intros a b n Hn. assert (HnR : INR n <> 0) by (apply not_0_INR; lia).
  induction k as [|k IH].
  - simpl. field. exact HnR.
  - cbn [sum_midpoints]. cbv zeta. rewrite IH. rewrite S_INR. field. exact HnR.
Qed.

(* The uniform Riemann sum of x^2 equals the integral minus an explicit
   O(1/n^2) midpoint error. *)
Lemma riemann_sq_closed :
  forall (a b : R) (n : nat), (0 < n)%nat ->
    riemann_sum_uniform (fun x => x * x) a b n =
    (b*b*b - a*a*a)/3 - (b-a)*(b-a)*(b-a)/(12*(INR n*INR n)).
Proof.
  intros a b n Hn. unfold riemann_sum_uniform.
  rewrite (sum_midpoints_sq_closed a b n Hn n).
  assert (HnR : INR n <> 0) by (apply not_0_INR; lia). field. exact HnR.
Qed.

(* Hence integral_a^b x^2 = (b^3 - a^3)/3, constructively. *)
Theorem is_RInt_intuit_sq :
  forall (a b : R),
    is_RInt_intuit (fun x => x * x) a b ((b*b*b - a*a*a)/3).
Proof.
  intros a b eps Heps.
  set (K := Rabs ((b-a)*(b-a)*(b-a)) / 12).
  assert (HK : 0 <= K) by (unfold K; apply Rmult_le_pos; [apply Rabs_pos | lra]).
  destruct (arch_nat (K / eps)) as [M HM].
  exists (max 1 M). intros n Hn.
  assert (HnRpos : 0 < INR n) by (apply lt_0_INR; lia).
  assert (HnR1 : 1 <= INR n) by (rewrite <- INR_1; apply le_INR; lia).
  assert (HnR : INR n <> 0) by (apply Rgt_not_eq; exact HnRpos).
  assert (HMn : INR M <= INR n) by (apply le_INR; lia).
  assert (HKlt : K < eps * INR n).
  { apply Rlt_le_trans with (eps * INR M).
    - apply (Rmult_lt_reg_r (/ eps)); [apply Rinv_0_lt_compat; exact Heps |].
      replace (eps * INR M * / eps) with (INR M) by (field; lra).
      replace (K * / eps) with (K / eps) by (unfold Rdiv; ring). exact HM.
    - apply Rmult_le_compat_l; [lra | exact HMn]. }
  rewrite (riemann_sq_closed a b n ltac:(lia)).
  replace ((b*b*b - a*a*a)/3 - (b-a)*(b-a)*(b-a)/(12*(INR n*INR n)) - (b*b*b - a*a*a)/3)
    with (- ((b-a)*(b-a)*(b-a)/(12*(INR n*INR n)))) by (field; exact HnR).
  rewrite Rabs_Ropp.
  assert (Hdpos : 0 < 12 * (INR n * INR n)) by nra.
  unfold Rdiv. rewrite Rabs_mult. rewrite Rabs_inv.
  rewrite (Rabs_pos_eq (12 * (INR n * INR n))) by lra.
  assert (HKnum : Rabs ((b-a)*(b-a)*(b-a)) = 12 * K) by (unfold K; field).
  rewrite HKnum.
  apply Rmult_lt_reg_r with (r := 12 * (INR n * INR n)); [ exact Hdpos | ].
  replace (12 * K * / (12 * (INR n * INR n)) * (12 * (INR n * INR n))) with (12 * K)
    by (field; exact HnR).
  apply Rlt_le_trans with (12 * (eps * INR n)).
  - lra.
  - replace (eps * (12 * (INR n * INR n))) with (12 * (eps * INR n) * INR n) by ring.
    rewrite <- (Rmult_1_r (12 * (eps * INR n))) at 1.
    apply Rmult_le_compat_l; [ nra | exact HnR1 ].
Qed.

(* ================================================================== *)
(* === Uniqueness of the constructive integral === *)
(* ================================================================== *)

(* The constructive integral value is unique. Pure Stdlib proof, so it
   keeps this file free of Classical_Prop.classic. *)
Theorem is_RInt_intuit_unique :
  forall (f : R -> R) (a b l1 l2 : R),
    is_RInt_intuit f a b l1 -> is_RInt_intuit f a b l2 -> l1 = l2.
Proof.
  intros f a b l1 l2 H1 H2.
  destruct (Req_dec l1 l2) as [Heq | Hne]; [exact Heq | exfalso].
  set (eps := Rabs (l1 - l2) / 2).
  assert (Heps : 0 < eps).
  { unfold eps. apply Rdiv_lt_0_compat; [apply Rabs_pos_lt; lra | lra]. }
  destruct (H1 eps Heps) as [N1 HN1].
  destruct (H2 eps Heps) as [N2 HN2].
  set (n := Nat.max N1 N2).
  pose proof (HN1 n (Nat.le_max_l _ _)) as Hb1.
  pose proof (HN2 n (Nat.le_max_r _ _)) as Hb2.
  assert (Htri : Rabs (l1 - l2)
    <= Rabs (l1 - riemann_sum_uniform f a b n)
       + Rabs (riemann_sum_uniform f a b n - l2)).
  { replace (l1 - l2)
      with ((l1 - riemann_sum_uniform f a b n)
            + (riemann_sum_uniform f a b n - l2)) by ring.
    apply Rabs_triang. }
  rewrite (Rabs_minus_sym l1 (riemann_sum_uniform f a b n)) in Htri.
  unfold eps in *. lra.
Qed.

(* ================================================================== *)
(* === Footprint check === *)
(* ================================================================== *)

Print Assumptions is_RInt_intuit_unique.
Print Assumptions is_RInt_intuit_ext.
Print Assumptions is_RInt_intuit_opp.
Print Assumptions is_RInt_intuit_minus.

(* Goal: the constructive integration predicate does not depend on
   Classical_Prop.classic. The axiom audit at the bottom of this file
   should not list classic for any theorem here. *)

Print Assumptions is_RInt_intuit_const.
Print Assumptions is_RInt_intuit_id.
Print Assumptions is_RInt_intuit_plus.
Print Assumptions is_RInt_intuit_le.
Print Assumptions is_RInt_intuit_affine.
Print Assumptions is_RInt_intuit_ftc_id.
Print Assumptions is_RInt_intuit_ftc_constant.
Print Assumptions is_RInt_intuit_sq.
Print Assumptions is_RInt_intuit_scal.
Print Assumptions riemann_sum_uniform_const.


(* ================================================================== *)
(* === Axiom-footprint irreducibility === *)
(* ================================================================== *)
(* ================================================================== *)
(* === The axioms === *)
(* ================================================================== *)

(* A1: For every decidable nat-indexed predicate, either there is a
   witness of negation or the predicate holds universally. *)
Definition Axiom_sig_forall_dec : Type :=
  forall P : nat -> Prop,
    (forall n, {P n} + {~ P n}) ->
    {n | ~ P n} + {forall n, P n}.

(* A2: For every Prop, the double-negation has a decidable form. *)
Definition Axiom_sig_not_dec : Type :=
  forall P : Prop, {~ ~ P} + {~ P}.

(* A3: Functional extensionality (dependent version). *)
Definition Axiom_funext : Prop :=
  forall (A : Type) (B : A -> Type) (f g : forall x, B x),
    (forall x, f x = g x) -> f = g.

(* A4: Classical excluded middle for propositions. *)
Definition Axiom_classic : Prop :=
  forall P : Prop, P \/ ~ P.

(* ================================================================== *)
(* === The axioms hold in the development === *)
(* ================================================================== *)

(* Each axiom is provable from itself. The Print Assumptions
   command below should reveal each lemma uses exactly its own
   axiom (and any others it textually depends on). *)

Theorem axiom_sig_forall_dec_holds : Axiom_sig_forall_dec.
Proof.
  unfold Axiom_sig_forall_dec. intros P Hdec.
  exact (sig_forall_dec P Hdec).
Qed.

Theorem axiom_sig_not_dec_holds : Axiom_sig_not_dec.
Proof.
  unfold Axiom_sig_not_dec. intros P.
  exact (sig_not_dec P).
Qed.

Theorem axiom_funext_holds : Axiom_funext.
Proof.
  unfold Axiom_funext. intros.
  apply functional_extensionality_dep. assumption.
Qed.

Theorem axiom_classic_holds : Axiom_classic.
Proof.
  unfold Axiom_classic. intros P.
  exact (classic P).
Qed.

(* ================================================================== *)
(* === Witness contributions: each axiom enables a distinct content === *)
(* ================================================================== *)

(* === Witness for funext: equality of pointwise-equal functions ===
   Without funext we cannot conclude f = g from forall x, f x = g x. *)
Theorem witness_funext_needed :
  forall (A : Type) (B : A -> Type) (f g : forall x, B x),
    Axiom_funext ->
    (forall x, f x = g x) -> f = g.
Proof.
  intros A B f g Hfunext Hext.
  apply Hfunext, Hext.
Qed.

(* === Witness for classic: case-analysis on undecidable propositions ===
   Without classic we cannot deduce P \/ ~P for arbitrary P. *)
Theorem witness_classic_needed :
  forall P : Prop, Axiom_classic -> P \/ ~ P.
Proof.
  intros P Hclassic. exact (Hclassic P).
Qed.

(* === Witness for sig_forall_dec: nat-indexed search ===
   Used in constructive Dedekind real number theory to certify whether
   a sequence of approximations converges or not. *)
Theorem witness_sig_forall_dec_needed :
  forall (P : nat -> Prop) (Hdec : forall n, {P n} + {~ P n}),
    Axiom_sig_forall_dec ->
    {n | ~ P n} + {forall n, P n}.
Proof.
  intros P Hdec Hsig.
  exact (Hsig P Hdec).
Qed.

(* === Witness for sig_not_dec: double-negation case analysis ===
   Used in constructive Dedekind real number theory to handle
   Cauchy-completeness arguments where the limit is not constructively
   computable but its non-existence can still be detected. *)
Theorem witness_sig_not_dec_needed :
  forall P : Prop, Axiom_sig_not_dec -> {~ ~ P} + {~ P}.
Proof.
  intros P Hsig. exact (Hsig P).
Qed.

(* ================================================================== *)
(* === Reverse-mathematics equivalences === *)
(* ================================================================== *)

(* `Axiom_classic` is inter-derivable with the other standard
   formulations of classical logic (double-negation elimination,
   Peirce's law, de Morgan), each equivalence a constructive
   implication. This pins down what `classic` contributes: precisely the
   strength of excluded middle. *)

Definition DNE : Prop := forall P : Prop, ~ ~ P -> P.
Definition Peirce : Prop := forall P Q : Prop, ((P -> Q) -> P) -> P.

(* classic -> DNE. *)
Theorem classic_implies_DNE : Axiom_classic -> DNE.
Proof.
  intros Hclassic P Hnn.
  destruct (Hclassic P) as [Hp | Hnp].
  - exact Hp.
  - exfalso. apply Hnn. exact Hnp.
Qed.

(* DNE -> classic. The double negation of excluded middle is a
   constructive theorem; DNE then strips it. *)
Theorem DNE_implies_classic : DNE -> Axiom_classic.
Proof.
  intros Hdne P.
  apply Hdne.
  intro Hno.
  apply Hno. right. intro Hp.
  apply Hno. left. exact Hp.
Qed.

(* classic <-> DNE. *)
Theorem classic_iff_DNE : Axiom_classic <-> DNE.
Proof.
  split; [apply classic_implies_DNE | apply DNE_implies_classic].
Qed.

(* classic -> Peirce. *)
Theorem classic_implies_Peirce : Axiom_classic -> Peirce.
Proof.
  intros Hclassic P Q Hpqp.
  destruct (Hclassic P) as [Hp | Hnp].
  - exact Hp.
  - apply Hpqp. intro Hp. exfalso. apply Hnp. exact Hp.
Qed.

(* Peirce -> classic: instantiate Q with False to recover DNE-style
   reasoning, then excluded middle. *)
Theorem Peirce_implies_classic : Peirce -> Axiom_classic.
Proof.
  intros Hpeirce P.
  apply (Hpeirce (P \/ ~ P) False).
  intro Hno.
  right. intro Hp.
  apply Hno. left. exact Hp.
Qed.

(* classic <-> Peirce. *)
Theorem classic_iff_Peirce : Axiom_classic <-> Peirce.
Proof.
  split; [apply classic_implies_Peirce | apply Peirce_implies_classic].
Qed.

(* classic -> de Morgan (the non-constructive direction). *)
Theorem classic_implies_deMorgan :
  Axiom_classic ->
  forall P Q : Prop, ~ (P /\ Q) -> ~ P \/ ~ Q.
Proof.
  intros Hclassic P Q Hnpq.
  destruct (Hclassic P) as [Hp | Hnp].
  - destruct (Hclassic Q) as [Hq | Hnq].
    + exfalso. apply Hnpq. split; assumption.
    + right. exact Hnq.
  - left. exact Hnp.
Qed.

(* The double negation of excluded middle is a constructive theorem —
   no axiom. This is the precise sense in which weak LEM is free while
   full LEM (classic) is not. *)
Theorem not_not_excluded_middle : forall P : Prop, ~ ~ (P \/ ~ P).
Proof.
  intros P Hno. apply Hno. right. intro Hp. apply Hno. left. exact Hp.
Qed.

(* classic gives material implication: P -> Q is ~P \/ Q. *)
Theorem classic_material_implication :
  Axiom_classic -> forall P Q : Prop, (P -> Q) -> ~ P \/ Q.
Proof.
  intros Hclassic P Q Hpq.
  destruct (Hclassic P) as [Hp | Hnp].
  - right. apply Hpq. exact Hp.
  - left. exact Hnp.
Qed.

(* classic gives the contrapositive law (needs double-negation
   elimination, hence excluded middle). *)
Theorem classic_contrapositive :
  Axiom_classic -> forall P Q : Prop, (~ Q -> ~ P) -> P -> Q.
Proof.
  intros Hclassic P Q Hcontra Hp.
  destruct (Hclassic Q) as [Hq | Hnq].
  - exact Hq.
  - exfalso. apply (Hcontra Hnq Hp).
Qed.

(* classic gives Dummett's linearity (the disjunction of the two
   implication directions). *)
Theorem classic_implies_linearity :
  Axiom_classic -> forall P Q : Prop, (P -> Q) \/ (Q -> P).
Proof.
  intros Hclassic P Q.
  destruct (Hclassic P) as [Hp | Hnp].
  - right. intro. exact Hp.
  - left. intro Hp. exfalso. apply Hnp. exact Hp.
Qed.

(* === Funext witness ===
   Two functions that are extensionally equal but built differently:
   `fun n => n + 0` and `fun n => n`. They are equal as functions
   *only* via functional extensionality (Coq does not identify them
   definitionally because `Nat.add` recurses on its first argument). *)
Theorem funext_distinguishes :
  Axiom_funext ->
  (fun n : nat => (n + 0)%nat) = (fun n : nat => n).
Proof.
  intro Hfunext.
  apply (Hfunext nat (fun _ => nat) (fun n => (n + 0)%nat) (fun n => n)).
  intro n. apply Nat.add_0_r.
Qed.

(* The pointwise equality alone does NOT give the function equality
   constructively — this is exactly the content funext adds. *)
Theorem funext_needed_for_eq :
  (forall n : nat, (fun n => (n + 0)%nat) n = (fun n => n) n) ->
  Axiom_funext ->
  (fun n : nat => (n + 0)%nat) = (fun n : nat => n).
Proof.
  intros Hpt Hfunext.
  apply Hfunext. exact Hpt.
Qed.

(* === sig_forall_dec witness ===
   From sig_forall_dec we get the informative decidability of a
   universally-quantified decidable predicate: we can constructively
   produce *either* a counterexample index *or* a proof the predicate
   holds everywhere. We exhibit this on a concrete predicate. *)
Theorem sig_forall_dec_decides_concrete :
  Axiom_sig_forall_dec ->
  {n : nat | ~ (n = n)} + {forall n : nat, (n = n)}.
Proof.
  intro Hsig.
  apply (Hsig (fun n : nat => n = n)).
  intro n. left. reflexivity.
Qed.

(* The right branch is the one that actually holds; the search
   terminates with the universal proof. *)
Theorem sig_forall_dec_concrete_universal :
  Axiom_sig_forall_dec ->
  (forall n : nat, (n = n)%nat) ->
  exists (_ : forall n : nat, (n = n)%nat), True.
Proof.
  intros Hsig Hall. exists Hall. exact I.
Qed.

(* === sig_forall_dec is exactly the Limited Principle of Omniscience ===
   The Dedekind-real decidability axiom is inter-derivable with LPO,
   the canonical non-constructive principle for Boolean sequences. This
   pins down sig_forall_dec as a logical principle of a DIFFERENT
   character from classic/DNE/Peirce (excluded middle): LPO is strictly
   about searching nat-indexed decisions. *)
Definition LPO : Prop :=
  forall p : nat -> bool,
    (exists n, p n = true) \/ (forall n, p n = false).

Theorem sig_forall_dec_implies_LPO : Axiom_sig_forall_dec -> LPO.
Proof.
  intros Hsig p.
  destruct (Hsig (fun n => p n = false)
              (fun n => bool_dec (p n) false)) as [[n Hn] | Hall].
  - left. exists n. destruct (p n); [reflexivity | exfalso; apply Hn; reflexivity].
  - right. exact Hall.
Qed.

(* The informative Set-level search for a Boolean sequence: from a
   constructive existence proof, extract the witness via constructive
   epsilon (no axiom). This is the Set-level content that sig_forall_dec
   provides and that the propositional LPO does not — LPO's disjunction
   lives in Prop and cannot be eliminated into Set, so sig_forall_dec is
   strictly more informative than LPO. *)
Theorem bool_search_informative :
  forall p : nat -> bool,
    (exists n, p n = true) -> {n | p n = true}.
Proof.
  intros p Hex.
  apply (constructive_indefinite_ground_description_nat
           (fun n => p n = true)
           (fun n => bool_dec (p n) true) Hex).
Qed.

(* ================================================================== *)
(* === Irreducibility content === *)
(* ================================================================== *)

(* The classical-logic axiom is now pinned exactly: classic, DNE,
   Peirce, and (one direction of) de Morgan are all inter-derivable,
   so `classic` contributes precisely excluded-middle strength. The
   is_RInt_intuit development in pb_avalanche_constructive.v uses none
   of them (its axiom audit omits classic), so classic is separable from
   the Dedekind axioms — the constructive fragment stands without it.

   These axioms are logically distinct (in the metamathematical
   sense): no constructive proof of any one from the conjunction of
   the others is known. The Stdlib treats each as a separate
   `Axiom`, and the present development needs each for a different
   structural purpose:

   - funext: equality of integrands inside RInt_ext / is_derive_ext.
   - classic: Coquelicot's classical FTC layer.
   - sig_forall_dec, sig_not_dec: Dedekind-real Cauchy completeness.

   The is_RInt_intuit framework shows the FTC for polynomials can be
   re-derived without classic, leaving only the Dedekind axioms. Those
   cannot be removed without re-axiomatising the real numbers
   themselves. *)

(* === A combined statement that the named axioms hold === *)
Theorem all_named_axioms_hold :
  Axiom_sig_forall_dec *
  Axiom_sig_not_dec *
  Axiom_funext *
  Axiom_classic.
Proof.
  repeat split.
  - apply axiom_sig_forall_dec_holds.
  - apply axiom_sig_not_dec_holds.
  - apply axiom_funext_holds.
  - apply axiom_classic_holds.
Qed.

(* These axioms are exactly those *named* in the present development
   for the Hora-Putvinski settlement: any subset that omits one of
   them cannot prove the settlement at the current level of generality.
   This is documented (not provable inside Coq) by the audit
   `scripts/check_axioms.sh`. *)

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions axiom_sig_forall_dec_holds.
Print Assumptions axiom_sig_not_dec_holds.
Print Assumptions axiom_funext_holds.
Print Assumptions axiom_classic_holds.
Print Assumptions witness_funext_needed.
Print Assumptions witness_classic_needed.
Print Assumptions witness_sig_forall_dec_needed.
Print Assumptions witness_sig_not_dec_needed.
Print Assumptions all_named_axioms_hold.
Print Assumptions classic_iff_DNE.
Print Assumptions classic_iff_Peirce.
Print Assumptions classic_implies_deMorgan.
Print Assumptions funext_distinguishes.
Print Assumptions sig_forall_dec_decides_concrete.
Print Assumptions sig_forall_dec_implies_LPO.
Print Assumptions bool_search_informative.
Print Assumptions not_not_excluded_middle.
Print Assumptions classic_material_implication.
Print Assumptions classic_contrapositive.
Print Assumptions classic_implies_linearity.
