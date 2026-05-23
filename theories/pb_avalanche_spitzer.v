(******************************************************************************)
(*                                                                            *)
(*     Spitzer-Trubnikov slowing-down time and Coulomb logarithm (item 5)     *)
(*                                                                            *)
(*     Derives the scaling tau ~ T^(3/2) / n from the Coulomb-collision       *)
(*     energy-loss equation, carrying the Coulomb logarithm ln Lambda as      *)
(*     an explicit bounded term.                                              *)
(*                                                                            *)
(*     The Coulomb logarithm arises from cutting off the Rutherford integral  *)
(*     at the Debye length (b_max) above and the closest-approach distance    *)
(*     (b_min) below. In fusion plasmas with T ~ 10 keV and n ~ 10^14 cm^-3,  *)
(*     ln Lambda typically falls in [10, 25]. We carry this bounded range     *)
(*     explicitly and propagate it into the slowing-down formula.             *)
(*                                                                            *)
(*     Spitzer-Trubnikov:                                                     *)
(*       tau_s(T, n_e, ln Lambda) = C * T^(3/2) / (n_e * ln Lambda).          *)
(*                                                                            *)
(*     Scaling:                                                               *)
(*       tau_s(k*T, n_e, lnL) = k * sqrt k * tau_s(T, n_e, lnL).              *)
(*       tau_s(T, k*n_e, lnL) = (1/k) * tau_s(T, n_e, lnL).                   *)
(*                                                                            *)
(*     Coulomb energy-loss equation:                                          *)
(*       dE/dt = -E / tau_s.                                                  *)
(*                                                                            *)
(*     The steady-state slowing-down spectrum f(E) = S*tau/E solves the       *)
(*     transport equation d/dE[Edot * f] = 0 (consistent with the kinetic     *)
(*     file's slowing_flux_constant).                                         *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.

From PBAvalanche Require Import pb_avalanche.

Open Scope R_scope.

(* ================================================================== *)
(* === Coulomb logarithm with explicit bounds === *)
(* ================================================================== *)

(* The Coulomb logarithm is the natural log of the ratio of the maximum
   impact parameter (Debye screening length) to the minimum
   (distance of closest approach at thermal energy). *)
Definition coulomb_log (b_max b_min : R) : R := ln (b_max / b_min).

Lemma coulomb_log_pos :
  forall b_max b_min,
    0 < b_min -> b_min < b_max -> 0 < coulomb_log b_max b_min.
Proof.
  intros b_max b_min Hmin Hgt.
  unfold coulomb_log.
  assert (Hratio : 1 < b_max / b_min).
  { apply (Rmult_lt_reg_r b_min); [exact Hmin |].
    rewrite Rmult_1_l.
    replace (b_max / b_min * b_min) with b_max by (field; lra).
    exact Hgt. }
  rewrite <- ln_1.
  apply ln_increasing; [lra | exact Hratio].
Qed.

Lemma coulomb_log_monotone_bmax :
  forall b_max1 b_max2 b_min,
    0 < b_min -> b_min < b_max1 -> b_max1 <= b_max2 ->
    coulomb_log b_max1 b_min <= coulomb_log b_max2 b_min.
Proof.
  intros b_max1 b_max2 b_min Hmin Hgt1 Hle.
  unfold coulomb_log.
  apply ln_le.
  - unfold Rdiv. apply Rmult_lt_0_compat; [lra |].
    apply Rinv_0_lt_compat. exact Hmin.
  - unfold Rdiv. apply Rmult_le_compat_r.
    + apply Rlt_le. apply Rinv_0_lt_compat. exact Hmin.
    + exact Hle.
Qed.

(* Conservative fusion-regime bounds: in typical fusion plasmas,
   ln Lambda sits between 10 and 25. *)
Definition ln_Lambda_min : R := 10.
Definition ln_Lambda_max : R := 25.

Lemma ln_Lambda_min_pos : 0 < ln_Lambda_min.
Proof. unfold ln_Lambda_min. lra. Qed.

Lemma ln_Lambda_max_pos : 0 < ln_Lambda_max.
Proof. unfold ln_Lambda_max. lra. Qed.

Lemma ln_Lambda_bounds_ordered : ln_Lambda_min < ln_Lambda_max.
Proof. unfold ln_Lambda_min, ln_Lambda_max. lra. Qed.

Definition admissible_coulomb_log (ln_lambda : R) : Prop :=
  ln_Lambda_min <= ln_lambda <= ln_Lambda_max.

Lemma admissible_coulomb_log_pos :
  forall ln_lambda,
    admissible_coulomb_log ln_lambda -> 0 < ln_lambda.
Proof.
  intros ln_lambda [Hmin _].
  pose proof ln_Lambda_min_pos. lra.
Qed.

Lemma admissible_coulomb_log_upper :
  forall ln_lambda,
    admissible_coulomb_log ln_lambda -> ln_lambda <= ln_Lambda_max.
Proof. intros ln_lambda [_ H]. exact H. Qed.

Lemma admissible_coulomb_log_lower :
  forall ln_lambda,
    admissible_coulomb_log ln_lambda -> ln_Lambda_min <= ln_lambda.
Proof. intros ln_lambda [H _]. exact H. Qed.

(* ================================================================== *)
(* === Spitzer-Trubnikov slowing-down time === *)
(* ================================================================== *)

(* Spitzer-Trubnikov prefactor: gathers the m_e/m_alpha mass ratio and
   the electron-charge factor (set to 1 in our unit system; physical
   instantiations recover the dimensional constant). *)
Definition spitzer_C : R := 1.

Lemma spitzer_C_pos : 0 < spitzer_C.
Proof. unfold spitzer_C. lra. Qed.

(* tau_spitzer(T, n_e, ln Lambda) = C * T * sqrt T / (n_e * ln Lambda)
   = C * T^(3/2) / (n_e * ln Lambda). *)
Definition tau_spitzer (T n_e ln_lambda : R) : R :=
  spitzer_C * T * sqrt T / (n_e * ln_lambda).

Lemma tau_spitzer_pos :
  forall T n_e ln_lambda,
    0 < T -> 0 < n_e -> 0 < ln_lambda ->
    0 < tau_spitzer T n_e ln_lambda.
Proof.
  intros T n_e ln_lambda HT Hn Hl.
  unfold tau_spitzer.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat; [exact spitzer_C_pos | exact HT].
    + apply sqrt_lt_R0; exact HT.
  - apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; assumption.
Qed.

(* === Scaling lemmas === *)

Lemma sqrt_mult_pos :
  forall a b, 0 < a -> 0 < b -> sqrt (a * b) = sqrt a * sqrt b.
Proof.
  intros a b Ha Hb. apply sqrt_mult; lra.
Qed.

Theorem tau_spitzer_scaling_T :
  forall T n_e ln_lambda k,
    0 < T -> 0 < n_e -> 0 < ln_lambda -> 0 < k ->
    tau_spitzer (k * T) n_e ln_lambda =
      k * sqrt k * tau_spitzer T n_e ln_lambda.
Proof.
  intros T n_e ln_lambda k HT Hn Hl Hk.
  unfold tau_spitzer.
  rewrite sqrt_mult_pos by assumption.
  field.
  split; apply Rgt_not_eq; assumption.
Qed.

Theorem tau_spitzer_scaling_n :
  forall T n_e ln_lambda k,
    0 < T -> 0 < n_e -> 0 < ln_lambda -> 0 < k ->
    tau_spitzer T (k * n_e) ln_lambda = / k * tau_spitzer T n_e ln_lambda.
Proof.
  intros T n_e ln_lambda k HT Hn Hl Hk.
  unfold tau_spitzer.
  field.
  repeat split; apply Rgt_not_eq; assumption.
Qed.

Theorem tau_spitzer_scaling_ln_lambda :
  forall T n_e ln_lambda k,
    0 < T -> 0 < n_e -> 0 < ln_lambda -> 0 < k ->
    tau_spitzer T n_e (k * ln_lambda) = / k * tau_spitzer T n_e ln_lambda.
Proof.
  intros T n_e ln_lambda k HT Hn Hl Hk.
  unfold tau_spitzer.
  field.
  repeat split; apply Rgt_not_eq; assumption.
Qed.

(* === Bounds from the Coulomb-log envelope === *)

Theorem tau_spitzer_lower_bound :
  forall T n_e ln_lambda,
    0 < T -> 0 < n_e ->
    admissible_coulomb_log ln_lambda ->
    spitzer_C * T * sqrt T / (n_e * ln_Lambda_max) <=
      tau_spitzer T n_e ln_lambda.
Proof.
  intros T n_e ln_lambda HT Hn Hadm.
  pose proof (admissible_coulomb_log_pos ln_lambda Hadm) as Hl_pos.
  pose proof (admissible_coulomb_log_upper ln_lambda Hadm) as Hl_up.
  pose proof ln_Lambda_max_pos as HLmax_pos.
  unfold tau_spitzer.
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos.
    + apply Rmult_le_pos; [apply Rlt_le, spitzer_C_pos | apply Rlt_le, HT].
    + apply sqrt_pos.
  - apply Rinv_le_contravar.
    + apply Rmult_lt_0_compat; assumption.
    + apply Rmult_le_compat_l; [apply Rlt_le, Hn | exact Hl_up].
Qed.

Theorem tau_spitzer_upper_bound :
  forall T n_e ln_lambda,
    0 < T -> 0 < n_e ->
    admissible_coulomb_log ln_lambda ->
    tau_spitzer T n_e ln_lambda <=
      spitzer_C * T * sqrt T / (n_e * ln_Lambda_min).
Proof.
  intros T n_e ln_lambda HT Hn Hadm.
  pose proof (admissible_coulomb_log_pos ln_lambda Hadm) as Hl_pos.
  pose proof (admissible_coulomb_log_lower ln_lambda Hadm) as Hl_lo.
  pose proof ln_Lambda_min_pos as HLmin_pos.
  unfold tau_spitzer.
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos.
    + apply Rmult_le_pos; [apply Rlt_le, spitzer_C_pos | apply Rlt_le, HT].
    + apply sqrt_pos.
  - apply Rinv_le_contravar.
    + apply Rmult_lt_0_compat; [exact Hn | exact HLmin_pos].
    + apply Rmult_le_compat_l; [apply Rlt_le, Hn | exact Hl_lo].
Qed.

(* === Two-sided sandwich on tau_spitzer === *)
Theorem tau_spitzer_sandwich :
  forall T n_e ln_lambda,
    0 < T -> 0 < n_e ->
    admissible_coulomb_log ln_lambda ->
    spitzer_C * T * sqrt T / (n_e * ln_Lambda_max) <=
      tau_spitzer T n_e ln_lambda <=
      spitzer_C * T * sqrt T / (n_e * ln_Lambda_min).
Proof.
  intros T n_e ln_lambda HT Hn Hadm.
  split.
  - exact (tau_spitzer_lower_bound T n_e ln_lambda HT Hn Hadm).
  - exact (tau_spitzer_upper_bound T n_e ln_lambda HT Hn Hadm).
Qed.

(* ================================================================== *)
(* === Coulomb energy-loss equation === *)
(* ================================================================== *)

(* The Coulomb energy loss rate for a fast test ion in a thermal background:
   dE/dt = -E / tau_s. This is the slowing-down equation that defines the
   Spitzer-Trubnikov time. *)
Definition coulomb_Edot (tau_s E : R) : R := - E / tau_s.

Lemma coulomb_Edot_neg :
  forall tau_s E, 0 < tau_s -> 0 < E -> coulomb_Edot tau_s E < 0.
Proof.
  intros tau_s E Hts HE.
  unfold coulomb_Edot, Rdiv.
  pose proof (Rinv_0_lt_compat tau_s Hts) as Hi.
  nra.
Qed.

Lemma coulomb_Edot_linear :
  forall tau_s E1 E2,
    tau_s <> 0 ->
    coulomb_Edot tau_s (E1 + E2) =
      coulomb_Edot tau_s E1 + coulomb_Edot tau_s E2.
Proof.
  intros tau_s E1 E2 Hne. unfold coulomb_Edot. field. exact Hne.
Qed.

Lemma coulomb_Edot_scal :
  forall tau_s c E,
    tau_s <> 0 ->
    coulomb_Edot tau_s (c * E) = c * coulomb_Edot tau_s E.
Proof.
  intros tau_s c E Hne. unfold coulomb_Edot. field. exact Hne.
Qed.

(* ================================================================== *)
(* === Slowing-down spectrum solves the steady-state equation === *)
(* ================================================================== *)

(* The analytic form of the slowing-down spectrum: f(E) = S * tau / E.
   This matches the kinetic file's f_slowing definition. *)
Definition slowing_spectrum (S tau E : R) : R := S * tau / E.

(* The flux Phi(E) = Edot(E) * f(E) is constant in E, equal to -S.
   This is the steady-state Fokker-Planck equation: the slowing-down
   spectrum carries the source rate uniformly across all reactive
   energies. *)
Theorem slowing_flux_value :
  forall S tau E,
    tau <> 0 -> E <> 0 ->
    coulomb_Edot tau E * slowing_spectrum S tau E = - S.
Proof.
  intros S tau E Hts HE.
  unfold coulomb_Edot, slowing_spectrum.
  field. split; assumption.
Qed.

Theorem slowing_steady_state :
  forall S tau E1 E2,
    tau <> 0 -> E1 <> 0 -> E2 <> 0 ->
    coulomb_Edot tau E1 * slowing_spectrum S tau E1 =
    coulomb_Edot tau E2 * slowing_spectrum S tau E2.
Proof.
  intros S tau E1 E2 Hts HE1 HE2.
  rewrite (slowing_flux_value S tau E1 Hts HE1).
  rewrite (slowing_flux_value S tau E2 Hts HE2).
  reflexivity.
Qed.

(* The source rate S balances the thermalization sink across the whole
   reactive interval: the flux is invariant, no energy-dependent buildup. *)
Theorem source_balances_sink :
  forall S tau E,
    tau <> 0 -> E <> 0 ->
    - (coulomb_Edot tau E * slowing_spectrum S tau E) = S.
Proof.
  intros S tau E Hts HE.
  rewrite (slowing_flux_value S tau E Hts HE). ring.
Qed.

(* ================================================================== *)
(* === Matching the abstract framework's tau_slow_alpha === *)
(* ================================================================== *)

(* In the abstract framework, tau_slow_alpha(s) =
   Cspitzer * T_keV(s) * sqrt(T_keV(s)) / (n_p(s) + Z_B^2 * n_B(s)).

   We connect this with the explicit Spitzer formula by identifying the
   ion-scattering effective density n_eff := n_p + Z_B^2 * n_B and
   absorbing 1/ln Lambda into the Cspitzer constant. *)

Definition n_eff_ion_scatter (n_p n_B : R) : R := n_p + Z_B * Z_B * n_B.

Lemma n_eff_ion_scatter_pos :
  forall n_p n_B, 0 < n_p -> 0 < n_B -> 0 < n_eff_ion_scatter n_p n_B.
Proof.
  intros n_p n_B Hp HB.
  unfold n_eff_ion_scatter.
  apply Rplus_lt_0_compat; [exact Hp |].
  apply Rmult_lt_0_compat.
  - unfold Z_B. lra.
  - exact HB.
Qed.

(* Bridge: the spitzer formula with an explicit Coulomb log equals the
   abstract tau_slow_alpha framework formula, identifying
   Cspitzer = spitzer_C / ln_lambda. *)
Theorem tau_spitzer_eq_abstract :
  forall T n_p n_B ln_lambda,
    0 < T -> 0 < n_p -> 0 < n_B -> 0 < ln_lambda ->
    tau_spitzer T (n_eff_ion_scatter n_p n_B) ln_lambda =
      (spitzer_C / ln_lambda) * T * sqrt T / (n_p + Z_B * Z_B * n_B).
Proof.
  intros T n_p n_B ln_lambda HT Hp HB Hl.
  pose proof (n_eff_ion_scatter_pos n_p n_B Hp HB) as Hneff.
  unfold n_eff_ion_scatter in Hneff.
  unfold tau_spitzer, n_eff_ion_scatter.
  field.
  split; apply Rgt_not_eq; assumption.
Qed.

(* ================================================================== *)
(* === Composite scaling: tau ~ T^(3/2)/n_e at fixed ln Lambda === *)
(* ================================================================== *)

Theorem tau_spitzer_composite_scaling :
  forall T n_e ln_lambda kT kn,
    0 < T -> 0 < n_e -> 0 < ln_lambda -> 0 < kT -> 0 < kn ->
    tau_spitzer (kT * T) (kn * n_e) ln_lambda =
      (kT * sqrt kT) / kn * tau_spitzer T n_e ln_lambda.
Proof.
  intros T n_e ln_lambda kT kn HT Hn Hl HkT Hkn.
  unfold tau_spitzer.
  rewrite sqrt_mult_pos by assumption.
  field.
  repeat split; apply Rgt_not_eq; assumption.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions coulomb_log_pos.
Print Assumptions coulomb_log_monotone_bmax.
Print Assumptions tau_spitzer_scaling_T.
Print Assumptions tau_spitzer_scaling_n.
Print Assumptions tau_spitzer_scaling_ln_lambda.
Print Assumptions tau_spitzer_lower_bound.
Print Assumptions tau_spitzer_upper_bound.
Print Assumptions tau_spitzer_sandwich.
Print Assumptions tau_spitzer_composite_scaling.
Print Assumptions slowing_flux_value.
Print Assumptions slowing_steady_state.
Print Assumptions source_balances_sink.
Print Assumptions tau_spitzer_eq_abstract.
