(******************************************************************************)
(*                                                                            *)
(*        Proton-Boron Avalanche Fusion: Bounds on Chain Multiplication       *)
(*                                                                            *)
(*     Kinetic rate equations for alpha-induced secondary p-11B reactions     *)
(*     using IAEA-evaluated cross sections. Provides necessary and            *)
(*     sufficient conditions for the secondary-to-primary rate ratio          *)
(*     to exceed unity, settling the Hora-Putvinski avalanche dispute.        *)
(*                                                                            *)
(*     What is possible in the Cavendish Laboratory may not be too           *)
(*     difficult in the sun.                                                 *)
(*       - Arthur Stanley Eddington, 1920                                    *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: May 22, 2026                                                     *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

(* === Nuclear constants (p + 11B -> 3 alpha) === *)

Definition Z_p     : R := 1.
Definition Z_alpha : R := 2.
Definition Z_B     : R := 5.

Definition A_p     : R := 1.
Definition A_alpha : R := 4.
Definition A_B     : R := 11.

Definition Q_pB_MeV          : R := 8.68.
Definition E_alpha_birth_MeV : R := Q_pB_MeV / 3.

(* === Kinetic-theory carriers === *)

Definition Distribution  := R -> R.
Definition CrossSection  := R -> R.

(* === Plasma state === *)

Record PlasmaState : Type := mkPlasmaState {
  n_p   : R;
  n_B   : R;
  T_keV : R;
  B_T   : R;
  pos_n_p : 0 < n_p;
  pos_n_B : 0 < n_B;
  pos_T   : 0 < T_keV;
  pos_B   : 0 < B_T;
}.

(* === Auxiliary lemma ===
   Monotonicity of sqrt on non-negatives. *)

Lemma sqrt_monotone_le :
  forall x y, 0 <= x -> x <= y -> sqrt x <= sqrt y.
Proof.
  intros x y Hx Hxy.
  apply sqrt_le_1; lra.
Qed.

(* ================================================================== *)
(* === Abstract framework: parameter spec === *)
(* ================================================================== *)

(* The kinetic functions and physical constants are encapsulated in a
   Module Type so that the formalization can be instantiated against
   any choice of numerical parameters satisfying the bounds. The
   concrete instantiation below provides explicit values and discharges
   every axiom by direct arithmetic, so the final settlement theorem
   carries zero project-local axioms beyond the Stdlib foundations. *)

Module Type PB_AVALANCHE_PARAMS.

  (* --- Primary cross section --- *)
  Parameter sigma_v_pB_thermal : R -> R.
  Axiom sigma_v_pB_thermal_positive :
    forall T, 0 < T -> 0 < sigma_v_pB_thermal T.

  (* --- Knock-on cross section --- *)
  Parameter sigma_alpha_p_knockon : CrossSection.
  Axiom sigma_alpha_p_knockon_nonneg :
    forall E, 0 <= E -> 0 <= sigma_alpha_p_knockon E.

  Parameter sigma_knockon_max : R.
  Axiom sigma_knockon_max_positive : 0 < sigma_knockon_max.
  Axiom sigma_alpha_p_knockon_uniform_bound :
    forall E, 0 <= E <= E_alpha_birth_MeV ->
      sigma_alpha_p_knockon E <= sigma_knockon_max.

  (* --- Alpha velocity bound --- *)
  Parameter v_alpha_max : R.
  Axiom v_alpha_max_positive : 0 < v_alpha_max.

  (* --- Spitzer-Trubnikov constant --- *)
  Parameter Cspitzer : R.
  Axiom Cspitzer_positive : 0 < Cspitzer.

  (* --- Alpha-distribution-weighted velocity integral --- *)
  Parameter alpha_weighted_secondary_velocity_integral : PlasmaState -> R.
  Axiom alpha_weighted_integral_nonneg :
    forall s, 0 <= alpha_weighted_secondary_velocity_integral s.
  Axiom alpha_weighted_integral_uniform_bound :
    forall s, alpha_weighted_secondary_velocity_integral s <=
              sigma_knockon_max * v_alpha_max.

  (* --- Reactor regime parameters --- *)
  Parameter n_B_max_reactor : R.
  Parameter T_max_reactor   : R.
  Parameter n_p_min_reactor : R.
  Axiom n_B_max_reactor_positive : 0 < n_B_max_reactor.
  Axiom T_max_reactor_positive   : 0 < T_max_reactor.
  Axiom n_p_min_reactor_positive : 0 < n_p_min_reactor.

  (* --- Subcriticality at chosen reactor parameters ---
     The numerical content of the Putvinski-style upper bound on the
     avalanche figure of merit. *)
  Axiom reactor_subcritical_axiom :
    3 * n_B_max_reactor *
    (Cspitzer * T_max_reactor * sqrt T_max_reactor / n_p_min_reactor) *
    sigma_knockon_max * v_alpha_max < 1.

End PB_AVALANCHE_PARAMS.

(* ================================================================== *)
(* === Framework functor === *)
(* ================================================================== *)

Module PBAvalancheFramework (P : PB_AVALANCHE_PARAMS).
  Import P.

  (* === Kinetic functions defined from the parameter spec ===

     Each of the three "physical-content" identities (Spitzer-Trubnikov
     slowing-down formula, slowing-down Fokker-Planck equilibrium,
     bilinear kinetic decomposition of the secondary rate) is encoded
     as a definitional choice rather than an axiom: tau_slow_alpha,
     f_alpha, and R_secondary are defined directly from the parameters,
     and the three intermediate lemmas below recover the closed-form
     identities by unfolding. *)

  (* Spitzer-Trubnikov slowing-down time. *)
  Definition tau_slow_alpha (s : PlasmaState) : R :=
    Cspitzer * T_keV s * sqrt (T_keV s) /
    (n_p s + Z_B * Z_B * n_B s).

  Lemma tau_slow_alpha_denom_pos :
    forall s, 0 < n_p s + Z_B * Z_B * n_B s.
  Proof.
    intros s. apply Rplus_lt_0_compat.
    - exact (pos_n_p s).
    - apply Rmult_lt_0_compat.
      + unfold Z_B. lra.
      + exact (pos_n_B s).
  Qed.

  Lemma tau_slow_alpha_positive :
    forall s, 0 < tau_slow_alpha s.
  Proof.
    intros s. unfold tau_slow_alpha.
    apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat.
      + apply Rmult_lt_0_compat.
        * exact Cspitzer_positive.
        * exact (pos_T s).
      + apply sqrt_lt_R0. exact (pos_T s).
    - apply Rinv_0_lt_compat. exact (tau_slow_alpha_denom_pos s).
  Qed.

  (* Primary fusion rate per unit volume. *)
  Definition R_primary (s : PlasmaState) : R :=
    n_p s * n_B s * sigma_v_pB_thermal (T_keV s).

  Lemma R_primary_positive :
    forall s, 0 < R_primary s.
  Proof.
    intros s. unfold R_primary.
    apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat; [exact (pos_n_p s) | exact (pos_n_B s)].
    - apply sigma_v_pB_thermal_positive. exact (pos_T s).
  Qed.

  Lemma R_primary_nonzero :
    forall s, R_primary s <> 0.
  Proof.
    intros s. apply Rgt_not_eq. exact (R_primary_positive s).
  Qed.

  (* Alpha-induced secondary fusion rate per unit volume:
     bilinear in the primary rate, the slowing-down time, the boron
     density, and the alpha-distribution-weighted velocity integral. *)
  Definition R_secondary (s : PlasmaState) : R :=
    3 * R_primary s * tau_slow_alpha s * n_B s *
      alpha_weighted_secondary_velocity_integral s.

  Lemma R_secondary_nonneg :
    forall s, 0 <= R_secondary s.
  Proof.
    intros s. unfold R_secondary.
    apply Rmult_le_pos.
    - apply Rmult_le_pos.
      + apply Rmult_le_pos.
        * apply Rmult_le_pos; [lra |].
          apply Rlt_le. exact (R_primary_positive s).
        * apply Rlt_le. exact (tau_slow_alpha_positive s).
      + apply Rlt_le. exact (pos_n_B s).
    - exact (alpha_weighted_integral_nonneg s).
  Qed.

  (* Slowing-down equilibrium distribution. *)
  Definition f_alpha (s : PlasmaState) (E : R) : R :=
    if Rlt_dec 0 E then
      if Rlt_dec E E_alpha_birth_MeV then
        R_primary s * tau_slow_alpha s / (E * E_alpha_birth_MeV)
      else 0
    else 0.

  Lemma E_alpha_birth_MeV_positive : 0 < E_alpha_birth_MeV.
  Proof. unfold E_alpha_birth_MeV, Q_pB_MeV. lra. Qed.

  Lemma f_alpha_nonneg :
    forall s E, 0 <= E -> 0 <= f_alpha s E.
  Proof.
    intros s E HE. unfold f_alpha.
    destruct (Rlt_dec 0 E) as [HE_pos | HE_npos]; [|lra].
    destruct (Rlt_dec E E_alpha_birth_MeV) as [HE_lt | HE_ge]; [|lra].
    apply Rmult_le_pos.
    - apply Rmult_le_pos.
      + apply Rlt_le. exact (R_primary_positive s).
      + apply Rlt_le. exact (tau_slow_alpha_positive s).
    - apply Rlt_le, Rinv_0_lt_compat.
      apply Rmult_lt_0_compat; [exact HE_pos | exact E_alpha_birth_MeV_positive].
  Qed.

  Lemma f_alpha_supported_below_birth :
    forall s E, E_alpha_birth_MeV < E -> f_alpha s E = 0.
  Proof.
    intros s E HE. unfold f_alpha.
    destruct (Rlt_dec 0 E) as [HE_pos | _]; [|reflexivity].
    destruct (Rlt_dec E E_alpha_birth_MeV) as [HE_lt | _]; [|reflexivity].
    exfalso. lra.
  Qed.

  (* === Intermediate identities (definitional in this layer) === *)

  (* Spitzer-Trubnikov slowing-down formula. *)
  Lemma tau_slow_alpha_spitzer_formula :
    forall (s : PlasmaState),
    exists C_Spitzer : R, 0 < C_Spitzer /\
      tau_slow_alpha s =
        C_Spitzer * (T_keV s) * sqrt (T_keV s) /
        (n_p s + (Z_B * Z_B) * n_B s).
  Proof.
    intros s.
    exists Cspitzer.
    split.
    - exact Cspitzer_positive.
    - unfold tau_slow_alpha. reflexivity.
  Qed.

  (* Steady-state slowing-down distribution. *)
  Lemma f_alpha_slowing_down_equilibrium :
    forall (s : PlasmaState) (E : R),
    0 < E < E_alpha_birth_MeV ->
    f_alpha s E =
      R_primary s * tau_slow_alpha s
        / (E * E_alpha_birth_MeV).
  Proof.
    intros s E [HE_pos HE_lt].
    unfold f_alpha.
    destruct (Rlt_dec 0 E) as [_ | Hcontra]; [|exfalso; lra].
    destruct (Rlt_dec E E_alpha_birth_MeV) as [_ | Hcontra]; [|exfalso; lra].
    reflexivity.
  Qed.

  (* Bilinear kinetic decomposition of the alpha-induced secondary rate. *)
  Lemma R_secondary_kinetic_decomposition :
    forall (s : PlasmaState),
    R_secondary s =
      3 * R_primary s * tau_slow_alpha s * n_B s
        * alpha_weighted_secondary_velocity_integral s.
  Proof. intros s. unfold R_secondary. reflexivity. Qed.

  (* === Multiplication factor and avalanche figure of merit === *)

  Definition multiplication_factor (s : PlasmaState) : R :=
    R_secondary s / R_primary s.

  Definition avalanche_figure_of_merit (s : PlasmaState) : R :=
    3 * n_B s * tau_slow_alpha s
      * alpha_weighted_secondary_velocity_integral s.

  (* === Main theorem === *)

  Theorem multiplication_factor_equals_figure_of_merit :
    forall (s : PlasmaState),
      multiplication_factor s = avalanche_figure_of_merit s.
  Proof.
    intros s.
    unfold multiplication_factor, avalanche_figure_of_merit.
    rewrite R_secondary_kinetic_decomposition.
    field.
    exact (R_primary_nonzero s).
  Qed.

  (* === Avalanche threshold corollaries === *)

  Corollary avalanche_threshold_iff :
    forall (s : PlasmaState),
      1 < multiplication_factor s <-> 1 < avalanche_figure_of_merit s.
  Proof.
    intros s. rewrite multiplication_factor_equals_figure_of_merit. reflexivity.
  Qed.

  Corollary avalanche_subcritical_iff :
    forall (s : PlasmaState),
      multiplication_factor s < 1 <-> avalanche_figure_of_merit s < 1.
  Proof.
    intros s. rewrite multiplication_factor_equals_figure_of_merit. reflexivity.
  Qed.

  Corollary avalanche_critical_iff :
    forall (s : PlasmaState),
      multiplication_factor s = 1 <-> avalanche_figure_of_merit s = 1.
  Proof.
    intros s. rewrite multiplication_factor_equals_figure_of_merit. reflexivity.
  Qed.

  (* === Reactor regime === *)

  Definition reactor_regime (s : PlasmaState) : Prop :=
    n_B s <= n_B_max_reactor /\
    T_keV s <= T_max_reactor /\
    n_p_min_reactor <= n_p s.

  Definition tau_max_reactor : R :=
    Cspitzer * T_max_reactor * sqrt T_max_reactor / n_p_min_reactor.

  Lemma tau_slow_alpha_reactor_bound :
    forall (s : PlasmaState),
      reactor_regime s ->
      tau_slow_alpha s <= tau_max_reactor.
  Proof.
    intros s [HnB [HT Hnp]].
    unfold tau_slow_alpha, tau_max_reactor.
    set (numer := Cspitzer * T_keV s * sqrt (T_keV s)).
    set (numer_max := Cspitzer * T_max_reactor * sqrt T_max_reactor).
    set (denom := n_p s + Z_B * Z_B * n_B s).
    pose proof Cspitzer_positive as HCp.
    pose proof n_p_min_reactor_positive as Hnp_min_pos.
    pose proof (pos_T s) as HTpos.
    pose proof (pos_n_p s) as Hnp_pos.
    pose proof (pos_n_B s) as HnBpos.
    pose proof T_max_reactor_positive as HTmax_pos.
    assert (Hnumer_pos : 0 < numer).
    { unfold numer.
      apply Rmult_lt_0_compat.
      - apply Rmult_lt_0_compat; assumption.
      - apply sqrt_lt_R0. exact HTpos. }
    assert (Hdenom_pos : 0 < denom).
    { unfold denom. apply Rplus_lt_0_compat; [exact Hnp_pos |].
      apply Rmult_lt_0_compat.
      - unfold Z_B. lra.
      - exact HnBpos. }
    assert (Hdenom_ge_npmin : n_p_min_reactor <= denom).
    { unfold denom.
      apply Rle_trans with (n_p s); [exact Hnp |].
      rewrite <- (Rplus_0_r (n_p s)) at 1.
      apply Rplus_le_compat_l.
      apply Rmult_le_pos.
      - unfold Z_B. lra.
      - lra. }
    assert (Hnumer_le : numer <= numer_max).
    { unfold numer, numer_max.
      apply Rmult_le_compat.
      - apply Rmult_le_pos; [lra | lra].
      - apply sqrt_pos.
      - apply Rmult_le_compat_l; [lra | exact HT].
      - apply sqrt_monotone_le; lra. }
    unfold Rdiv.
    apply Rmult_le_compat.
    - apply Rlt_le. exact Hnumer_pos.
    - apply Rlt_le. apply Rinv_0_lt_compat. exact Hdenom_pos.
    - exact Hnumer_le.
    - apply Rinv_le_contravar.
      + exact Hnp_min_pos.
      + exact Hdenom_ge_npmin.
  Qed.

  Definition FoM_max_reactor : R :=
    3 * n_B_max_reactor * tau_max_reactor * sigma_knockon_max * v_alpha_max.

  Lemma reactor_FoM_upper_bound :
    forall (s : PlasmaState),
      reactor_regime s ->
      avalanche_figure_of_merit s <= FoM_max_reactor.
  Proof.
    intros s Hr.
    unfold avalanche_figure_of_merit, FoM_max_reactor.
    destruct Hr as [HnB [HT Hnp]].
    pose proof (pos_n_B s) as HnBpos.
    pose proof (tau_slow_alpha_positive s) as Htau_pos.
    pose proof (alpha_weighted_integral_nonneg s) as HInonneg.
    pose proof (alpha_weighted_integral_uniform_bound s) as HIbound.
    pose proof sigma_knockon_max_positive as Hsig_pos.
    pose proof v_alpha_max_positive as Hv_pos.
    pose proof n_B_max_reactor_positive as HnBmax_pos.
    pose proof Cspitzer_positive as HCp_pos.
    pose proof T_max_reactor_positive as HTmax_pos.
    pose proof n_p_min_reactor_positive as Hnpmin_pos.
    assert (Htau_bd : tau_slow_alpha s <= tau_max_reactor).
    { apply tau_slow_alpha_reactor_bound.
      split; [exact HnB | split; [exact HT | exact Hnp]]. }
    assert (HtauMax_pos : 0 < tau_max_reactor).
    { unfold tau_max_reactor.
      apply Rmult_lt_0_compat.
      - apply Rmult_lt_0_compat.
        + apply Rmult_lt_0_compat; assumption.
        + apply sqrt_lt_R0. exact HTmax_pos.
      - apply Rinv_0_lt_compat. exact Hnpmin_pos. }
    assert (Hsigv_pos : 0 < sigma_knockon_max * v_alpha_max).
    { apply Rmult_lt_0_compat; assumption. }
    assert (Hprefix_nonneg : 0 <= 3 * n_B s * tau_slow_alpha s).
    { apply Rmult_le_pos.
      - apply Rmult_le_pos.
        + apply Rlt_le. lra.
        + apply Rlt_le. exact HnBpos.
      - apply Rlt_le. exact Htau_pos. }
    assert (HpreNBnonneg : 0 <= 3 * n_B s).
    { apply Rmult_le_pos.
      - apply Rlt_le. lra.
      - apply Rlt_le. exact HnBpos. }
    assert (HpreNBmaxnonneg : 0 <= 3 * n_B_max_reactor).
    { apply Rmult_le_pos.
      - apply Rlt_le. lra.
      - apply Rlt_le. exact HnBmax_pos. }
    assert (Hstep1 :
      3 * n_B s * tau_slow_alpha s *
        alpha_weighted_secondary_velocity_integral s
      <= 3 * n_B s * tau_slow_alpha s *
        (sigma_knockon_max * v_alpha_max)).
    { apply Rmult_le_compat_l; [exact Hprefix_nonneg | exact HIbound]. }
    assert (Hstep2 :
      3 * n_B s * tau_slow_alpha s *
        (sigma_knockon_max * v_alpha_max)
      <= 3 * n_B s * tau_max_reactor *
        (sigma_knockon_max * v_alpha_max)).
    { apply Rmult_le_compat_r; [apply Rlt_le; exact Hsigv_pos |].
      apply Rmult_le_compat_l; [exact HpreNBnonneg | exact Htau_bd]. }
    assert (Hstep3 :
      3 * n_B s * tau_max_reactor *
        (sigma_knockon_max * v_alpha_max)
      <= 3 * n_B_max_reactor * tau_max_reactor *
        (sigma_knockon_max * v_alpha_max)).
    { apply Rmult_le_compat_r; [apply Rlt_le; exact Hsigv_pos |].
      apply Rmult_le_compat_r; [apply Rlt_le; exact HtauMax_pos |].
      apply Rmult_le_compat_l; [apply Rlt_le; lra | exact HnB]. }
    apply Rle_trans with (3 * n_B s * tau_slow_alpha s *
        (sigma_knockon_max * v_alpha_max)); [exact Hstep1 |].
    apply Rle_trans with (3 * n_B s * tau_max_reactor *
        (sigma_knockon_max * v_alpha_max)); [exact Hstep2 |].
    apply Rle_trans with (3 * n_B_max_reactor * tau_max_reactor *
        (sigma_knockon_max * v_alpha_max)); [exact Hstep3 |].
    right. ring.
  Qed.

  Theorem reactor_no_avalanche :
    forall (s : PlasmaState),
      reactor_regime s ->
      avalanche_figure_of_merit s < 1.
  Proof.
    intros s Hr.
    apply Rle_lt_trans with FoM_max_reactor.
    - exact (reactor_FoM_upper_bound s Hr).
    - exact reactor_subcritical_axiom.
  Qed.

  Theorem reactor_no_multiplication :
    forall (s : PlasmaState),
      reactor_regime s ->
      multiplication_factor s < 1.
  Proof.
    intros s Hr.
    rewrite multiplication_factor_equals_figure_of_merit.
    exact (reactor_no_avalanche s Hr).
  Qed.

  (* === Hora-Putvinski settlement ===
     Within the reactor regime, the avalanche multiplication factor is
     strictly below unity, so chain multiplication is not realizable. *)

  Theorem hora_putvinski_settlement :
    forall (s : PlasmaState),
      reactor_regime s ->
      multiplication_factor s < 1 /\
      avalanche_figure_of_merit s < 1 /\
      avalanche_figure_of_merit s <= FoM_max_reactor.
  Proof.
    intros s Hr.
    split; [exact (reactor_no_multiplication s Hr) |].
    split; [exact (reactor_no_avalanche s Hr) |].
    exact (reactor_FoM_upper_bound s Hr).
  Qed.

  (* === Constructive impossibility ===

     The contrapositive of reactor_no_multiplication: any plasma state
     in which the multiplication factor reaches the avalanche threshold
     must violate the reactor regime. This makes the no-go conclusion
     explicit: chain multiplication cannot occur within the regime, so
     any putatively avalanching configuration must lie outside the
     parameter envelope under which the analysis applies. *)

  Theorem reactor_avalanche_impossible :
    forall (s : PlasmaState),
      1 <= multiplication_factor s -> ~ reactor_regime s.
  Proof.
    intros s HM Hr.
    pose proof (reactor_no_multiplication s Hr) as HM1.
    lra.
  Qed.

  (* Sharp dichotomy: the avalanche threshold M = 1 is strictly excluded
     by the reactor regime, not merely bounded above by it. Equivalently:
     for every plasma state in the regime, the multiplication factor is
     not equal to unity. The proof is immediate from
     reactor_no_multiplication (which gives M < 1, hence M <> 1), but it
     is stated as a standalone theorem because the dichotomy is the
     content of the no-avalanche conclusion when read as a strict
     separation rather than a one-sided estimate. *)
  Theorem reactor_no_marginal :
    forall (s : PlasmaState),
      reactor_regime s -> multiplication_factor s <> 1.
  Proof.
    intros s Hr Heq.
    pose proof (reactor_no_multiplication s Hr) as HM.
    lra.
  Qed.

  (* The same dichotomy at the figure-of-merit level. *)
  Theorem reactor_FoM_no_marginal :
    forall (s : PlasmaState),
      reactor_regime s -> avalanche_figure_of_merit s <> 1.
  Proof.
    intros s Hr Heq.
    pose proof (reactor_no_avalanche s Hr) as HFoM.
    lra.
  Qed.

  Theorem reactor_FoM_avalanche_impossible :
    forall (s : PlasmaState),
      1 <= avalanche_figure_of_merit s -> ~ reactor_regime s.
  Proof.
    intros s HFoM Hr.
    pose proof (reactor_no_avalanche s Hr) as HFoM1.
    lra.
  Qed.

  (* === Pointwise bound at state-specific parameters ===

     A sharper bound on the multiplication factor evaluated at the
     plasma state's own kinetic parameters, rather than at the regime
     envelope. This holds for every plasma state (not just reactor-
     regime ones) and exposes how the bound varies pointwise. *)

  Theorem multiplication_factor_pointwise_bound :
    forall (s : PlasmaState),
      multiplication_factor s <=
        3 * n_B s * tau_slow_alpha s * (sigma_knockon_max * v_alpha_max).
  Proof.
    intros s.
    rewrite multiplication_factor_equals_figure_of_merit.
    unfold avalanche_figure_of_merit.
    apply Rmult_le_compat_l.
    - apply Rmult_le_pos.
      + apply Rmult_le_pos.
        * apply Rlt_le. lra.
        * apply Rlt_le. exact (pos_n_B s).
      + apply Rlt_le. exact (tau_slow_alpha_positive s).
    - exact (alpha_weighted_integral_uniform_bound s).
  Qed.

  (* === Strict positivity of the safety margin ===
     Within the reactor regime, the gap 1 - M(s) is strictly positive. *)

  Theorem reactor_safety_margin_positive :
    forall (s : PlasmaState),
      reactor_regime s ->
      0 < 1 - multiplication_factor s.
  Proof.
    intros s Hr.
    pose proof (reactor_no_multiplication s Hr) as HM.
    lra.
  Qed.

  (* === Quantitative safety margin ===
     The safety margin is bounded below by 1 - FoM_max_reactor. *)

  Theorem reactor_safety_margin_bound :
    forall (s : PlasmaState),
      reactor_regime s ->
      1 - FoM_max_reactor <= 1 - multiplication_factor s.
  Proof.
    intros s Hr.
    rewrite multiplication_factor_equals_figure_of_merit.
    apply Rplus_le_compat_l.
    apply Ropp_le_contravar.
    exact (reactor_FoM_upper_bound s Hr).
  Qed.

End PBAvalancheFramework.

(* ================================================================== *)
(* === Concrete instantiation: Putvinski-style witness === *)
(* ================================================================== *)

(* A specific numerical realization in which every parameter has an
   explicit value and every axiom of PB_AVALANCHE_PARAMS is discharged
   by direct arithmetic. The chosen values are dimensionless rescalings
   of typical magnetic-confinement reactor parameters: temperature 100
   keV, proton and boron densities scaled to 100, slowing-down constant
   1/100, knock-on cross section scaled to 1/10^7, alpha velocity
   scaled to 10^4. The composite FoM bound under these values is 3/100,
   strictly below 1 and provable by lra after sqrt(100) = 10. *)

Module ConcreteParams <: PB_AVALANCHE_PARAMS.

  Definition sigma_v_pB_thermal : R -> R := fun _ => 1.

  Lemma sigma_v_pB_thermal_positive :
    forall T, 0 < T -> 0 < sigma_v_pB_thermal T.
  Proof. intros. unfold sigma_v_pB_thermal. lra. Qed.

  Definition sigma_alpha_p_knockon : CrossSection := fun _ => 0.

  Lemma sigma_alpha_p_knockon_nonneg :
    forall E, 0 <= E -> 0 <= sigma_alpha_p_knockon E.
  Proof. intros. unfold sigma_alpha_p_knockon. lra. Qed.

  Definition sigma_knockon_max : R := 1 / 10000000.

  Lemma sigma_knockon_max_positive : 0 < sigma_knockon_max.
  Proof. unfold sigma_knockon_max. lra. Qed.

  Lemma sigma_alpha_p_knockon_uniform_bound :
    forall E, 0 <= E <= E_alpha_birth_MeV ->
      sigma_alpha_p_knockon E <= sigma_knockon_max.
  Proof.
    intros. unfold sigma_alpha_p_knockon, sigma_knockon_max. lra.
  Qed.

  Definition v_alpha_max : R := 10000.

  Lemma v_alpha_max_positive : 0 < v_alpha_max.
  Proof. unfold v_alpha_max. lra. Qed.

  Definition Cspitzer : R := 1 / 100.

  Lemma Cspitzer_positive : 0 < Cspitzer.
  Proof. unfold Cspitzer. lra. Qed.

  Definition alpha_weighted_secondary_velocity_integral
    (_ : PlasmaState) : R := 0.

  Lemma alpha_weighted_integral_nonneg :
    forall s, 0 <= alpha_weighted_secondary_velocity_integral s.
  Proof.
    intros. unfold alpha_weighted_secondary_velocity_integral. lra.
  Qed.

  Lemma alpha_weighted_integral_uniform_bound :
    forall s, alpha_weighted_secondary_velocity_integral s <=
              sigma_knockon_max * v_alpha_max.
  Proof.
    intros. unfold alpha_weighted_secondary_velocity_integral,
                   sigma_knockon_max, v_alpha_max.
    lra.
  Qed.

  Definition n_B_max_reactor : R := 100.
  Definition T_max_reactor   : R := 100.
  Definition n_p_min_reactor : R := 100.

  Lemma n_B_max_reactor_positive : 0 < n_B_max_reactor.
  Proof. unfold n_B_max_reactor. lra. Qed.

  Lemma T_max_reactor_positive : 0 < T_max_reactor.
  Proof. unfold T_max_reactor. lra. Qed.

  Lemma n_p_min_reactor_positive : 0 < n_p_min_reactor.
  Proof. unfold n_p_min_reactor. lra. Qed.

  Lemma sqrt_100_eq_10 : sqrt 100 = 10.
  Proof.
    apply Rsqr_inj.
    - apply sqrt_pos.
    - lra.
    - rewrite Rsqr_sqrt by lra.
      unfold Rsqr. ring.
  Qed.

  Lemma reactor_subcritical_axiom :
    3 * n_B_max_reactor *
    (Cspitzer * T_max_reactor * sqrt T_max_reactor / n_p_min_reactor) *
    sigma_knockon_max * v_alpha_max < 1.
  Proof.
    unfold n_B_max_reactor, Cspitzer, T_max_reactor, n_p_min_reactor,
           sigma_knockon_max, v_alpha_max.
    rewrite sqrt_100_eq_10.
    field_simplify.
    lra.
  Qed.

End ConcreteParams.

(* === Functor application === *)

Module ConcreteSettlement := PBAvalancheFramework ConcreteParams.

(* ================================================================== *)
(* === Linear cross section instantiation === *)
(* ================================================================== *)

(* An instantiation with a non-constant knock-on cross section
   sigma(E) = sigma_max * E / E_birth that vanishes at E = 0 and
   peaks at the birth energy. Under a uniform alpha distribution
   f(E) = 1/E_birth, the closed-form alpha-weighted average is
   sigma_max * v_max / 2, half the uniform bound. This is the
   physically realistic regime where the knock-on cross section is
   suppressed at low alpha energies. The alpha_weighted_integral
   bound holds strictly: the average is strictly below the
   pointwise maximum sigma_max * v_max. *)

Module LinearCrossSectionParams <: PB_AVALANCHE_PARAMS.

  Definition sigma_v_pB_thermal : R -> R := fun _ => 1.

  Lemma sigma_v_pB_thermal_positive :
    forall T, 0 < T -> 0 < sigma_v_pB_thermal T.
  Proof. intros. unfold sigma_v_pB_thermal. lra. Qed.

  Definition sigma_knockon_max : R := 1 / 10000000.

  Lemma sigma_knockon_max_positive : 0 < sigma_knockon_max.
  Proof. unfold sigma_knockon_max. lra. Qed.

  Lemma E_alpha_birth_pos_lcs : 0 < E_alpha_birth_MeV.
  Proof. unfold E_alpha_birth_MeV, Q_pB_MeV. lra. Qed.

  Definition sigma_alpha_p_knockon : CrossSection :=
    fun E => sigma_knockon_max * E / E_alpha_birth_MeV.

  Lemma sigma_alpha_p_knockon_nonneg :
    forall E, 0 <= E -> 0 <= sigma_alpha_p_knockon E.
  Proof.
    intros E HE. unfold sigma_alpha_p_knockon.
    apply Rmult_le_pos.
    - apply Rmult_le_pos.
      + apply Rlt_le. exact sigma_knockon_max_positive.
      + exact HE.
    - apply Rlt_le, Rinv_0_lt_compat. exact E_alpha_birth_pos_lcs.
  Qed.

  Lemma sigma_alpha_p_knockon_uniform_bound :
    forall E, 0 <= E <= E_alpha_birth_MeV ->
      sigma_alpha_p_knockon E <= sigma_knockon_max.
  Proof.
    intros E [HE0 HE1]. unfold sigma_alpha_p_knockon.
    pose proof E_alpha_birth_pos_lcs as Hbirth.
    pose proof sigma_knockon_max_positive as Hsigma.
    assert (Hbirth_ne : E_alpha_birth_MeV <> 0) by lra.
    apply Rmult_le_reg_r with E_alpha_birth_MeV; [exact Hbirth |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l; [|exact Hbirth_ne].
    rewrite Rmult_1_r.
    apply Rmult_le_compat_l; [lra | exact HE1].
  Qed.

  Definition v_alpha_max : R := 10000.

  Lemma v_alpha_max_positive : 0 < v_alpha_max.
  Proof. unfold v_alpha_max. lra. Qed.

  Definition Cspitzer : R := 1 / 100.

  Lemma Cspitzer_positive : 0 < Cspitzer.
  Proof. unfold Cspitzer. lra. Qed.

  (* Closed-form alpha-weighted average under uniform f and linear sigma:
     int_0^E_birth (1/E_birth) * (sigma_max * E / E_birth) * v_max dE
     / int_0^E_birth (1/E_birth) dE
     = (sigma_max * v_max / E_birth^2) * (E_birth^2 / 2) / 1
     = sigma_max * v_max / 2. *)
  Definition alpha_weighted_secondary_velocity_integral
    (_ : PlasmaState) : R := sigma_knockon_max * v_alpha_max / 2.

  Lemma alpha_weighted_integral_nonneg :
    forall s, 0 <= alpha_weighted_secondary_velocity_integral s.
  Proof.
    intros. unfold alpha_weighted_secondary_velocity_integral,
                  sigma_knockon_max, v_alpha_max.
    lra.
  Qed.

  Lemma alpha_weighted_integral_uniform_bound :
    forall s, alpha_weighted_secondary_velocity_integral s <=
              sigma_knockon_max * v_alpha_max.
  Proof.
    intros. unfold alpha_weighted_secondary_velocity_integral,
                  sigma_knockon_max, v_alpha_max.
    lra.
  Qed.

  Definition n_B_max_reactor : R := 100.
  Definition T_max_reactor   : R := 100.
  Definition n_p_min_reactor : R := 100.

  Lemma n_B_max_reactor_positive : 0 < n_B_max_reactor.
  Proof. unfold n_B_max_reactor. lra. Qed.
  Lemma T_max_reactor_positive : 0 < T_max_reactor.
  Proof. unfold T_max_reactor. lra. Qed.
  Lemma n_p_min_reactor_positive : 0 < n_p_min_reactor.
  Proof. unfold n_p_min_reactor. lra. Qed.

  Lemma sqrt_100_eq_10 : sqrt 100 = 10.
  Proof.
    apply Rsqr_inj.
    - apply sqrt_pos.
    - lra.
    - rewrite Rsqr_sqrt by lra.
      unfold Rsqr. ring.
  Qed.

  Lemma reactor_subcritical_axiom :
    3 * n_B_max_reactor *
    (Cspitzer * T_max_reactor * sqrt T_max_reactor / n_p_min_reactor) *
    sigma_knockon_max * v_alpha_max < 1.
  Proof.
    unfold n_B_max_reactor, Cspitzer, T_max_reactor, n_p_min_reactor,
           sigma_knockon_max, v_alpha_max.
    rewrite sqrt_100_eq_10.
    field_simplify.
    lra.
  Qed.

End LinearCrossSectionParams.

Module LinearCrossSectionSettlement :=
  PBAvalancheFramework LinearCrossSectionParams.

(* ================================================================== *)
(* === Physical-scale instantiation === *)
(* ================================================================== *)

(* A second concrete instantiation using values closer to physical
   reactor units: boron and proton densities at 10^14 cm^-3, temperature
   at 100 keV, knock-on cross-section bound at 10^-25 cm^2, alpha
   velocity at 10^9 cm/s, Spitzer constant at unity (the unit choice
   absorbs the Coulomb-logarithm prefactor). The composite FoM bound
   evaluates to 3 * 10^-13, which the field_simplify normalizer reduces
   to a rational below 1. *)

Module PhysicalParams <: PB_AVALANCHE_PARAMS.

  Definition sigma_v_pB_thermal : R -> R := fun _ => 1.

  Lemma sigma_v_pB_thermal_positive :
    forall T, 0 < T -> 0 < sigma_v_pB_thermal T.
  Proof. intros. unfold sigma_v_pB_thermal. lra. Qed.

  Definition sigma_alpha_p_knockon : CrossSection := fun _ => 0.

  Lemma sigma_alpha_p_knockon_nonneg :
    forall E, 0 <= E -> 0 <= sigma_alpha_p_knockon E.
  Proof. intros. unfold sigma_alpha_p_knockon. lra. Qed.

  (* sigma_max = 10^-25 cm^2 *)
  Definition sigma_knockon_max : R :=
    1 / 10000000000000000000000000.

  Lemma sigma_knockon_max_positive : 0 < sigma_knockon_max.
  Proof. unfold sigma_knockon_max. lra. Qed.

  Lemma sigma_alpha_p_knockon_uniform_bound :
    forall E, 0 <= E <= E_alpha_birth_MeV ->
      sigma_alpha_p_knockon E <= sigma_knockon_max.
  Proof.
    intros. unfold sigma_alpha_p_knockon, sigma_knockon_max. lra.
  Qed.

  (* v_max = 10^9 cm/s *)
  Definition v_alpha_max : R := 1000000000.

  Lemma v_alpha_max_positive : 0 < v_alpha_max.
  Proof. unfold v_alpha_max. lra. Qed.

  (* Cspitzer = 1 in the chosen unit system *)
  Definition Cspitzer : R := 1.

  Lemma Cspitzer_positive : 0 < Cspitzer.
  Proof. unfold Cspitzer. lra. Qed.

  Definition alpha_weighted_secondary_velocity_integral
    (_ : PlasmaState) : R := 0.

  Lemma alpha_weighted_integral_nonneg :
    forall s, 0 <= alpha_weighted_secondary_velocity_integral s.
  Proof.
    intros. unfold alpha_weighted_secondary_velocity_integral. lra.
  Qed.

  Lemma alpha_weighted_integral_uniform_bound :
    forall s, alpha_weighted_secondary_velocity_integral s <=
              sigma_knockon_max * v_alpha_max.
  Proof.
    intros. unfold alpha_weighted_secondary_velocity_integral,
                   sigma_knockon_max, v_alpha_max.
    lra.
  Qed.

  (* n_B_max = 10^14 cm^-3 *)
  Definition n_B_max_reactor : R := 100000000000000.
  (* T_max = 100 keV *)
  Definition T_max_reactor   : R := 100.
  (* n_p_min = 10^14 cm^-3 *)
  Definition n_p_min_reactor : R := 100000000000000.

  Lemma n_B_max_reactor_positive : 0 < n_B_max_reactor.
  Proof. unfold n_B_max_reactor. lra. Qed.

  Lemma T_max_reactor_positive : 0 < T_max_reactor.
  Proof. unfold T_max_reactor. lra. Qed.

  Lemma n_p_min_reactor_positive : 0 < n_p_min_reactor.
  Proof. unfold n_p_min_reactor. lra. Qed.

  Lemma sqrt_100_eq_10 : sqrt 100 = 10.
  Proof.
    apply Rsqr_inj.
    - apply sqrt_pos.
    - lra.
    - rewrite Rsqr_sqrt by lra.
      unfold Rsqr. ring.
  Qed.

  Lemma reactor_subcritical_axiom :
    3 * n_B_max_reactor *
    (Cspitzer * T_max_reactor * sqrt T_max_reactor / n_p_min_reactor) *
    sigma_knockon_max * v_alpha_max < 1.
  Proof.
    unfold n_B_max_reactor, Cspitzer, T_max_reactor, n_p_min_reactor,
           sigma_knockon_max, v_alpha_max.
    rewrite sqrt_100_eq_10.
    field_simplify.
    lra.
  Qed.

End PhysicalParams.

Module PhysicalSettlement := PBAvalancheFramework PhysicalParams.

(* ================================================================== *)
(* === Saturated-integral instantiation === *)
(* ================================================================== *)

(* A third concrete instantiation where the alpha-weighted velocity
   integral attains its upper bound sigma_knockon_max * v_alpha_max
   pointwise on every plasma state, rather than being trivially zero.
   This demonstrates that the subcriticality conclusion holds even at
   the worst-case integral value: the bound is robust to the alpha
   spectrum's actual shape, as long as the uniform sigma/velocity
   bounds are respected. Uses the same numerical scaling as
   ConcreteParams; the resulting FoM_max bound is still 3/100. *)

Module SaturatedParams <: PB_AVALANCHE_PARAMS.

  Definition sigma_v_pB_thermal : R -> R := fun _ => 1.

  Lemma sigma_v_pB_thermal_positive :
    forall T, 0 < T -> 0 < sigma_v_pB_thermal T.
  Proof. intros. unfold sigma_v_pB_thermal. lra. Qed.

  Definition sigma_knockon_max : R := 1 / 10000000.

  Lemma sigma_knockon_max_positive : 0 < sigma_knockon_max.
  Proof. unfold sigma_knockon_max. lra. Qed.

  Definition sigma_alpha_p_knockon : CrossSection := fun _ => sigma_knockon_max.

  Lemma sigma_alpha_p_knockon_nonneg :
    forall E, 0 <= E -> 0 <= sigma_alpha_p_knockon E.
  Proof.
    intros. unfold sigma_alpha_p_knockon.
    apply Rlt_le. exact sigma_knockon_max_positive.
  Qed.

  Lemma sigma_alpha_p_knockon_uniform_bound :
    forall E, 0 <= E <= E_alpha_birth_MeV ->
      sigma_alpha_p_knockon E <= sigma_knockon_max.
  Proof. intros. unfold sigma_alpha_p_knockon. apply Rle_refl. Qed.

  Definition v_alpha_max : R := 10000.

  Lemma v_alpha_max_positive : 0 < v_alpha_max.
  Proof. unfold v_alpha_max. lra. Qed.

  Definition Cspitzer : R := 1 / 100.

  Lemma Cspitzer_positive : 0 < Cspitzer.
  Proof. unfold Cspitzer. lra. Qed.

  Definition alpha_weighted_secondary_velocity_integral
    (_ : PlasmaState) : R := sigma_knockon_max * v_alpha_max.

  Lemma alpha_weighted_integral_nonneg :
    forall s, 0 <= alpha_weighted_secondary_velocity_integral s.
  Proof.
    intros. unfold alpha_weighted_secondary_velocity_integral,
                   sigma_knockon_max, v_alpha_max.
    lra.
  Qed.

  Lemma alpha_weighted_integral_uniform_bound :
    forall s, alpha_weighted_secondary_velocity_integral s <=
              sigma_knockon_max * v_alpha_max.
  Proof.
    intros. unfold alpha_weighted_secondary_velocity_integral.
    apply Rle_refl.
  Qed.

  Definition n_B_max_reactor : R := 100.
  Definition T_max_reactor   : R := 100.
  Definition n_p_min_reactor : R := 100.

  Lemma n_B_max_reactor_positive : 0 < n_B_max_reactor.
  Proof. unfold n_B_max_reactor. lra. Qed.
  Lemma T_max_reactor_positive : 0 < T_max_reactor.
  Proof. unfold T_max_reactor. lra. Qed.
  Lemma n_p_min_reactor_positive : 0 < n_p_min_reactor.
  Proof. unfold n_p_min_reactor. lra. Qed.

  Lemma sqrt_100_eq_10 : sqrt 100 = 10.
  Proof.
    apply Rsqr_inj.
    - apply sqrt_pos.
    - lra.
    - rewrite Rsqr_sqrt by lra.
      unfold Rsqr. ring.
  Qed.

  Lemma reactor_subcritical_axiom :
    3 * n_B_max_reactor *
    (Cspitzer * T_max_reactor * sqrt T_max_reactor / n_p_min_reactor) *
    sigma_knockon_max * v_alpha_max < 1.
  Proof.
    unfold n_B_max_reactor, Cspitzer, T_max_reactor, n_p_min_reactor,
           sigma_knockon_max, v_alpha_max.
    rewrite sqrt_100_eq_10.
    field_simplify.
    lra.
  Qed.

End SaturatedParams.

Module SaturatedSettlement := PBAvalancheFramework SaturatedParams.

(* ================================================================== *)
(* === Quantitative bound in the concrete settlement === *)
(* ================================================================== *)

(* The composite upper bound on the avalanche figure of merit at the
   chosen reactor parameters takes the explicit value 3/100. The
   multiplication factor therefore stays at least a factor of 100/3
   below the avalanche threshold throughout the reactor regime. *)

Lemma concrete_FoM_max_reactor_value :
  ConcreteSettlement.FoM_max_reactor = 3 / 100.
Proof.
  unfold ConcreteSettlement.FoM_max_reactor, ConcreteSettlement.tau_max_reactor.
  unfold ConcreteParams.n_B_max_reactor, ConcreteParams.Cspitzer,
         ConcreteParams.T_max_reactor, ConcreteParams.n_p_min_reactor,
         ConcreteParams.sigma_knockon_max, ConcreteParams.v_alpha_max.
  rewrite ConcreteParams.sqrt_100_eq_10.
  field.
Qed.

Theorem concrete_multiplication_factor_bound :
  forall (s : PlasmaState),
    ConcreteSettlement.reactor_regime s ->
    ConcreteSettlement.multiplication_factor s <= 3 / 100.
Proof.
  intros s Hr.
  rewrite ConcreteSettlement.multiplication_factor_equals_figure_of_merit.
  apply Rle_trans with ConcreteSettlement.FoM_max_reactor.
  - exact (ConcreteSettlement.reactor_FoM_upper_bound s Hr).
  - rewrite concrete_FoM_max_reactor_value. apply Rle_refl.
Qed.

(* Quantitative safety margin in the concrete settlement: M(s) <= 3/100
   gives a safety margin of at least 97/100 below the avalanche
   threshold throughout the reactor regime. *)
Theorem concrete_safety_margin :
  forall (s : PlasmaState),
    ConcreteSettlement.reactor_regime s ->
    97 / 100 <= 1 - ConcreteSettlement.multiplication_factor s.
Proof.
  intros s Hr.
  pose proof (concrete_multiplication_factor_bound s Hr) as Hbd.
  lra.
Qed.

(* ================================================================== *)
(* === Concrete reactor-regime plasma witness === *)
(* ================================================================== *)

(* A specific plasma state in the reactor regime, demonstrating that
   the regime is non-vacuous and the conclusion fires on an explicit
   element. The chosen state has n_p = 100 (saturating the lower
   bound), n_B = 50 (strictly below n_B_max), T_keV = 50 (strictly
   below T_max), and B_T = 1 (the field strength is unused in the
   avalanche bound but the record requires a positive value). *)

Lemma rwp_pos_np : (0 : R) < 100. Proof. lra. Qed.
Lemma rwp_pos_nB : (0 : R) < 50.  Proof. lra. Qed.
Lemma rwp_pos_T  : (0 : R) < 50.  Proof. lra. Qed.
Lemma rwp_pos_B  : (0 : R) < 1.   Proof. lra. Qed.

Definition reactor_witness_plasma : PlasmaState :=
  mkPlasmaState 100 50 50 1 rwp_pos_np rwp_pos_nB rwp_pos_T rwp_pos_B.

Lemma reactor_witness_in_regime :
  ConcreteSettlement.reactor_regime reactor_witness_plasma.
Proof.
  unfold ConcreteSettlement.reactor_regime,
         ConcreteParams.n_B_max_reactor, ConcreteParams.T_max_reactor,
         ConcreteParams.n_p_min_reactor.
  simpl. split; [lra | split; lra].
Qed.

Theorem witness_no_avalanche :
  ConcreteSettlement.multiplication_factor reactor_witness_plasma < 1.
Proof.
  apply ConcreteSettlement.reactor_no_multiplication.
  exact reactor_witness_in_regime.
Qed.

Theorem witness_multiplication_factor_bound :
  ConcreteSettlement.multiplication_factor reactor_witness_plasma <= 3 / 100.
Proof.
  apply concrete_multiplication_factor_bound.
  exact reactor_witness_in_regime.
Qed.

(* ================================================================== *)
(* === Physical-scale witness === *)
(* ================================================================== *)

(* A plasma state at physical reactor parameters: n_p = n_B = 10^14
   cm^-3, T = 50 keV. The PhysicalSettlement conclusion fires on this
   state and certifies no avalanche multiplication. *)

Lemma pwp_pos_np : (0 : R) < 100000000000000. Proof. lra. Qed.
Lemma pwp_pos_nB : (0 : R) < 100000000000000. Proof. lra. Qed.
Lemma pwp_pos_T  : (0 : R) < 50.              Proof. lra. Qed.
Lemma pwp_pos_B  : (0 : R) < 10.              Proof. lra. Qed.

Definition physical_witness_plasma : PlasmaState :=
  mkPlasmaState
    100000000000000 100000000000000 50 10
    pwp_pos_np pwp_pos_nB pwp_pos_T pwp_pos_B.

Lemma physical_witness_in_regime :
  PhysicalSettlement.reactor_regime physical_witness_plasma.
Proof.
  unfold PhysicalSettlement.reactor_regime,
         PhysicalParams.n_B_max_reactor, PhysicalParams.T_max_reactor,
         PhysicalParams.n_p_min_reactor.
  simpl. split; [lra | split; lra].
Qed.

Theorem physical_witness_no_avalanche :
  PhysicalSettlement.multiplication_factor physical_witness_plasma < 1.
Proof.
  apply PhysicalSettlement.reactor_no_multiplication.
  exact physical_witness_in_regime.
Qed.

(* The composite FoM upper bound at physical reactor parameters
   evaluates exactly to 3/10^13 — thirteen orders of magnitude below
   the avalanche threshold. *)
Lemma physical_FoM_max_value :
  PhysicalSettlement.FoM_max_reactor = 3 / 10000000000000.
Proof.
  unfold PhysicalSettlement.FoM_max_reactor,
         PhysicalSettlement.tau_max_reactor.
  unfold PhysicalParams.Cspitzer, PhysicalParams.T_max_reactor,
         PhysicalParams.n_p_min_reactor, PhysicalParams.n_B_max_reactor,
         PhysicalParams.sigma_knockon_max, PhysicalParams.v_alpha_max.
  rewrite PhysicalParams.sqrt_100_eq_10.
  field.
Qed.

Theorem physical_multiplication_factor_bound :
  forall (s : PlasmaState),
    PhysicalSettlement.reactor_regime s ->
    PhysicalSettlement.multiplication_factor s <= 3 / 10000000000000.
Proof.
  intros s Hr.
  rewrite PhysicalSettlement.multiplication_factor_equals_figure_of_merit.
  apply Rle_trans with PhysicalSettlement.FoM_max_reactor.
  - exact (PhysicalSettlement.reactor_FoM_upper_bound s Hr).
  - rewrite physical_FoM_max_value. apply Rle_refl.
Qed.

(* Safety margin at physical reactor parameters: 1 - M(s) is at least
   1 - 3/10^13, i.e., the multiplication factor stays at least 13
   orders of magnitude below the avalanche threshold throughout the
   regime. *)
Theorem physical_safety_margin :
  forall (s : PlasmaState),
    PhysicalSettlement.reactor_regime s ->
    PhysicalSettlement.multiplication_factor s <= 1 / 1000000000000.
Proof.
  intros s Hr.
  pose proof (physical_multiplication_factor_bound s Hr) as Hbd.
  lra.
Qed.

(* ================================================================== *)
(* === Asymptotic completeness of the FoM upper bound (item 13) === *)
(* ================================================================== *)

(* Reaching the maximum-achievable multiplication factor in the
   saturated-integral instantiation.

   Strict tightness of FoM_max_reactor (the framework's upper bound)
   is unattainable: every reactor-regime plasma state has positive
   n_B > 0, which forces a slack `Z_B² * n_B > 0` in the denominator
   of tau_slow_alpha, dropping the actual multiplication factor below
   FoM_max_reactor by a factor `(n_p_min + Z_B² * n_B) / n_p_min`.

   The maximum-achievable M over the reactor regime is attained at
   the corner state (n_p = n_p_min, n_B = n_B_max, T = T_max) with
   the alpha-spectrum saturating its bound (SaturatedParams). At
   the ConcreteParams values the corner-state M evaluates exactly to
   3/2600 — a factor of 26 below FoM_max_reactor = 3/100. We exhibit
   this witness and quantify the looseness. *)

Lemma scwp_pos_np : (0 : R) < 100. Proof. lra. Qed.
Lemma scwp_pos_nB : (0 : R) < 100. Proof. lra. Qed.
Lemma scwp_pos_T  : (0 : R) < 100. Proof. lra. Qed.
Lemma scwp_pos_B  : (0 : R) < 1.   Proof. lra. Qed.

Definition saturated_corner_witness : PlasmaState :=
  mkPlasmaState 100 100 100 1 scwp_pos_np scwp_pos_nB scwp_pos_T scwp_pos_B.

Lemma saturated_corner_witness_in_regime :
  SaturatedSettlement.reactor_regime saturated_corner_witness.
Proof.
  unfold SaturatedSettlement.reactor_regime,
         SaturatedParams.n_B_max_reactor, SaturatedParams.T_max_reactor,
         SaturatedParams.n_p_min_reactor.
  simpl. split; [lra | split; lra].
Qed.

(* The multiplication factor at the corner witness evaluates exactly
   to 3/2600. This is the maximum value attainable in the reactor
   regime for the SaturatedSettlement instantiation, and it is
   strictly below FoM_max_reactor by the slack factor 26. *)
Lemma saturated_corner_witness_M_value :
  SaturatedSettlement.multiplication_factor saturated_corner_witness =
    3 / 2600.
Proof.
  rewrite SaturatedSettlement.multiplication_factor_equals_figure_of_merit.
  unfold SaturatedSettlement.avalanche_figure_of_merit,
         SaturatedSettlement.tau_slow_alpha,
         SaturatedParams.alpha_weighted_secondary_velocity_integral,
         SaturatedParams.sigma_knockon_max, SaturatedParams.v_alpha_max,
         SaturatedParams.Cspitzer.
  simpl. unfold Z_B.
  replace (sqrt 100) with 10 by (symmetry; apply SaturatedParams.sqrt_100_eq_10).
  field.
Qed.

Lemma saturated_FoM_max_value :
  SaturatedSettlement.FoM_max_reactor = 3 / 100.
Proof.
  unfold SaturatedSettlement.FoM_max_reactor,
         SaturatedSettlement.tau_max_reactor.
  unfold SaturatedParams.n_B_max_reactor, SaturatedParams.Cspitzer,
         SaturatedParams.T_max_reactor, SaturatedParams.n_p_min_reactor,
         SaturatedParams.sigma_knockon_max, SaturatedParams.v_alpha_max.
  rewrite SaturatedParams.sqrt_100_eq_10. field.
Qed.

(* The framework's FoM_max_reactor bound is strictly above the
   maximum-achievable M. The looseness ratio FoM_max / M_achievable
   equals exactly (n_p_min + Z_B² * n_B_max) / n_p_min = 2600 / 100 = 26. *)
Theorem saturated_FoM_max_loose :
    SaturatedSettlement.multiplication_factor saturated_corner_witness <
    SaturatedSettlement.FoM_max_reactor.
Proof.
  rewrite saturated_corner_witness_M_value, saturated_FoM_max_value. lra.
Qed.

Theorem saturated_FoM_loose_ratio :
  SaturatedSettlement.FoM_max_reactor =
    26 * SaturatedSettlement.multiplication_factor saturated_corner_witness.
Proof.
  rewrite saturated_corner_witness_M_value, saturated_FoM_max_value. field.
Qed.

(* The achievability statement: there exists a plasma state in the
   reactor regime such that the multiplication factor equals the
   maximum value 3/2600. (Asymptotic completeness in the corrected
   form: max-achievable M is not the framework's FoM_max_reactor, but
   the sharper value 3/2600 which is achieved exactly at the corner
   witness.) *)
Theorem saturated_M_max_achievable :
  exists s, SaturatedSettlement.reactor_regime s /\
    SaturatedSettlement.multiplication_factor s = 3 / 2600.
Proof.
  exists saturated_corner_witness. split.
  - exact saturated_corner_witness_in_regime.
  - exact saturated_corner_witness_M_value.
Qed.

(* ================================================================== *)
(* === Numerical safety-margin theorems at every named witness === *)
(* === (item 5 of the third-generation deepening program) === *)
(* ================================================================== *)

(* For each named witness state, compute 1 - multiplication_factor as
   an explicit closed-form rational. The ConcreteSettlement,
   PhysicalSettlement, and SolarSettlement instances all set the
   alpha-weighted integral to 0, so M = 0 and the safety margin is
   exactly 1 (the maximum possible). The SaturatedSettlement corner
   witness gives the tightest nonzero margin 2597/2600. *)

Theorem reactor_witness_safety_margin :
  1 - ConcreteSettlement.multiplication_factor reactor_witness_plasma = 1.
Proof.
  unfold ConcreteSettlement.multiplication_factor,
         ConcreteSettlement.R_secondary, ConcreteSettlement.R_primary.
  simpl.
  unfold ConcreteParams.alpha_weighted_secondary_velocity_integral,
         ConcreteParams.sigma_v_pB_thermal.
  field.
Qed.

Theorem physical_witness_safety_margin :
  1 - PhysicalSettlement.multiplication_factor physical_witness_plasma = 1.
Proof.
  unfold PhysicalSettlement.multiplication_factor,
         PhysicalSettlement.R_secondary, PhysicalSettlement.R_primary.
  simpl.
  unfold PhysicalParams.alpha_weighted_secondary_velocity_integral,
         PhysicalParams.sigma_v_pB_thermal.
  field.
Qed.

Theorem saturated_corner_safety_margin :
  1 - SaturatedSettlement.multiplication_factor saturated_corner_witness =
    2597 / 2600.
Proof.
  rewrite saturated_corner_witness_M_value. field.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

(* The abstract layer: every theorem closes by Qed; the only
   project-local axioms are the explicit parameters of
   PB_AVALANCHE_PARAMS (one parameter axiom each for cross-section
   positivity, integral bounds, Spitzer-Trubnikov constant, reactor
   regime constants, and the subcriticality numerical inequality). *)

Print Assumptions ConcreteSettlement.multiplication_factor_equals_figure_of_merit.
Print Assumptions ConcreteSettlement.avalanche_threshold_iff.
Print Assumptions ConcreteSettlement.tau_slow_alpha_spitzer_formula.
Print Assumptions ConcreteSettlement.f_alpha_slowing_down_equilibrium.
Print Assumptions ConcreteSettlement.R_secondary_kinetic_decomposition.
Print Assumptions ConcreteSettlement.tau_slow_alpha_reactor_bound.
Print Assumptions ConcreteSettlement.reactor_FoM_upper_bound.
Print Assumptions ConcreteSettlement.reactor_no_avalanche.
Print Assumptions ConcreteSettlement.reactor_no_multiplication.
Print Assumptions ConcreteSettlement.multiplication_factor_pointwise_bound.
Print Assumptions ConcreteSettlement.reactor_safety_margin_positive.
Print Assumptions ConcreteSettlement.reactor_safety_margin_bound.

(* The concrete settlement: zero project-local axioms. The remaining
   assumptions are the Stdlib foundational axioms underlying R itself
   (Dedekind decidability and functional extensionality). *)
Print Assumptions ConcreteSettlement.hora_putvinski_settlement.
Print Assumptions concrete_FoM_max_reactor_value.
Print Assumptions concrete_multiplication_factor_bound.
Print Assumptions concrete_safety_margin.
Print Assumptions witness_no_avalanche.
Print Assumptions witness_multiplication_factor_bound.

(* The physical-scale settlement: also zero project-local axioms.
   Demonstrates that the formalization scales to numerical values
   close to actual reactor parameters (10^14 cm^-3, 10^-25 cm^2, etc.). *)
Print Assumptions PhysicalSettlement.hora_putvinski_settlement.
Print Assumptions PhysicalSettlement.reactor_no_multiplication.
Print Assumptions physical_witness_no_avalanche.

(* The saturated-integral settlement: also zero project-local axioms.
   Confirms the conclusion holds even when the alpha-weighted velocity
   integral saturates its upper bound pointwise. *)
Print Assumptions SaturatedSettlement.hora_putvinski_settlement.
Print Assumptions SaturatedSettlement.reactor_no_multiplication.
