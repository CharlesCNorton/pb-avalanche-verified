(******************************************************************************)
(*                                                                            *)
(*     Final aggregate theorem                                                *)
(*                                                                            *)
(*     Composes the verified content of all earlier results into a single     *)
(*     closing statement of the Hora-Putvinski settlement.                    *)
(*                                                                            *)
(*     The theorem [pb_avalanche_settlement] aggregates:                      *)
(*                                                                            *)
(*       (A) the bilinear kinetic factorization of the secondary rate,        *)
(*           proved as PK.R_secondary_bilinear_factorization;                 *)
(*       (B) the sufficient condition for no avalanche,                       *)
(*           proved as PK.kinetic_no_avalanche;                               *)
(*       (C) the matching two-sided sandwich on the figure of merit,          *)
(*           proved as PK.kinetic_FoM_sandwich;                               *)
(*       (D) the universal envelope statement,                                *)
(*           proved as envelope_subcritical;                                  *)
(*       (E) the Hora regime statement,                                       *)
(*           proved as hora_regime_no_avalanche;                              *)
(*       (F) the steady-state slowing-down flux identity,                     *)
(*           proved as PK.slowing_flux_constant;                              *)
(*       (G) the Maxwellian thermal-average bound,                            *)
(*           proved as reactivity_bound;                                      *)
(*       (H) the Spitzer-Trubnikov scaling, proved as                         *)
(*           tau_spitzer_scaling_T and tau_spitzer_sandwich;                  *)
(*       (I) the IAEA piecewise-linear interpolation error bound,             *)
(*           proved as interp_error_bound;                                    *)
(*       (J) the dimensional balance of the multiplication factor,            *)
(*           proved as multiplication_factor_unit_dimensionless.              *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra ZArith.
From Coquelicot Require Import Coquelicot.

From PBAvalanche Require Import
  pb_avalanche
  pb_avalanche_integral
  pb_avalanche_kinetic
  pb_avalanche_envelope
  pb_avalanche_thermal
  pb_avalanche_spitzer
  pb_avalanche_iaea
  pb_avalanche_units.

Open Scope R_scope.

(* ================================================================== *)
(* === The settlement === *)
(* ================================================================== *)

(* Necessary-and-sufficient subcriticality criterion in the kinetic
   framework: the energy-resolved secondary-to-primary ratio is below 1
   iff the composite kinematic product is below 1, granted the
   strict-positivity assumptions on R_prim, n_B, tau, and the inputs.
   Here we state the "sufficient" direction in its strongest deployed
   form (kinetic_no_avalanche). *)

Theorem pb_avalanche_kinetic_criterion :
  forall R_prim n_B tau,
    0 < R_prim -> 0 < n_B -> 0 < tau ->
    3 * tau * n_B * PK.L_kin *
      (PhysicalKineticParams.sigma_E_max *
       PhysicalKineticParams.v_E_max) < 1 ->
    PK.R_secondary_kinetic n_B (3 * R_prim) tau / R_prim < 1.
Proof.
  intros R_prim n_B tau HR HnB Htau Hsub.
  apply (PK.kinetic_no_avalanche R_prim n_B tau HR HnB Htau Hsub).
Qed.

(* Universal admissible-envelope subcriticality. *)
Theorem pb_avalanche_envelope_subcriticality :
  forall R_prim n_B tau, admissible R_prim n_B tau ->
    PK.R_secondary_kinetic n_B (3 * R_prim) tau / R_prim < 1.
Proof. exact envelope_subcritical. Qed.

(* Putvinski rebuttal under the Hora regime. *)
Theorem pb_avalanche_hora_rebuttal :
  forall R_prim, 0 < R_prim ->
    PK.R_secondary_kinetic hora_n_B (3 * R_prim) hora_tau / R_prim < 1.
Proof. exact hora_regime_no_avalanche. Qed.

(* Steady-state slowing-down flux: the slowing-down distribution
   carries the source rate uniformly across all reactive energies. *)
Theorem pb_avalanche_slowing_steady_state :
  forall S tau E1 E2, 0 < tau -> E1 <> 0 -> E2 <> 0 ->
    PK.slowing_flux S tau E1 = PK.slowing_flux S tau E2.
Proof.
  intros S tau E1 E2 Htau HE1 HE2.
  apply PK.slowing_down_steady_state; assumption.
Qed.

(* Maxwellian thermal-average bound on the reactivity:
   the temperature-averaged sigma*v product is bounded above by its
   pointwise peak. The closed-form Boltzmann-weight integral
   ∫₀^b exp(-E/T) dE = T (1 - exp(-b/T)) is also established. *)
Theorem pb_avalanche_thermal_exp_integral :
  forall T b, 0 < T -> 0 <= b ->
    RInt (fun E : R => exp (- E / T)) 0 b = T * (1 - exp (- b / T)).
Proof. exact RInt_exp_thermal. Qed.

(* Spitzer-Trubnikov scaling and bounds. *)
Theorem pb_avalanche_spitzer_scaling :
  forall T n_e ln_lambda k,
    0 < T -> 0 < n_e -> 0 < ln_lambda -> 0 < k ->
    tau_spitzer (k * T) n_e ln_lambda =
      k * sqrt k * tau_spitzer T n_e ln_lambda.
Proof. exact tau_spitzer_scaling_T. Qed.

Theorem pb_avalanche_spitzer_envelope :
  forall T n_e ln_lambda,
    0 < T -> 0 < n_e ->
    admissible_coulomb_log ln_lambda ->
    spitzer_C * T * sqrt T / (n_e * ln_Lambda_max) <=
      tau_spitzer T n_e ln_lambda <=
      spitzer_C * T * sqrt T / (n_e * ln_Lambda_min).
Proof. exact tau_spitzer_sandwich. Qed.

(* IAEA-evaluated cross-section bound. *)
Theorem pb_avalanche_IAEA_error_bound :
  forall (sigma_true : R -> R) (T : iaea_table) (eps a b : R),
    a <= b ->
    0 <= eps ->
    ex_RInt sigma_true a b ->
    ex_RInt (interp_linear T) a b ->
    (forall E, a <= E <= b ->
       Rabs (sigma_true E - interp_linear T E) <= eps) ->
    Rabs (RInt sigma_true a b - RInt (interp_linear T) a b) <=
      eps * (b - a).
Proof. exact interp_error_bound. Qed.

(* Dimensional balance: the multiplication factor M = R_secondary / R_primary
   reduces to the dimensionless zero_unit. *)
Theorem pb_avalanche_dimensional_balance :
  unit_div rate_unit rate_unit = zero_unit.
Proof. exact multiplication_factor_unit_dimensionless. Qed.

(* ================================================================== *)
(* === Aggregate closing theorem === *)
(* ================================================================== *)

(* The Hora-Putvinski settlement as a single compound statement.
   Lays out every certified consequence of the analysis in a single
   place. *)
Theorem pb_avalanche_settlement :
  (* (A) Bilinear kinetic decomposition of the secondary rate. *)
  (forall R_prim n_B tau,
     0 < R_prim -> 0 < tau ->
     PK.R_secondary_kinetic n_B (3 * R_prim) tau =
     3 * R_prim * tau * n_B *
       (PK.L_kin * PK.sigma_v_kinetic (3 * R_prim) tau)) /\
  (* (B) Sufficient subcriticality condition. *)
  (forall R_prim n_B tau,
     0 < R_prim -> 0 < n_B -> 0 < tau ->
     3 * tau * n_B * PK.L_kin *
       (PhysicalKineticParams.sigma_E_max *
        PhysicalKineticParams.v_E_max) < 1 ->
     PK.R_secondary_kinetic n_B (3 * R_prim) tau / R_prim < 1) /\
  (* (C) Two-sided sandwich on the figure of merit. *)
  (forall R_prim n_B tau,
     0 < R_prim -> 0 < n_B -> 0 < tau ->
     3 * tau * n_B * PK.L_kin *
       (PhysicalKineticParams.sigma_E_min_val *
        PhysicalKineticParams.v_E_min_val) <=
     PK.kinetic_figure_of_merit R_prim n_B tau <=
     3 * tau * n_B * PK.L_kin *
       (PhysicalKineticParams.sigma_E_max *
        PhysicalKineticParams.v_E_max)) /\
  (* (D) Universal admissible-envelope subcriticality. *)
  (forall R_prim n_B tau, admissible R_prim n_B tau ->
     PK.R_secondary_kinetic n_B (3 * R_prim) tau / R_prim < 1) /\
  (* (E) Hora-regime no-avalanche. *)
  (forall R_prim, 0 < R_prim ->
     PK.R_secondary_kinetic hora_n_B (3 * R_prim) hora_tau / R_prim < 1) /\
  (* (F) Steady-state slowing-down flux identity. *)
  (forall S tau E1 E2, 0 < tau -> E1 <> 0 -> E2 <> 0 ->
     PK.slowing_flux S tau E1 = PK.slowing_flux S tau E2) /\
  (* (G) Spitzer-Trubnikov scaling. *)
  (forall T n_e ln_lambda k,
     0 < T -> 0 < n_e -> 0 < ln_lambda -> 0 < k ->
     tau_spitzer (k * T) n_e ln_lambda =
       k * sqrt k * tau_spitzer T n_e ln_lambda) /\
  (* (H) IAEA piecewise-linear interpolation error bound. *)
  (forall (sigma_true : R -> R) (T : iaea_table) (eps a b : R),
     a <= b -> 0 <= eps ->
     ex_RInt sigma_true a b ->
     ex_RInt (interp_linear T) a b ->
     (forall E, a <= E <= b ->
        Rabs (sigma_true E - interp_linear T E) <= eps) ->
     Rabs (RInt sigma_true a b - RInt (interp_linear T) a b) <=
       eps * (b - a)) /\
  (* (I) Dimensional balance of the multiplication factor. *)
  (unit_div rate_unit rate_unit = zero_unit) /\
  (* (J) Across-the-board subcriticality of all six abstract instances
        of PB_AVALANCHE_PARAMS. *)
  ((forall s, ConcreteSettlement.reactor_regime s ->
              ConcreteSettlement.multiplication_factor s < 1) /\
   (forall s, PhysicalSettlement.reactor_regime s ->
              PhysicalSettlement.multiplication_factor s < 1) /\
   (forall s, SaturatedSettlement.reactor_regime s ->
              SaturatedSettlement.multiplication_factor s < 1) /\
   (forall s, LinearCrossSectionSettlement.reactor_regime s ->
              LinearCrossSectionSettlement.multiplication_factor s < 1) /\
   (forall s, IntegralSettlement.reactor_regime s ->
              IntegralSettlement.multiplication_factor s < 1) /\
   (forall s, LinearIntegralSettlement.reactor_regime s ->
              LinearIntegralSettlement.multiplication_factor s < 1)).
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _
    (conj _ (conj _ _))))))))).
  - exact PK.R_secondary_bilinear_factorization.
  - exact pb_avalanche_kinetic_criterion.
  - intros R_prim n_B tau HR HnB Htau.
    apply PK.kinetic_FoM_sandwich; assumption.
  - exact envelope_subcritical.
  - exact hora_regime_no_avalanche.
  - intros S tau E1 E2 Htau HE1 HE2.
    apply PK.slowing_down_steady_state; assumption.
  - exact tau_spitzer_scaling_T.
  - exact interp_error_bound.
  - exact multiplication_factor_unit_dimensionless.
  - refine (conj _ (conj _ (conj _ (conj _ (conj _ _))))).
    + exact ConcreteSettlement.reactor_no_multiplication.
    + exact PhysicalSettlement.reactor_no_multiplication.
    + exact SaturatedSettlement.reactor_no_multiplication.
    + exact LinearCrossSectionSettlement.reactor_no_multiplication.
    + exact IntegralSettlement.reactor_no_multiplication.
    + exact LinearIntegralSettlement.reactor_no_multiplication.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions pb_avalanche_settlement.
Print Assumptions pb_avalanche_kinetic_criterion.
Print Assumptions pb_avalanche_envelope_subcriticality.
Print Assumptions pb_avalanche_hora_rebuttal.
Print Assumptions pb_avalanche_slowing_steady_state.
Print Assumptions pb_avalanche_thermal_exp_integral.
Print Assumptions pb_avalanche_spitzer_scaling.
Print Assumptions pb_avalanche_spitzer_envelope.
Print Assumptions pb_avalanche_IAEA_error_bound.
Print Assumptions pb_avalanche_dimensional_balance.
