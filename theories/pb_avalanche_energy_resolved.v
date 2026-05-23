(******************************************************************************)
(*                                                                            *)
(*     Energy-resolved velocity kinetic model (item 12)                       *)
(*                                                                            *)
(*     Instantiates KINETIC_MODEL_PARAMS with a non-constant velocity         *)
(*     v_alpha(E) = sqrt(E)  (in MeV^{1/2} units, classical kinematics        *)
(*     v = sqrt(2 E / m) up to an absorbed prefactor).                        *)
(*                                                                            *)
(*     This replaces the placeholder constant velocity in                     *)
(*     ConstantKineticParams with a realistic monotone profile and proves     *)
(*     all the obligations: positivity, sup bound, lower bound, continuity.   *)
(*                                                                            *)
(*     The cross section is taken as a linear ramp on [E_min, E_alpha_birth]  *)
(*     to keep the proofs algebraic, but anything continuous and bounded      *)
(*     would discharge the same obligations.                                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
From PBAvalanche Require Import pb_avalanche pb_avalanche_kinetic.

Open Scope R_scope.

(* ================================================================== *)
(* === Energy-resolved kinetic parameters === *)
(* ================================================================== *)

Module EnergyResolvedKineticParams <: KINETIC_MODEL_PARAMS.

  Definition E_min : R := E_alpha_birth_MeV / 10.

  Lemma E_min_pos : 0 < E_min.
  Proof.
    unfold E_min, E_alpha_birth_MeV, Q_pB_MeV. lra.
  Qed.

  Lemma E_min_lt_birth : E_min < E_alpha_birth_MeV.
  Proof.
    unfold E_min, E_alpha_birth_MeV, Q_pB_MeV. lra.
  Qed.

  (* Sup envelopes. *)
  Definition sigma_E_max : R := 1 / 10000000.
  Definition v_E_max : R := 2.   (* sqrt(E_alpha_birth_MeV) < 2 *)

  Lemma sigma_E_max_pos : 0 < sigma_E_max.
  Proof. unfold sigma_E_max. lra. Qed.

  Lemma v_E_max_pos : 0 < v_E_max.
  Proof. unfold v_E_max. lra. Qed.

  (* Energy-resolved cross section: linear ramp on [E_min, E_alpha_birth]. *)
  Definition sigma_E (E : R) : R :=
    sigma_E_max * (E / E_alpha_birth_MeV).

  (* Energy-resolved velocity: classical sqrt(E) profile. *)
  Definition v_E (E : R) : R := sqrt E.

  Lemma sigma_E_nonneg :
    forall E, E_min <= E <= E_alpha_birth_MeV -> 0 <= sigma_E E.
  Proof.
    intros E [HEm HEb]. unfold sigma_E.
    apply Rmult_le_pos.
    - apply Rlt_le. exact sigma_E_max_pos.
    - unfold Rdiv. apply Rmult_le_pos.
      + pose proof E_min_pos as Hpos. lra.
      + apply Rlt_le, Rinv_0_lt_compat.
        unfold E_alpha_birth_MeV, Q_pB_MeV. lra.
  Qed.

  Lemma v_E_nonneg :
    forall E, E_min <= E <= E_alpha_birth_MeV -> 0 <= v_E E.
  Proof.
    intros E [HEm HEb]. unfold v_E. apply sqrt_pos.
  Qed.

  Lemma sigma_E_bound :
    forall E, E_min <= E <= E_alpha_birth_MeV -> sigma_E E <= sigma_E_max.
  Proof.
    intros E [_ HEb]. unfold sigma_E.
    rewrite <- (Rmult_1_r sigma_E_max) at 2.
    apply Rmult_le_compat_l.
    - apply Rlt_le. exact sigma_E_max_pos.
    - assert (HE_pos : 0 < E_alpha_birth_MeV)
        by (unfold E_alpha_birth_MeV, Q_pB_MeV; lra).
      apply Rmult_le_reg_r with (r := E_alpha_birth_MeV); [exact HE_pos |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra.
      rewrite Rmult_1_l, Rmult_1_r. exact HEb.
  Qed.

  Lemma sqrt_below_2 : forall E, 0 <= E <= E_alpha_birth_MeV -> sqrt E <= 2.
  Proof.
    intros E [HEpos HEb].
    apply Rsqr_incr_0_var.
    - rewrite Rsqr_sqrt by exact HEpos.
      unfold Rsqr, E_alpha_birth_MeV, Q_pB_MeV in *. lra.
    - lra.
  Qed.

  Lemma v_E_bound :
    forall E, E_min <= E <= E_alpha_birth_MeV -> v_E E <= v_E_max.
  Proof.
    intros E [HEm HEb]. unfold v_E, v_E_max.
    apply sqrt_below_2.
    pose proof E_min_pos as Hpos. split; lra.
  Qed.

  (* Lower bounds for two-sided sandwich. *)
  Definition sigma_E_min_val : R :=
    sigma_E_max * (E_min / E_alpha_birth_MeV).
  Definition v_E_min_val : R := sqrt E_min.

  Lemma sigma_E_min_nonneg : 0 <= sigma_E_min_val.
  Proof.
    unfold sigma_E_min_val. apply Rmult_le_pos.
    - apply Rlt_le. exact sigma_E_max_pos.
    - unfold Rdiv. apply Rmult_le_pos.
      + pose proof E_min_pos as H. lra.
      + apply Rlt_le, Rinv_0_lt_compat.
        unfold E_alpha_birth_MeV, Q_pB_MeV. lra.
  Qed.

  Lemma v_E_min_nonneg : 0 <= v_E_min_val.
  Proof. unfold v_E_min_val. apply sqrt_pos. Qed.

  Lemma sigma_E_lower :
    forall E, E_min <= E <= E_alpha_birth_MeV -> sigma_E_min_val <= sigma_E E.
  Proof.
    intros E [HEm HEb]. unfold sigma_E_min_val, sigma_E.
    apply Rmult_le_compat_l.
    - apply Rlt_le. exact sigma_E_max_pos.
    - unfold Rdiv. apply Rmult_le_compat_r.
      + apply Rlt_le, Rinv_0_lt_compat.
        unfold E_alpha_birth_MeV, Q_pB_MeV. lra.
      + exact HEm.
  Qed.

  Lemma v_E_lower :
    forall E, E_min <= E <= E_alpha_birth_MeV -> v_E_min_val <= v_E E.
  Proof.
    intros E [HEm HEb]. unfold v_E_min_val, v_E.
    apply sqrt_le_1.
    - pose proof E_min_pos as H. lra.
    - pose proof E_min_pos as H. lra.
    - exact HEm.
  Qed.

  Lemma sigma_E_continuous_on :
    forall E, E_min <= E <= E_alpha_birth_MeV -> continuous sigma_E E.
  Proof.
    intros E _. unfold sigma_E.
    apply (continuous_mult (fun _ => sigma_E_max)
                            (fun x => x / E_alpha_birth_MeV)).
    - apply continuous_const.
    - apply (continuous_mult (fun x => x) (fun _ => / E_alpha_birth_MeV)).
      + apply continuous_id.
      + apply continuous_const.
  Qed.

  Lemma v_E_continuous_on :
    forall E, E_min <= E <= E_alpha_birth_MeV -> continuous v_E E.
  Proof.
    intros E [HEm HEb]. unfold v_E.
    apply continuity_pt_filterlim.
    apply continuity_pt_sqrt.
    pose proof E_min_pos as H. lra.
  Qed.

End EnergyResolvedKineticParams.

Module EnergyResolvedKineticFramework :=
  KineticFramework EnergyResolvedKineticParams.

(* ================================================================== *)
(* === Re-export of the kinetic upper bound at the new instance === *)
(* ================================================================== *)

Theorem energy_resolved_kinetic_multiplication_bound :
  forall R_prim n_B S tau,
    0 < R_prim -> 0 < n_B -> 0 < S -> 0 < tau ->
    EnergyResolvedKineticFramework.R_secondary_kinetic n_B S tau / R_prim <=
    EnergyResolvedKineticFramework.n_alpha_kinetic S tau * n_B *
      (EnergyResolvedKineticParams.sigma_E_max *
       EnergyResolvedKineticParams.v_E_max) / R_prim.
Proof.
  exact EnergyResolvedKineticFramework.multiplication_factor_kinetic_bound.
Qed.

(* ================================================================== *)
(* === Item 13: numerical FoM_max at SW+energy-resolved kinetic === *)
(* ================================================================== *)

(* The sigma_max * v_max product at the energy-resolved instance is
   exactly 1/5000000 = 2 * 10^{-7}. This is the per-alpha contribution
   to the figure of merit. *)
Theorem energy_resolved_sigma_v_max :
  EnergyResolvedKineticParams.sigma_E_max *
    EnergyResolvedKineticParams.v_E_max = 1 / 5000000.
Proof.
  unfold EnergyResolvedKineticParams.sigma_E_max,
         EnergyResolvedKineticParams.v_E_max.
  field.
Qed.

(* The figure-of-merit ceiling at SW+energy-resolved kinetic,
   parametrised by R_primary, n_B, S = sigma_v_pB_thermal, tau =
   tau_slow_alpha, is bounded by
     n_alpha * n_B * (1/5000000) / R_prim.
   This is the numerical content of item 13. *)
Theorem energy_resolved_kinetic_FoM_numerical :
  forall R_prim n_B S tau,
    0 < R_prim -> 0 < n_B -> 0 < S -> 0 < tau ->
    EnergyResolvedKineticFramework.R_secondary_kinetic n_B S tau / R_prim <=
    EnergyResolvedKineticFramework.n_alpha_kinetic S tau * n_B *
      (1 / 5000000) / R_prim.
Proof.
  intros R_prim n_B S tau HR HnB HS Htau.
  rewrite <- energy_resolved_sigma_v_max.
  exact (energy_resolved_kinetic_multiplication_bound
            R_prim n_B S tau HR HnB HS Htau).
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions energy_resolved_kinetic_multiplication_bound.
