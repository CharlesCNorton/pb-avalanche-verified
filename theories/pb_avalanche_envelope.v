(******************************************************************************)
(*                                                                            *)
(*     Admissible parameter envelope and the Hora regime                      *)
(*                                                                            *)
(*     Item 7: universal subcriticality across the physically realizable      *)
(*     parameter region. A physical-scale kinetic instance (E_min = E_birth/2 *)
(*     so the kinematic factor L = ln 2 < 1; knock-on cross-section bound      *)
(*     sigma_max = 10^-25 cm^2 from the IAEA scale; alpha velocity bound       *)
(*     v_max = 10^9 cm/s) is fixed, and the admissible region is the set of    *)
(*     plasma parameters with boron density at most 10^14 cm^-3 and            *)
(*     slowing-down time at most 1 s. The multiplication factor is proved      *)
(*     strictly below 1 across the whole region.                              *)
(*                                                                            *)
(*     Item 8: the Hora regime. Hora's avalanche scenario assumes a large      *)
(*     slowing-down/confinement time and a large velocity integral. We         *)
(*     instantiate at Hora's most generous residence time (tau = 1 s, two      *)
(*     orders of magnitude above the realistic ~10^-2 s) and the full          *)
(*     reactor boron density, and prove the multiplication factor is still     *)
(*     below 1. The decisive factor is the magnitude of the knock-on cross     *)
(*     section: even with Hora's generous kinetics, the IAEA-scale             *)
(*     sigma ~ 10^-25 cm^2 keeps the secondary rate subcritical. This is the   *)
(*     formal content of Putvinski's rebuttal.                                *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.

From PBAvalanche Require Import pb_avalanche pb_avalanche_integral
  pb_avalanche_kinetic.

Open Scope R_scope.

(* ================================================================== *)
(* === Physical-scale kinetic instance === *)
(* ================================================================== *)

Module PhysicalKineticParams <: KINETIC_MODEL_PARAMS.

  Definition E_min : R := E_alpha_birth_MeV / 2.

  Lemma E_min_pos : 0 < E_min.
  Proof. unfold E_min, E_alpha_birth_MeV, Q_pB_MeV. lra. Qed.

  Lemma E_min_lt_birth : E_min < E_alpha_birth_MeV.
  Proof. unfold E_min, E_alpha_birth_MeV, Q_pB_MeV. lra. Qed.

  (* sigma_max = 10^-25 cm^2 *)
  Definition sigma_E_max : R := 1 / 10000000000000000000000000.
  (* v_max = 10^9 cm/s *)
  Definition v_E_max : R := 1000000000.

  Lemma sigma_E_max_pos : 0 < sigma_E_max.
  Proof. unfold sigma_E_max. lra. Qed.

  Lemma v_E_max_pos : 0 < v_E_max.
  Proof. unfold v_E_max. lra. Qed.

  Definition sigma_E : R -> R := fun _ => sigma_E_max.
  Definition v_E : R -> R := fun _ => v_E_max.

  Lemma sigma_E_nonneg :
    forall E, E_min <= E <= E_alpha_birth_MeV -> 0 <= sigma_E E.
  Proof. intros. unfold sigma_E. apply Rlt_le, sigma_E_max_pos. Qed.

  Lemma v_E_nonneg :
    forall E, E_min <= E <= E_alpha_birth_MeV -> 0 <= v_E E.
  Proof. intros. unfold v_E. apply Rlt_le, v_E_max_pos. Qed.

  Lemma sigma_E_bound :
    forall E, E_min <= E <= E_alpha_birth_MeV -> sigma_E E <= sigma_E_max.
  Proof. intros. unfold sigma_E. apply Rle_refl. Qed.

  Lemma v_E_bound :
    forall E, E_min <= E <= E_alpha_birth_MeV -> v_E E <= v_E_max.
  Proof. intros. unfold v_E. apply Rle_refl. Qed.

  Definition sigma_E_min_val : R := sigma_E_max.
  Definition v_E_min_val : R := v_E_max.

  Lemma sigma_E_min_nonneg : 0 <= sigma_E_min_val.
  Proof. unfold sigma_E_min_val. apply Rlt_le, sigma_E_max_pos. Qed.

  Lemma v_E_min_nonneg : 0 <= v_E_min_val.
  Proof. unfold v_E_min_val. apply Rlt_le, v_E_max_pos. Qed.

  Lemma sigma_E_lower :
    forall E, E_min <= E <= E_alpha_birth_MeV -> sigma_E_min_val <= sigma_E E.
  Proof. intros. unfold sigma_E_min_val, sigma_E. apply Rle_refl. Qed.

  Lemma v_E_lower :
    forall E, E_min <= E <= E_alpha_birth_MeV -> v_E_min_val <= v_E E.
  Proof. intros. unfold v_E_min_val, v_E. apply Rle_refl. Qed.

  Lemma sigma_E_continuous_on :
    forall E, E_min <= E <= E_alpha_birth_MeV -> continuous sigma_E E.
  Proof. intros. unfold sigma_E. apply continuous_const. Qed.

  Lemma v_E_continuous_on :
    forall E, E_min <= E <= E_alpha_birth_MeV -> continuous v_E E.
  Proof. intros. unfold v_E. apply continuous_const. Qed.

End PhysicalKineticParams.

Module PK := KineticFramework PhysicalKineticParams.

(* ================================================================== *)
(* === The kinematic factor L = ln 2 < 1 === *)
(* ================================================================== *)

Lemma ln2_lt_1 : ln 2 < 1.
Proof.
  rewrite <- (ln_exp 1).
  apply ln_increasing.
  - lra.
  - pose proof (exp_ineq1 1 ltac:(lra)) as H. lra.
Qed.

Lemma PK_L_eq_ln2 : PK.L_kin = ln 2.
Proof.
  unfold PK.L_kin, PhysicalKineticParams.E_min.
  rewrite ln_div.
  - ring.
  - unfold E_alpha_birth_MeV, Q_pB_MeV. lra.
  - lra.
Qed.

Lemma PK_L_lt_1 : PK.L_kin < 1.
Proof. rewrite PK_L_eq_ln2. exact ln2_lt_1. Qed.

Lemma PK_L_pos : 0 < PK.L_kin.
Proof. exact PK.L_kin_pos. Qed.

(* sigma_max * v_max = 10^-25 * 10^9 = 10^-16 *)
Lemma PK_sigma_v_value :
  PhysicalKineticParams.sigma_E_max * PhysicalKineticParams.v_E_max =
  1 / 10000000000000000.
Proof.
  unfold PhysicalKineticParams.sigma_E_max, PhysicalKineticParams.v_E_max.
  field.
Qed.

(* ================================================================== *)
(* === Admissible parameter envelope (item 7) === *)
(* ================================================================== *)

(* The physically realizable region: positive plasma parameters with
   boron density at most 10^14 cm^-3 and slowing-down time at most 1 s.
   These are the operational bounds of a magnetic-confinement reactor. *)
Definition admissible (R_prim n_B tau : R) : Prop :=
  0 < R_prim /\ 0 < n_B /\ 0 < tau /\
  n_B <= 100000000000000 /\ tau <= 1.

(* The composite kinematic product stays strictly below 1 across the
   whole admissible region: the small IAEA-scale cross section dominates
   the bound. *)
Lemma admissible_product_subcritical :
  forall R_prim n_B tau, admissible R_prim n_B tau ->
    3 * tau * n_B * PK.L_kin *
      (PhysicalKineticParams.sigma_E_max * PhysicalKineticParams.v_E_max) < 1.
Proof.
  intros R_prim n_B tau (HR & HnB & Htau & HnBmax & Htaumax).
  rewrite PK_sigma_v_value.
  pose proof PK_L_lt_1 as HL1.
  pose proof PK_L_pos as HLpos.
  (* Bound each factor by its maximum: tau<=1, n_B<=10^14, L<1. *)
  apply Rle_lt_trans with
    (3 * 1 * 100000000000000 * 1 * (1 / 10000000000000000)).
  - apply Rmult_le_compat_r; [lra |].
    apply Rmult_le_compat.
    + repeat apply Rmult_le_pos; lra.
    + lra.
    + apply Rmult_le_compat.
      * repeat apply Rmult_le_pos; lra.
      * lra.
      * apply Rmult_le_compat_l; [lra | exact Htaumax].
      * exact HnBmax.
    + lra.
  - lra.
Qed.

(* Universal subcriticality: the multiplication factor is strictly below
   1 at every plasma state in the admissible region. *)
Theorem envelope_subcritical :
  forall R_prim n_B tau, admissible R_prim n_B tau ->
    PK.R_secondary_kinetic n_B (3 * R_prim) tau / R_prim < 1.
Proof.
  intros R_prim n_B tau Hadm.
  pose proof Hadm as Hadm2.
  destruct Hadm2 as (HR & HnB & Htau & HnBmax & Htaumax).
  apply PK.kinetic_no_avalanche; [exact HR | exact HnB | exact Htau |].
  exact (admissible_product_subcritical R_prim n_B tau Hadm).
Qed.

(* ================================================================== *)
(* === The Hora regime (item 8) === *)
(* ================================================================== *)

(* Hora's avalanche scenario posits a large slowing-down/confinement
   time. We take tau = 1 s, two orders of magnitude above the realistic
   ~10^-2 s, together with the full reactor boron density 10^14 cm^-3.
   These are Hora's most generous kinetic assumptions. *)
Definition hora_tau : R := 1.
Definition hora_n_B : R := 100000000000000.

(* Hora's parameters lie within the admissible envelope: the generous
   residence time saturates the bound but does not exceed it. *)
Lemma hora_admissible :
  forall R_prim, 0 < R_prim -> admissible R_prim hora_n_B hora_tau.
Proof.
  intros R_prim HR.
  unfold admissible, hora_n_B, hora_tau.
  repeat split; lra.
Qed.

(* Even at Hora's generous residence time and full reactor density, the
   multiplication factor is strictly below 1. The IAEA-scale knock-on
   cross section is what settles it: this is Putvinski's rebuttal,
   formalized. *)
Theorem hora_regime_no_avalanche :
  forall R_prim, 0 < R_prim ->
    PK.R_secondary_kinetic hora_n_B (3 * R_prim) hora_tau / R_prim < 1.
Proof.
  intros R_prim HR.
  apply envelope_subcritical.
  apply hora_admissible. exact HR.
Qed.

(* ================================================================== *)
(* === Magnetic-field-threaded ITER witness (item 8) === *)
(* ================================================================== *)

(* Until now, the witness states in pb_avalanche.v have B_T set to a
   positive constant (1 Tesla) which is consumed only by the
   PlasmaState positivity requirement and not by the kinematic bound.
   The kinetic framework's tau_eff_B machinery (tau_eff_B tau_slow
   kappa B) lets the magnetic field appear in the effective residence
   time via the harmonic combination 1/tau_eff = 1/tau_slow +
   1/tau_confine, where tau_confine ∝ B². Stronger B → longer
   residence, but capped by the slowing-down ceiling. Here we exhibit a
   concrete ITER-class witness at B = 5 T, kappa = 1 (a kinematic
   coupling constant), and tau_slow = 1 s (Hora-generous), and show the
   resulting multiplication factor lies below 1. *)

Definition iter_B : R := 5.        (* ITER-class field strength, Tesla. *)
Definition iter_kappa : R := 1.    (* Kinematic coupling. *)
Definition iter_tau_slow : R := 1. (* Hora-generous slowing-down time. *)
Definition iter_n_B : R := 100000000000000. (* 10^14 cm^-3. *)

Lemma iter_B_pos : 0 < iter_B.
Proof. unfold iter_B. lra. Qed.

Lemma iter_kappa_pos : 0 < iter_kappa.
Proof. unfold iter_kappa. lra. Qed.

Lemma iter_tau_slow_pos : 0 < iter_tau_slow.
Proof. unfold iter_tau_slow. lra. Qed.

Lemma iter_n_B_pos : 0 < iter_n_B.
Proof. unfold iter_n_B. lra. Qed.

(* The composite kinematic product (with tau_slow as the upper-bound
   residence time, in place of the harmonically-combined tau_eff_B) is
   strictly subcritical at the ITER-class parameters. *)
Lemma iter_product_subcritical :
  3 * iter_tau_slow * iter_n_B * PK.L_kin *
    (PhysicalKineticParams.sigma_E_max * PhysicalKineticParams.v_E_max) < 1.
Proof.
  unfold iter_tau_slow, iter_n_B.
  rewrite PK_sigma_v_value.
  pose proof PK_L_lt_1 as HL1.
  pose proof PK_L_pos as HLpos.
  nra.
Qed.

(* The ITER-class witness theorem: at B = 5 T, with the effective
   residence time taken as the harmonic combination of the
   slowing-down time and the field-dependent confinement time, the
   multiplication factor stays strictly below 1. This is the
   field-threaded counterpart to hora_regime_no_avalanche. *)
Theorem iter_witness_no_avalanche :
  forall R_prim, 0 < R_prim ->
    PK.R_secondary_kinetic iter_n_B (3 * R_prim)
                           (PK.tau_eff_B iter_tau_slow iter_kappa iter_B)
      / R_prim < 1.
Proof.
  intros R_prim HR.
  apply PK.B_field_no_avalanche.
  - exact HR.
  - exact iter_n_B_pos.
  - exact iter_tau_slow_pos.
  - exact iter_kappa_pos.
  - exact iter_B_pos.
  - exact iter_product_subcritical.
Qed.

(* Monotonicity in B at the witness parameters: doubling the field
   strength from 5 T to 10 T can only increase the effective
   residence time, hence the multiplication factor remains bounded. *)
Theorem iter_witness_monotone_in_B :
  forall B1 B2, 0 < B1 -> B1 <= B2 ->
    PK.tau_eff_B iter_tau_slow iter_kappa B1 <=
    PK.tau_eff_B iter_tau_slow iter_kappa B2.
Proof.
  intros B1 B2 HB1 HB12.
  apply PK.residence_monotone_in_B.
  - exact iter_tau_slow_pos.
  - exact iter_kappa_pos.
  - exact HB1.
  - exact HB12.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions envelope_subcritical.
Print Assumptions hora_regime_no_avalanche.
Print Assumptions admissible_product_subcritical.
Print Assumptions PK_L_lt_1.
Print Assumptions iter_witness_no_avalanche.
Print Assumptions iter_witness_monotone_in_B.
