(******************************************************************************)
(*                                                                            *)
(*     Laser-driven regime explicit out-of-scope (item 27)                    *)
(*                                                                            *)
(*     Defines the Hora-style laser-driven fast-ignition regime               *)
(*       n_B in [10^21, 10^23] cm^-3, tau in [10^-12, 10^-6] s                *)
(*     and demonstrates that PhysicalSettlement's subcriticality conclusion   *)
(*     does NOT extend to this regime: an explicit "avalanching" witness      *)
(*     state with n_B = 10^22 and tau = 10^-6 has the composite product       *)
(*     3 * n_B * tau * (sigma_max * v_max) above unity.                       *)
(*                                                                            *)
(*     This formally identifies the Hora claim as a genuine open question     *)
(*     above the magnetic-confinement parameter envelope.                     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From PBAvalanche Require Import pb_avalanche pb_avalanche_kinetic
                                pb_avalanche_envelope.

Open Scope R_scope.

(* ================================================================== *)
(* === The laser-driven parameter regime === *)
(* ================================================================== *)

Definition laser_n_B_min : R := 1000000000000000000000.    (* 10^21 cm^-3 *)
Definition laser_n_B_max : R := 100000000000000000000000.  (* 10^23 cm^-3 *)
Definition laser_tau_min : R := 1 / 1000000000000.         (* 10^-12 s   *)
Definition laser_tau_max : R := 1 / 1000000.               (* 10^-6 s    *)

Lemma laser_n_B_min_pos : 0 < laser_n_B_min.
Proof. unfold laser_n_B_min. lra. Qed.

Lemma laser_tau_max_pos : 0 < laser_tau_max.
Proof. unfold laser_tau_max. lra. Qed.

(* ================================================================== *)
(* === Avalanching witness in the laser regime === *)
(* ================================================================== *)

(* At n_B = 10^22 cm^-3 and tau = 10^-6 s, the composite product
   3 * n_B * tau * sigma_max * v_max exceeds unity with the physical
   IAEA-scale cross section (sigma_max = 10^-25, v_max = 10^9 in cgs):

   3 * 10^22 * 10^-6 * 10^-25 * 10^9 = 3 * 10^0 = 3 > 1.

   This is the formal violation: the "subcritical product" condition
   fails in the laser regime. *)

Definition laser_witness_n_B : R := 10000000000000000000000.    (* 10^22 *)
Definition laser_witness_tau : R := 1 / 1000000.                (* 10^-6 *)

Lemma laser_witness_n_B_pos : 0 < laser_witness_n_B.
Proof. unfold laser_witness_n_B. lra. Qed.

Lemma laser_witness_tau_pos : 0 < laser_witness_tau.
Proof. unfold laser_witness_tau. lra. Qed.

(* The composite product at the laser witness: 3 * 10^22 * 10^-6 * 10^-16
   = 3 * 10^0 = 3. *)
Lemma laser_witness_product :
  3 * laser_witness_tau * laser_witness_n_B * PK.L_kin *
    (PhysicalKineticParams.sigma_E_max * PhysicalKineticParams.v_E_max) =
  3 * PK.L_kin.
Proof.
  unfold laser_witness_tau, laser_witness_n_B.
  rewrite PK_sigma_v_value. lra.
Qed.

(* PK.L_kin = ln 2 < 1, so 3 * L_kin < 3 — but 3 * L_kin > 1 since
   L_kin > 1/3 (i.e., ln 2 > 1/3 ≈ 0.693 > 0.333). The "above unity"
   threshold IS exceeded at this witness even with the small ln 2
   factor. *)

Lemma ln2_gt_one_third : 1 / 3 < ln 2.
Proof.
  (* ln 2 > 0.5 > 1/3 by elementary computation. Use exp_le_3:
     exp 1 > 2, so e > 2, so 1 > ln 2 (we have ln2_lt_1 already).
     For the lower bound, we use ln_2_inv_lt:
     ln 2 > 0.6 by precision of the standard library — but we can't
     easily extract that. Use the integral lower bound:
     ln 2 = integral_1^2 (1/x) dx > integral_1^2 (1/2) dx = 1/2.
     That's >= 1/2 > 1/3. Use a direct route via exp: exp(1/2) <= 2
     iff 1/2 <= ln 2. We have exp(1/2) < e/sqrt(e) = sqrt(e) < sqrt(3)
     < 2 (since 3 < 4 = 2^2). So exp(1/2) < 2, hence 1/2 < ln 2. *)
  apply Rlt_le_trans with (1 / 2); [lra |].
  apply Rnot_lt_le. intro Hcontra.
  (* Hcontra : ln 2 < 1/2 *)
  pose proof (exp_increasing (ln 2) (1/2) Hcontra) as H.
  rewrite exp_ln in H by lra.
  (* H : 2 < exp (1/2) *)
  (* exp(1/2)^2 = exp 1 = e < 3 < 4 = 2^2, contradiction with 2 < exp(1/2) *)
  assert (Hsq : exp (1/2) * exp (1/2) = exp 1).
  { rewrite <- exp_plus. f_equal. lra. }
  pose proof (exp_le_3) as He3.
  nra.
Qed.

Theorem laser_witness_above_unity :
  3 * laser_witness_tau * laser_witness_n_B * PK.L_kin *
    (PhysicalKineticParams.sigma_E_max * PhysicalKineticParams.v_E_max) > 1.
Proof.
  rewrite laser_witness_product.
  pose proof ln2_gt_one_third as Hln23.
  pose proof PK_L_eq_ln2 as HLeq.
  rewrite HLeq. lra.
Qed.

(* The laser-regime witness exceeds n_B_max = 10^14 of the
   PhysicalSettlement reactor regime, so PhysicalSettlement's
   reactor_no_multiplication theorem does NOT apply. The composite
   product is above unity in this regime — the formal statement
   that the avalanche conclusion is open above the magnetic-confinement
   envelope. *)
Theorem laser_witness_outside_magnetic_envelope :
  laser_witness_n_B > 100000000000000.  (* > 10^14 = PhysicalParams.n_B_max_reactor *)
Proof. unfold laser_witness_n_B. lra. Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions laser_witness_product.
Print Assumptions ln2_gt_one_third.
Print Assumptions laser_witness_above_unity.
Print Assumptions laser_witness_outside_magnetic_envelope.
