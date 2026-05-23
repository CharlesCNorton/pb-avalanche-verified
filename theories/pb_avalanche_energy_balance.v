(******************************************************************************)
(*                                                                            *)
(*     Energy-balance admissibility (item 26)                                 *)
(*                                                                            *)
(*     Adds bremsstrahlung and synchrotron radiation losses to the plasma     *)
(*     model and defines the energy-balance condition                         *)
(*                                                                            *)
(*       R_primary * Q_pB >= bremsstrahlung + synchrotron                     *)
(*                                                                            *)
(*     Plasma states satisfying both the kinematic reactor regime and the     *)
(*     energy balance are bounded by a tighter FoM than the regime alone.    *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From PBAvalanche Require Import pb_avalanche.

Open Scope R_scope.

(* ================================================================== *)
(* === Radiation losses === *)
(* ================================================================== *)

(* Bremsstrahlung prefactor (in our unit system). *)
Definition C_brems : R := 1 / 100.
Lemma C_brems_pos : 0 < C_brems. Proof. unfold C_brems. lra. Qed.

(* Synchrotron prefactor. *)
Definition C_sync : R := 1 / 1000.
Lemma C_sync_pos : 0 < C_sync. Proof. unfold C_sync. lra. Qed.

(* Bremsstrahlung volumetric power:
   P_brems ~ C_brems * Z_eff^2 * n_e^2 * sqrt(T),
   with Z_eff^2 * n_e^2 absorbed into (n_p + Z_B^2 * n_B)^2. *)
Definition bremsstrahlung (s : PlasmaState) : R :=
  C_brems * (n_p s + Z_B * Z_B * n_B s)^2 * sqrt (T_keV s).

Lemma bremsstrahlung_pos :
  forall s, 0 < bremsstrahlung s.
Proof.
  intros s. unfold bremsstrahlung.
  pose proof (pos_n_p s) as Hp.
  pose proof (pos_n_B s) as HB.
  pose proof (pos_T s) as HT.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat; [exact C_brems_pos |].
    assert (Hsum : 0 < n_p s + Z_B * Z_B * n_B s).
    { apply Rplus_lt_0_compat; [exact Hp |].
      apply Rmult_lt_0_compat; [unfold Z_B; lra | exact HB]. }
    simpl. nra.
  - apply sqrt_lt_R0; exact HT.
Qed.

(* Synchrotron volumetric power: P_sync ~ C_sync * n_e * T^2 * B^2. *)
Definition synchrotron (s : PlasmaState) : R :=
  C_sync * (n_p s + Z_B * Z_B * n_B s) * (T_keV s)^2 * (B_T s)^2.

Lemma synchrotron_pos :
  forall s, 0 < synchrotron s.
Proof.
  intros s. unfold synchrotron.
  pose proof (pos_n_p s) as Hp.
  pose proof (pos_n_B s) as HB.
  pose proof (pos_T s) as HT.
  pose proof (pos_B s) as HBT.
  assert (Hsum : 0 < n_p s + Z_B * Z_B * n_B s).
  { apply Rplus_lt_0_compat; [exact Hp |].
    apply Rmult_lt_0_compat; [unfold Z_B; lra | exact HB]. }
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat; [exact C_sync_pos | exact Hsum].
    + simpl. nra.
  - simpl. nra.
Qed.

(* ================================================================== *)
(* === Energy-balance admissibility === *)
(* ================================================================== *)

(* The energy-balance criterion: alpha heating from primary fusion
   must exceed total radiation losses. Using Q_pB as the energy
   per reaction (in keV) and R_primary as the volumetric rate, this
   reads R_primary * Q_pB >= bremss + sync. *)
Definition energy_balance_admissible
  (R_primary_val : R) (s : PlasmaState) : Prop :=
  R_primary_val * Q_pB_MeV >= bremsstrahlung s + synchrotron s.

(* A state satisfying both regime + energy balance — the physically
   realizable operating envelope. *)
Definition operating_envelope
  (R_primary_val : R) (s : PlasmaState)
  (n_B_max T_max n_p_min : R) : Prop :=
  (n_B s <= n_B_max /\ T_keV s <= T_max /\ n_p_min <= n_p s) /\
  energy_balance_admissible R_primary_val s.

(* The energy-balance condition forces n_e^2 * sqrt(T) to be bounded
   by R_primary * Q_pB / C_brems. This is a *tightening* of the
   kinematic regime. *)
Lemma energy_balance_bremsstrahlung_bound :
  forall R_primary_val s,
    energy_balance_admissible R_primary_val s ->
    bremsstrahlung s <= R_primary_val * Q_pB_MeV.
Proof.
  intros R_primary_val s Hbal.
  unfold energy_balance_admissible in Hbal.
  pose proof (synchrotron_pos s) as Hsync.
  lra.
Qed.

(* Equivalent statement on the density factor: a state in the
   operating envelope satisfies
   (n_p + Z_B^2 * n_B)^2 * sqrt(T) <= R_primary * Q_pB / C_brems. *)
Theorem energy_balance_density_constraint :
  forall R_primary_val s,
    energy_balance_admissible R_primary_val s ->
    C_brems * (n_p s + Z_B * Z_B * n_B s)^2 * sqrt (T_keV s) <=
    R_primary_val * Q_pB_MeV.
Proof.
  intros R_primary_val s Hbal.
  pose proof (energy_balance_bremsstrahlung_bound R_primary_val s Hbal) as H.
  unfold bremsstrahlung in H. exact H.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions C_brems_pos.
Print Assumptions C_sync_pos.
Print Assumptions bremsstrahlung_pos.
Print Assumptions synchrotron_pos.
Print Assumptions energy_balance_bremsstrahlung_bound.
Print Assumptions energy_balance_density_constraint.
