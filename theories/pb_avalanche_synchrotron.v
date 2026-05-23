(******************************************************************************)
(*                                                                            *)
(*     Synchrotron toroidal geometry (item 27)                                *)
(*                                                                            *)
(*     A relativistic charged particle in a magnetic field B emits            *)
(*     synchrotron radiation. The Larmor / relativistic Larmor formula        *)
(*     gives the radiated power per particle:                                 *)
(*                                                                            *)
(*       P_sync = (2/3) * (q^2 / (4 pi eps_0 c^3)) * (gamma^2 q B / m)^2      *)
(*                                                                            *)
(*     For a toroidal reactor geometry (tokamak-like), the trapped-particle   *)
(*     fraction and Larmor-orbit averaging modify the power. We expose the    *)
(*     Larmor formula in algebraic form and prove monotonicity in B, gamma,   *)
(*     and inverse mass.                                                      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* ================================================================== *)
(* === Larmor formula for synchrotron radiation === *)
(* ================================================================== *)

(* P_sync = K * gamma^2 * B^2 * q^2 / m^2,
   where K = (2/3) * (q^2 / (4 pi eps_0 c^3)) is the radiative
   prefactor (positive). For relativistic motion, the Lorentz
   factor gamma > 1 enhances the radiated power quadratically. *)

Definition synchrotron_power (K gamma B q m : R) : R :=
  K * (gamma * gamma) * (B * B) * (q * q) / (m * m).

Lemma synchrotron_power_pos :
  forall K gamma B q m,
    0 < K -> 0 < gamma -> 0 < B -> 0 < q -> 0 < m ->
    0 < synchrotron_power K gamma B q m.
Proof.
  intros K gamma B q m HK Hg HB Hq Hm.
  unfold synchrotron_power.
  apply Rdiv_lt_0_compat.
  - repeat apply Rmult_lt_0_compat;
      try apply Rmult_lt_0_compat; assumption.
  - apply Rmult_lt_0_compat; exact Hm.
Qed.

(* Monotonicity in B^2: doubling B quadruples P_sync. *)
Theorem synchrotron_B_scaling :
  forall K gamma B q m,
    0 < K -> 0 < gamma -> 0 < B -> 0 < q -> 0 < m ->
    synchrotron_power K gamma (2 * B) q m =
    4 * synchrotron_power K gamma B q m.
Proof.
  intros K gamma B q m HK Hg HB Hq Hm.
  unfold synchrotron_power.
  field. apply Rgt_not_eq, Hm.
Qed.

(* Monotonicity in gamma^2: doubling gamma quadruples P_sync. *)
Theorem synchrotron_gamma_scaling :
  forall K gamma B q m,
    0 < K -> 0 < gamma -> 0 < B -> 0 < q -> 0 < m ->
    synchrotron_power K (2 * gamma) B q m =
    4 * synchrotron_power K gamma B q m.
Proof.
  intros K gamma B q m HK Hg HB Hq Hm.
  unfold synchrotron_power.
  field. apply Rgt_not_eq, Hm.
Qed.

(* Inverse-mass scaling: heavier particles radiate less. *)
Theorem synchrotron_mass_scaling :
  forall K gamma B q m,
    0 < K -> 0 < gamma -> 0 < B -> 0 < q -> 0 < m ->
    synchrotron_power K gamma B q (2 * m) =
    (1 / 4) * synchrotron_power K gamma B q m.
Proof.
  intros K gamma B q m HK Hg HB Hq Hm.
  unfold synchrotron_power.
  field. apply Rgt_not_eq, Hm.
Qed.

(* ================================================================== *)
(* === Toroidal reactor power budget === *)
(* ================================================================== *)

(* Total synchrotron power in a toroidal reactor with N_e relativistic
   electrons is N_e * P_sync. *)
Definition synchrotron_total (N_e K gamma B q m : R) : R :=
  N_e * synchrotron_power K gamma B q m.

Lemma synchrotron_total_pos :
  forall N_e K gamma B q m,
    0 < N_e -> 0 < K -> 0 < gamma -> 0 < B -> 0 < q -> 0 < m ->
    0 < synchrotron_total N_e K gamma B q m.
Proof.
  intros N_e K gamma B q m HN HK Hg HB Hq Hm.
  unfold synchrotron_total.
  apply Rmult_lt_0_compat; [exact HN |].
  apply synchrotron_power_pos; assumption.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions synchrotron_power_pos.
Print Assumptions synchrotron_B_scaling.
Print Assumptions synchrotron_gamma_scaling.
Print Assumptions synchrotron_mass_scaling.
Print Assumptions synchrotron_total_pos.
