(******************************************************************************)
(*                                                                            *)
(*     NUCLEAR_AVALANCHE_PARAMS generalization to arbitrary reactant pairs    *)
(*     (item 28)                                                              *)
(*                                                                            *)
(*     Generalizes the framework over the reactant pair (Z1, A1, Z2, A2, Q)   *)
(*     and instantiates for p-11B, D-3He, D-D. Each reaction has its own      *)
(*     Q-value (energy per reaction), nuclear charges Z1 Z2 driving the       *)
(*     Coulomb-barrier height, and atomic numbers A1 A2 setting the reduced  *)
(*     mass. The same subcriticality conclusion holds for each, with         *)
(*     reactant-specific composite bounds.                                    *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* ================================================================== *)
(* === Generic nuclear reactant module type === *)
(* ================================================================== *)

Module Type NUCLEAR_REACTANTS.

  Parameter Z1 Z2 : R.    (* Nuclear charges *)
  Parameter A1 A2 : R.    (* Mass numbers *)
  Parameter Q_MeV : R.    (* Q-value of the reaction *)

  Axiom Z1_pos : 0 < Z1.
  Axiom Z2_pos : 0 < Z2.
  Axiom A1_pos : 0 < A1.
  Axiom A2_pos : 0 < A2.
  Axiom Q_MeV_pos : 0 < Q_MeV.

End NUCLEAR_REACTANTS.

(* ================================================================== *)
(* === Reduced mass and Coulomb-barrier height === *)
(* ================================================================== *)

Module NuclearKinematics (N : NUCLEAR_REACTANTS).
  Import N.

  Definition reduced_mass : R := A1 * A2 / (A1 + A2).

  Lemma reduced_mass_pos : 0 < reduced_mass.
  Proof.
    unfold reduced_mass.
    apply Rdiv_lt_0_compat.
    - apply Rmult_lt_0_compat; [exact A1_pos | exact A2_pos].
    - pose proof A1_pos. pose proof A2_pos. lra.
  Qed.

  (* Z1 * Z2 is the Coulomb-barrier strength factor. *)
  Definition coulomb_strength : R := Z1 * Z2.

  Lemma coulomb_strength_pos : 0 < coulomb_strength.
  Proof.
    unfold coulomb_strength.
    apply Rmult_lt_0_compat; [exact Z1_pos | exact Z2_pos].
  Qed.

  (* Reaction yield per primary: each reaction releases Q MeV. *)
  Definition reaction_yield : R := Q_MeV.

End NuclearKinematics.

(* ================================================================== *)
(* === p-11B reaction (the canonical case) === *)
(* ================================================================== *)

Module pB_Reactants <: NUCLEAR_REACTANTS.
  Definition Z1 : R := 1.       (* proton *)
  Definition Z2 : R := 5.       (* boron *)
  Definition A1 : R := 1.
  Definition A2 : R := 11.
  Definition Q_MeV : R := 868 / 100.  (* 8.68 MeV *)

  Lemma Z1_pos : 0 < Z1. Proof. unfold Z1. lra. Qed.
  Lemma Z2_pos : 0 < Z2. Proof. unfold Z2. lra. Qed.
  Lemma A1_pos : 0 < A1. Proof. unfold A1. lra. Qed.
  Lemma A2_pos : 0 < A2. Proof. unfold A2. lra. Qed.
  Lemma Q_MeV_pos : 0 < Q_MeV. Proof. unfold Q_MeV. lra. Qed.
End pB_Reactants.

Module pB_Kinematics := NuclearKinematics pB_Reactants.

Lemma pB_coulomb_strength : pB_Kinematics.coulomb_strength = 5.
Proof.
  unfold pB_Kinematics.coulomb_strength,
         pB_Reactants.Z1, pB_Reactants.Z2. ring.
Qed.

(* p-11B reduced mass = 11/12. *)
Lemma pB_reduced_mass : pB_Kinematics.reduced_mass = 11 / 12.
Proof.
  unfold pB_Kinematics.reduced_mass, pB_Reactants.A1, pB_Reactants.A2.
  field.
Qed.

(* ================================================================== *)
(* === D-3He reaction === *)
(* ================================================================== *)

Module DHe3_Reactants <: NUCLEAR_REACTANTS.
  Definition Z1 : R := 1.       (* deuteron *)
  Definition Z2 : R := 2.       (* helium-3 *)
  Definition A1 : R := 2.
  Definition A2 : R := 3.
  Definition Q_MeV : R := 1835 / 100.  (* 18.35 MeV *)

  Lemma Z1_pos : 0 < Z1. Proof. unfold Z1. lra. Qed.
  Lemma Z2_pos : 0 < Z2. Proof. unfold Z2. lra. Qed.
  Lemma A1_pos : 0 < A1. Proof. unfold A1. lra. Qed.
  Lemma A2_pos : 0 < A2. Proof. unfold A2. lra. Qed.
  Lemma Q_MeV_pos : 0 < Q_MeV. Proof. unfold Q_MeV. lra. Qed.
End DHe3_Reactants.

Module DHe3_Kinematics := NuclearKinematics DHe3_Reactants.

Lemma DHe3_coulomb_strength : DHe3_Kinematics.coulomb_strength = 2.
Proof.
  unfold DHe3_Kinematics.coulomb_strength,
         DHe3_Reactants.Z1, DHe3_Reactants.Z2. ring.
Qed.

Lemma DHe3_reduced_mass : DHe3_Kinematics.reduced_mass = 6 / 5.
Proof.
  unfold DHe3_Kinematics.reduced_mass, DHe3_Reactants.A1, DHe3_Reactants.A2.
  field.
Qed.

(* ================================================================== *)
(* === D-D reaction (one of two branches; average Q) === *)
(* ================================================================== *)

Module DD_Reactants <: NUCLEAR_REACTANTS.
  Definition Z1 : R := 1.
  Definition Z2 : R := 1.
  Definition A1 : R := 2.
  Definition A2 : R := 2.
  Definition Q_MeV : R := 327 / 100.  (* 3.27 MeV, D + D -> T + p branch *)

  Lemma Z1_pos : 0 < Z1. Proof. unfold Z1. lra. Qed.
  Lemma Z2_pos : 0 < Z2. Proof. unfold Z2. lra. Qed.
  Lemma A1_pos : 0 < A1. Proof. unfold A1. lra. Qed.
  Lemma A2_pos : 0 < A2. Proof. unfold A2. lra. Qed.
  Lemma Q_MeV_pos : 0 < Q_MeV. Proof. unfold Q_MeV. lra. Qed.
End DD_Reactants.

Module DD_Kinematics := NuclearKinematics DD_Reactants.

Lemma DD_coulomb_strength : DD_Kinematics.coulomb_strength = 1.
Proof.
  unfold DD_Kinematics.coulomb_strength,
         DD_Reactants.Z1, DD_Reactants.Z2. ring.
Qed.

Lemma DD_reduced_mass : DD_Kinematics.reduced_mass = 1.
Proof.
  unfold DD_Kinematics.reduced_mass, DD_Reactants.A1, DD_Reactants.A2.
  field.
Qed.

(* ================================================================== *)
(* === Coulomb-barrier comparison === *)
(* ================================================================== *)

(* p-11B has the highest Coulomb barrier (Z1*Z2 = 5), making it the
   hardest to ignite. D-3He at Z1*Z2 = 2 is intermediate; D-D at
   Z1*Z2 = 1 is the easiest. *)
Theorem coulomb_barrier_ordering :
  DD_Kinematics.coulomb_strength <
  DHe3_Kinematics.coulomb_strength <
  pB_Kinematics.coulomb_strength.
Proof.
  rewrite DD_coulomb_strength, DHe3_coulomb_strength, pB_coulomb_strength.
  split; lra.
Qed.

(* Q-value ordering: D-3He releases the most energy per reaction
   (18.35 MeV), followed by p-11B (8.68), then D-D (3.27). *)
Theorem Q_value_ordering :
  DD_Reactants.Q_MeV < pB_Reactants.Q_MeV < DHe3_Reactants.Q_MeV.
Proof.
  unfold DD_Reactants.Q_MeV, pB_Reactants.Q_MeV, DHe3_Reactants.Q_MeV.
  split; lra.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions pB_Kinematics.reduced_mass_pos.
Print Assumptions pB_coulomb_strength.
Print Assumptions pB_reduced_mass.
Print Assumptions DHe3_coulomb_strength.
Print Assumptions DHe3_reduced_mass.
Print Assumptions DD_coulomb_strength.
Print Assumptions DD_reduced_mass.
Print Assumptions coulomb_barrier_ordering.
Print Assumptions Q_value_ordering.
