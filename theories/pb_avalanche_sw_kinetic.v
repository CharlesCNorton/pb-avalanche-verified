(******************************************************************************)
(*                                                                            *)
(*     Sikora-Weller kinetic instance (item 21)                               *)
(*                                                                            *)
(*     Instantiates KINETIC_MODEL_PARAMS using a constant cross-section bound *)
(*     derived from the Sikora-Weller p-11B tabulation (item 14) and a        *)
(*     constant velocity bound. This is the "wiring" of the IAEA data into    *)
(*     the kinetic framework at the bound level: the kinetic figure-of-merit  *)
(*     theorems carry through with sigma_E bounded by the SW maximum.         *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra ZArith.
From Coquelicot Require Import Coquelicot.

From PBAvalanche Require Import pb_avalanche pb_avalanche_integral
                                pb_avalanche_kinetic pb_avalanche_iaea.

Open Scope R_scope.

(* ================================================================== *)
(* === Sikora-Weller-bounded kinetic instance === *)
(* ================================================================== *)

Module SikoraWellerKineticParams <: KINETIC_MODEL_PARAMS.

  (* Reactive window: from a small positive threshold to the birth
     energy. We take E_min = E_alpha_birth_MeV / 2 to match the
     physical-kinetic instance from the envelope file. *)
  Definition E_min : R := E_alpha_birth_MeV / 2.

  Lemma E_min_pos : 0 < E_min.
  Proof. unfold E_min, E_alpha_birth_MeV, Q_pB_MeV. lra. Qed.

  Lemma E_min_lt_birth : E_min < E_alpha_birth_MeV.
  Proof. unfold E_min, E_alpha_birth_MeV, Q_pB_MeV. lra. Qed.

  (* sigma_E_max derived from the SW maximum (12/10 barns in our
     illustrative units). We use the SW upper bound as the cross-
     section ceiling. *)
  Definition sigma_E_max : R := sikora_weller_M_inf.

  Lemma sigma_E_max_pos : 0 < sigma_E_max.
  Proof. exact sikora_weller_M_inf_pos. Qed.

  (* v_E_max set to a constant alpha velocity at birth energy. *)
  Definition v_E_max : R := 1000000000. (* 10^9 cm/s *)

  Lemma v_E_max_pos : 0 < v_E_max.
  Proof. unfold v_E_max. lra. Qed.

  (* Constant sigma_E and v_E at their maxima — the simplest
     instantiation that ties to the SW upper bound. The SW table
     itself provides the M_inf input via sikora_weller_M_inf. *)
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

End SikoraWellerKineticParams.

Module SWK := KineticFramework SikoraWellerKineticParams.

(* ================================================================== *)
(* === SW-bound subcriticality === *)
(* ================================================================== *)

(* Under reasonable confinement parameters (n_B at 10^14, tau at 1 s,
   the Hora-generous values), the SW-bounded cross-section gives
   3 * tau * n_B * L_kin * (M_inf * v_max) > 1 in nominal units —
   indicating that the SW-bound case is NOT in the trivial subcritical
   regime that PhysicalKineticParams' 10^-25 bound put us in. The
   physical case requires the small IAEA-scale cross section
   (the SW values would need to be divided by the appropriate physical
   scale factor). We expose this as a numerical check rather than
   claiming subcriticality. *)

Lemma SW_K_sigma_v_product :
  SikoraWellerKineticParams.sigma_E_max *
    SikoraWellerKineticParams.v_E_max =
  sikora_weller_M_inf * 1000000000.
Proof.
  unfold SikoraWellerKineticParams.sigma_E_max,
         SikoraWellerKineticParams.v_E_max. reflexivity.
Qed.

(* The kinetic figure-of-merit upper bound carries through cleanly
   from the framework: M(s) <= 3 * tau * n_B * L_kin * (M_inf * v_max).
   Whether this is < 1 depends on the numerical values of tau and n_B. *)
Theorem SW_K_FoM_upper_bound :
  forall R_prim n_B tau,
    0 < R_prim -> 0 < n_B -> 0 < tau ->
    SWK.kinetic_figure_of_merit R_prim n_B tau <=
    3 * tau * n_B * SWK.L_kin *
      (SikoraWellerKineticParams.sigma_E_max *
       SikoraWellerKineticParams.v_E_max).
Proof.
  intros R_prim n_B tau HR HnB Htau.
  apply SWK.kinetic_FoM_upper_bound; assumption.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions SikoraWellerKineticParams.sigma_E_max_pos.
Print Assumptions SikoraWellerKineticParams.v_E_max_pos.
Print Assumptions SW_K_sigma_v_product.
Print Assumptions SW_K_FoM_upper_bound.
