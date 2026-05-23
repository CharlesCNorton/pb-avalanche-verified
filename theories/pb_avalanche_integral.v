(******************************************************************************)
(*                                                                            *)
(*     Integral derivation of the alpha-weighted velocity integral bound      *)
(*                                                                            *)
(*     Work in progress: replaces the abstract axiom                          *)
(*     alpha_weighted_integral_uniform_bound from pb_avalanche.v with a       *)
(*     derived theorem via Coquelicot's Riemann integral and its              *)
(*     monotonicity property.                                                 *)
(*                                                                            *)
(*     Status: the abstract section AlphaVelocityIntegral compiles and        *)
(*     proves the bound RInt(f * sigma * v) <= sigma_max * v_max * RInt(f)    *)
(*     via Coquelicot's RInt_le, with the scal/Rmult bridge lemmas            *)
(*     ex_RInt_scal_R / RInt_scal_R discharging the typeclass mismatch        *)
(*     between Coquelicot's polymorphic NormedModule [scal] and Stdlib's      *)
(*     [Rmult]. The concrete IntegralParams instantiation that would          *)
(*     produce a fully-grounded IntegralSettlement still has open obligations *)
(*     around the ex_RInt of the product integrand under the uniform          *)
(*     distribution; the kinetic content of the bound itself is settled.      *)
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
(* === Integral-based velocity integral and its derived bound === *)
(* ================================================================== *)

Section AlphaVelocityIntegral.

(* Plasma state-dependent alpha distribution f_alpha (un-normalized). *)
Variable f : PlasmaState -> R -> R.

(* Knock-on cross section and alpha velocity as functions of energy. *)
Variable sigma : R -> R.
Variable v_alpha_fn : R -> R.

(* Uniform upper bounds. *)
Variable sigma_max v_max : R.

Hypothesis sigma_max_nonneg : 0 <= sigma_max.
Hypothesis v_max_nonneg : 0 <= v_max.

Hypothesis sigma_nonneg :
  forall E, 0 <= E <= E_alpha_birth_MeV -> 0 <= sigma E.
Hypothesis sigma_bound :
  forall E, 0 <= E <= E_alpha_birth_MeV -> sigma E <= sigma_max.
Hypothesis v_nonneg :
  forall E, 0 <= E <= E_alpha_birth_MeV -> 0 <= v_alpha_fn E.
Hypothesis v_bound :
  forall E, 0 <= E <= E_alpha_birth_MeV -> v_alpha_fn E <= v_max.
Hypothesis f_nonneg :
  forall s E, 0 <= E <= E_alpha_birth_MeV -> 0 <= f s E.

(* Integrability. *)
Hypothesis ex_RInt_f :
  forall s, ex_RInt (f s) 0 E_alpha_birth_MeV.
Hypothesis ex_RInt_fsv :
  forall s, ex_RInt
    (fun E => f s E * (sigma E * v_alpha_fn E)) 0 E_alpha_birth_MeV.

(* Normalization: the integral of f over the birth-energy interval is
   strictly positive (so the average is well-defined). *)
Hypothesis f_int_pos :
  forall s, 0 < RInt (f s) 0 E_alpha_birth_MeV.

Lemma E_alpha_birth_pos : 0 < E_alpha_birth_MeV.
Proof. unfold E_alpha_birth_MeV, Q_pB_MeV. lra. Qed.

(* === Pointwise bound on the integrand === *)

Lemma fsv_pointwise_bound :
  forall s E, 0 <= E <= E_alpha_birth_MeV ->
    f s E * (sigma E * v_alpha_fn E) <= f s E * (sigma_max * v_max).
Proof.
  intros s E HE.
  apply Rmult_le_compat_l.
  - exact (f_nonneg s E HE).
  - apply Rmult_le_compat.
    + exact (sigma_nonneg E HE).
    + exact (v_nonneg E HE).
    + exact (sigma_bound E HE).
    + exact (v_bound E HE).
Qed.

(* Bridge between Coquelicot's polymorphic [scal] (over a normed
   module) and Stdlib's [Rmult] for the special case where the
   normed module is R itself. The two are definitionally equal but
   Coq's unifier does not always reduce through the typeclass
   instance, so we mediate via [ex_RInt_ext] / [RInt_ext]. *)

Lemma scal_R_eq : forall (k x : R), scal k x = k * x.
Proof. intros k x. reflexivity. Qed.

Lemma ex_RInt_scal_R :
  forall (h : R -> R) (a b : R) (k : R),
    ex_RInt h a b -> ex_RInt (fun x => k * h x) a b.
Proof.
  intros h a b k Hex.
  apply ex_RInt_ext with
    (f := fun y : R => @scal R_Ring R_ModuleSpace k (h y)).
  - intros x _. reflexivity.
  - exact (@ex_RInt_scal R_NormedModule h a b k Hex).
Qed.

Lemma RInt_scal_R :
  forall (h : R -> R) (a b : R) (k : R),
    ex_RInt h a b ->
    RInt (fun x => k * h x) a b = k * RInt h a b.
Proof.
  intros h a b k Hex.
  transitivity (RInt (fun y : R => @scal R_Ring R_ModuleSpace k (h y)) a b).
  - apply RInt_ext. intros x _. reflexivity.
  - exact (@RInt_scal R_CompleteNormedModule h a b k Hex).
Qed.

(* === Integral bound via Coquelicot RInt_le === *)

Lemma RInt_fsv_le :
  forall s,
    RInt (fun E => f s E * (sigma E * v_alpha_fn E)) 0 E_alpha_birth_MeV <=
    sigma_max * v_max * RInt (f s) 0 E_alpha_birth_MeV.
Proof.
  intros s.
  pose proof E_alpha_birth_pos as Hbirth.
  assert (Hex_scaled : ex_RInt
    (fun E => (sigma_max * v_max) * f s E) 0 E_alpha_birth_MeV).
  { apply ex_RInt_scal_R. exact (ex_RInt_f s). }
  assert (Hscal_eq :
    (sigma_max * v_max) * RInt (f s) 0 E_alpha_birth_MeV =
    RInt (fun E => (sigma_max * v_max) * f s E) 0 E_alpha_birth_MeV).
  { symmetry. apply RInt_scal_R. exact (ex_RInt_f s). }
  rewrite Hscal_eq.
  apply RInt_le.
  - apply Rlt_le. exact Hbirth.
  - exact (ex_RInt_fsv s).
  - exact Hex_scaled.
  - intros E [HE1 HE2].
    rewrite (Rmult_comm (sigma_max * v_max) (f s E)).
    apply fsv_pointwise_bound. split; lra.
Qed.

(* === Definition of the velocity-weighted average === *)

Definition alpha_velocity_average (s : PlasmaState) : R :=
  RInt (fun E => f s E * (sigma E * v_alpha_fn E)) 0 E_alpha_birth_MeV /
  RInt (f s) 0 E_alpha_birth_MeV.

Lemma alpha_velocity_average_nonneg :
  forall s, 0 <= alpha_velocity_average s.
Proof.
  intros s.
  unfold alpha_velocity_average.
  apply Rmult_le_pos.
  - apply RInt_ge_0.
    + apply Rlt_le. exact E_alpha_birth_pos.
    + exact (ex_RInt_fsv s).
    + intros x [Hx0 Hx1].
      apply Rmult_le_pos.
      * apply (f_nonneg s). split; lra.
      * apply Rmult_le_pos.
        ** apply (sigma_nonneg x). split; lra.
        ** apply (v_nonneg x). split; lra.
  - apply Rlt_le. apply Rinv_0_lt_compat. exact (f_int_pos s).
Qed.

(* === Main derived theorem: the average is bounded by sigma_max * v_max === *)

Theorem alpha_velocity_average_bound :
  forall s, alpha_velocity_average s <= sigma_max * v_max.
Proof.
  intros s.
  unfold alpha_velocity_average.
  pose proof (f_int_pos s) as Hf_pos.
  pose proof (RInt_fsv_le s) as Hint_le.
  apply Rle_trans with
    (sigma_max * v_max * RInt (f s) 0 E_alpha_birth_MeV /
     RInt (f s) 0 E_alpha_birth_MeV).
  - unfold Rdiv. apply Rmult_le_compat_r.
    + apply Rlt_le. apply Rinv_0_lt_compat. exact Hf_pos.
    + exact Hint_le.
  - assert (Hsimpl :
      sigma_max * v_max * RInt (f s) 0 E_alpha_birth_MeV /
        RInt (f s) 0 E_alpha_birth_MeV = sigma_max * v_max).
    { field. apply Rgt_not_eq. exact Hf_pos. }
    rewrite Hsimpl. apply Rle_refl.
Qed.

End AlphaVelocityIntegral.

(* ================================================================== *)
(* === Print Assumptions audit for the derived integral bound === *)
(* ================================================================== *)

Print Assumptions alpha_velocity_average_bound.
Print Assumptions RInt_fsv_le.
