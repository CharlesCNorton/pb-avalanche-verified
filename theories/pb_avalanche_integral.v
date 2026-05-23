(******************************************************************************)
(*                                                                            *)
(*     Integral derivation of the alpha-weighted velocity integral bound      *)
(*                                                                            *)
(*     Work in progress: replaces the abstract axiom                          *)
(*     alpha_weighted_integral_uniform_bound from pb_avalanche.v with a       *)
(*     derived theorem via Coquelicot's Riemann integral and its              *)
(*     monotonicity property.                                                 *)
(*                                                                            *)
(*     The abstract section AlphaVelocityIntegral proves the bound            *)
(*     RInt(f * sigma * v) <= sigma_max * v_max * RInt(f) via Coquelicot's    *)
(*     RInt_le, with the scal/Rmult bridge lemmas ex_RInt_scal_R /            *)
(*     RInt_scal_R discharging the typeclass mismatch between Coquelicot's    *)
(*     polymorphic NormedModule [scal] and Stdlib's [Rmult]. The concrete     *)
(*     IntegralParams instantiation discharges the abstract bound by direct   *)
(*     evaluation of RInt_const on the constant cross-section / velocity      *)
(*     functions, producing IntegralSettlement with zero project-local        *)
(*     axioms.                                                                *)
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
(* === Concrete instantiation: uniform distribution, constant sigma/v === *)
(* ================================================================== *)

(* A concrete realization of the PB_AVALANCHE_PARAMS module type in
   which every integral is computed explicitly via Coquelicot's
   RInt_const. The alpha distribution is uniform on the birth-energy
   interval, the knock-on cross section is the constant sigma_max, and
   the alpha velocity is the constant v_max. With these choices the
   alpha-weighted velocity integral evaluates to exactly
   sigma_max * v_max, and the abstract bound axiom of the module type
   is discharged by reflexivity rather than asserted. *)

Module IntegralParams <: PB_AVALANCHE_PARAMS.

  Definition sigma_v_pB_thermal : R -> R := fun _ => 1.

  Lemma sigma_v_pB_thermal_positive :
    forall T, 0 < T -> 0 < sigma_v_pB_thermal T.
  Proof. intros. unfold sigma_v_pB_thermal. lra. Qed.

  Definition sigma_knockon_max : R := 1 / 10000000.

  Lemma sigma_knockon_max_positive : 0 < sigma_knockon_max.
  Proof. unfold sigma_knockon_max. lra. Qed.

  Definition sigma_alpha_p_knockon : CrossSection :=
    fun _ => sigma_knockon_max.

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

  Lemma E_alpha_birth_pos_local : 0 < E_alpha_birth_MeV.
  Proof. unfold E_alpha_birth_MeV, Q_pB_MeV. lra. Qed.

  Lemma E_alpha_birth_neq_0 : E_alpha_birth_MeV <> 0.
  Proof. apply Rgt_not_eq. exact E_alpha_birth_pos_local. Qed.

  (* The alpha-weighted velocity integral defined as a literal RInt:
     the integral of the constant (sigma_max * v_max) over the birth
     interval, divided by the length of the interval. Since both the
     numerator and the integral of 1 are constants, the value computes
     to sigma_max * v_max exactly. *)
  Definition alpha_weighted_secondary_velocity_integral
    (_ : PlasmaState) : R :=
    RInt (fun _ : R => sigma_knockon_max * v_alpha_max)
         0 E_alpha_birth_MeV /
    RInt (fun _ : R => 1) 0 E_alpha_birth_MeV.

  (* RInt of the constant 1 over [0, E_birth] equals E_birth. *)
  Lemma RInt_const_one :
    RInt (fun _ : R => 1) 0 E_alpha_birth_MeV = E_alpha_birth_MeV.
  Proof.
    rewrite RInt_const.
    unfold scal; simpl. unfold mult; simpl.
    rewrite Rminus_0_r. rewrite Rmult_1_r. reflexivity.
  Qed.

  (* RInt of the constant (sigma_max * v_max) over [0, E_birth] equals
     (sigma_max * v_max) * E_birth. *)
  Lemma RInt_const_sv :
    RInt (fun _ : R => sigma_knockon_max * v_alpha_max)
         0 E_alpha_birth_MeV =
    (sigma_knockon_max * v_alpha_max) * E_alpha_birth_MeV.
  Proof.
    rewrite RInt_const.
    unfold scal; simpl. unfold mult; simpl.
    rewrite Rminus_0_r. apply Rmult_comm.
  Qed.

  Lemma alpha_weighted_integral_value :
    forall s, alpha_weighted_secondary_velocity_integral s =
              sigma_knockon_max * v_alpha_max.
  Proof.
    intros s.
    unfold alpha_weighted_secondary_velocity_integral.
    rewrite RInt_const_one, RInt_const_sv.
    field. exact E_alpha_birth_neq_0.
  Qed.

  Lemma alpha_weighted_integral_nonneg :
    forall s, 0 <= alpha_weighted_secondary_velocity_integral s.
  Proof.
    intros s. rewrite alpha_weighted_integral_value.
    apply Rmult_le_pos.
    - apply Rlt_le. exact sigma_knockon_max_positive.
    - apply Rlt_le. exact v_alpha_max_positive.
  Qed.

  Lemma alpha_weighted_integral_uniform_bound :
    forall s, alpha_weighted_secondary_velocity_integral s <=
              sigma_knockon_max * v_alpha_max.
  Proof.
    intros s. rewrite alpha_weighted_integral_value. apply Rle_refl.
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

End IntegralParams.

Module IntegralSettlement := PBAvalancheFramework IntegralParams.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions alpha_velocity_average_bound.
Print Assumptions RInt_fsv_le.
Print Assumptions IntegralSettlement.hora_putvinski_settlement.
Print Assumptions IntegralSettlement.reactor_no_multiplication.
Print Assumptions IntegralParams.alpha_weighted_integral_uniform_bound.
