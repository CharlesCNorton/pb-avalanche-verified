(******************************************************************************)
(*                                                                            *)
(*     WORK IN PROGRESS -- not yet in the build (_CoqProject).                *)
(*     The thermal exp-integral RInt_exp_thermal and the field-equation       *)
(*     derivative is_derive_neg_T_exp compile; continuous_exp_thermal and     *)
(*     the downstream reactivity bounds still have open obligations around     *)
(*     the Coquelicot continuity combinators (continuous_opp / continuous_id  *)
(*     instance resolution). Re-add to _CoqProject once green.                *)
(*                                                                            *)
(*     Maxwellian-averaged reactivity and the temperature dependence          *)
(*     of the primary rate (item 4)                                           *)
(*                                                                            *)
(*     The primary p+11B rate coefficient sigma_v_pB_thermal(T) is the        *)
(*     Maxwell-Boltzmann thermal average of sigma(E) v(E):                     *)
(*                                                                            *)
(*       <sigma v>(T) = integral( sigma(E) v(E) exp(-E/T) dE )                 *)
(*                      / integral( exp(-E/T) dE )                            *)
(*                                                                            *)
(*     over the reactive energy window. This file:                            *)
(*       - evaluates the thermal normalization integral                       *)
(*           integral_0^b exp(-E/T) dE = T (1 - exp(-b/T))                     *)
(*         via the fundamental theorem of calculus with antiderivative        *)
(*         F(E) = -T exp(-E/T);                                               *)
(*       - defines the Maxwellian average and proves it is a genuine          *)
(*         weighted average bounded by the pointwise maximum of sigma*v;       *)
(*       - establishes the primary rate R_primary(T) = n_p n_B <sigma v>(T)   *)
(*         and its monotone response to the reactivity.                       *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.

Open Scope R_scope.

(* ================================================================== *)
(* === Thermal normalization integral === *)
(* ================================================================== *)

(* Antiderivative of the Boltzmann weight: d/dE [ -T exp(-E/T) ] =
   exp(-E/T). *)
Lemma is_derive_neg_T_exp :
  forall T E, T <> 0 ->
    is_derive (fun x : R => - T * exp (- x / T)) E (exp (- E / T)).
Proof.
  intros T E HT.
  auto_derive.
  - exact I.
  - change (- E / T) with (- E * / T).
    field. exact HT.
Qed.

Lemma continuous_exp_thermal :
  forall T E, T <> 0 -> continuous (fun x : R => exp (- x / T)) E.
Proof.
  intros T E HT.
  apply (continuous_comp (fun x : R => - x / T) exp).
  - apply (continuous_mult (fun x : R => - x) (fun _ => / T)).
    + apply continuous_opp. apply continuous_id.
    + apply continuous_const.
  - apply continuous_exp.
Qed.

(* The thermal normalization integral over [0, b]. *)
Theorem RInt_exp_thermal :
  forall T b, 0 < T -> 0 <= b ->
    RInt (fun E : R => exp (- E / T)) 0 b = T * (1 - exp (- b / T)).
Proof.
  intros T b HT Hb.
  assert (HTne : T <> 0) by lra.
  assert (Hir : is_RInt (fun E : R => exp (- E / T)) 0 b
                  (T * (1 - exp (- b / T)))).
  { replace (T * (1 - exp (- b / T))) with
      (minus ((fun x : R => - T * exp (- x / T)) b)
             ((fun x : R => - T * exp (- x / T)) 0)).
    - apply (@is_RInt_derive R_CompleteNormedModule).
      + intros x _. apply is_derive_neg_T_exp. exact HTne.
      + intros x _. apply continuous_exp_thermal. exact HTne.
    - simpl. unfold minus, plus, opp; simpl.
      replace (- 0 / T) with 0 by (field; exact HTne).
      rewrite exp_0. ring. }
  apply is_RInt_unique. exact Hir.
Qed.

Lemma exp_thermal_pos :
  forall T b, 0 < T -> 0 < b -> 0 < T * (1 - exp (- b / T)).
Proof.
  intros T b HT Hb.
  apply Rmult_lt_0_compat; [exact HT |].
  assert (Hinv : 0 < / T) by (apply Rinv_0_lt_compat; exact HT).
  assert (Hneg : - b / T < 0) by (unfold Rdiv; nra).
  pose proof (exp_increasing (- b / T) 0 Hneg) as Hlt.
  rewrite exp_0 in Hlt. lra.
Qed.

(* ================================================================== *)
(* === Maxwellian-averaged reactivity === *)
(* ================================================================== *)

Section ThermalAverage.

(* Reactive energy window [E_lo, E_hi] and the (energy-dependent)
   sigma*v product to be thermally averaged. *)
Variable E_lo E_hi : R.
Hypothesis E_lo_pos : 0 < E_lo.
Hypothesis E_lo_lt_hi : E_lo < E_hi.

Variable sv : R -> R.
Variable sv_max : R.
Hypothesis sv_nonneg : forall E, E_lo <= E <= E_hi -> 0 <= sv E.
Hypothesis sv_bound : forall E, E_lo <= E <= E_hi -> sv E <= sv_max.
Hypothesis sv_continuous : forall E, E_lo <= E <= E_hi -> continuous sv E.

Lemma E_lo_le_hi : E_lo <= E_hi.
Proof. apply Rlt_le. exact E_lo_lt_hi. Qed.

(* The Boltzmann weight is integrable and its integral is positive. *)
Lemma ex_RInt_weight :
  forall T, 0 < T ->
    ex_RInt (fun E : R => exp (- E / T)) E_lo E_hi.
Proof.
  intros T HT.
  apply (@ex_RInt_continuous R_CompleteNormedModule).
  intros x _. apply continuous_exp_thermal. lra.
Qed.

Lemma ex_RInt_sv_weight :
  forall T, 0 < T ->
    ex_RInt (fun E : R => sv E * exp (- E / T)) E_lo E_hi.
Proof.
  intros T HT.
  apply (@ex_RInt_continuous R_CompleteNormedModule).
  intros x Hx.
  rewrite Rmin_left in Hx by (apply E_lo_le_hi).
  rewrite Rmax_right in Hx by (apply E_lo_le_hi).
  apply (continuous_mult sv (fun E => exp (- E / T))).
  - apply sv_continuous. exact Hx.
  - apply continuous_exp_thermal. lra.
Qed.

Lemma weight_integral_pos :
  forall T, 0 < T -> 0 < RInt (fun E : R => exp (- E / T)) E_lo E_hi.
Proof.
  intros T HT.
  apply RInt_gt_0.
  - exact E_lo_lt_hi.
  - intros x _. apply exp_pos.
  - intros x _. apply continuous_exp_thermal. lra.
Qed.

(* The Maxwellian-averaged reactivity at temperature T. *)
Definition reactivity (T : R) : R :=
  RInt (fun E : R => sv E * exp (- E / T)) E_lo E_hi /
  RInt (fun E : R => exp (- E / T)) E_lo E_hi.

(* The reactivity is non-negative. *)
Theorem reactivity_nonneg :
  forall T, 0 < T -> 0 <= reactivity T.
Proof.
  intros T HT.
  unfold reactivity.
  apply Rmult_le_pos.
  - apply RInt_ge_0.
    + apply E_lo_le_hi.
    + apply ex_RInt_sv_weight. exact HT.
    + intros x [Hx1 Hx2].
      apply Rmult_le_pos.
      * apply sv_nonneg. split; lra.
      * apply Rlt_le, exp_pos.
  - apply Rlt_le, Rinv_0_lt_compat, weight_integral_pos. exact HT.
Qed.

(* The reactivity is bounded by the pointwise maximum of sigma*v: a
   thermal average cannot exceed the peak of the averaged quantity. *)
Theorem reactivity_bound :
  forall T, 0 < T -> reactivity T <= sv_max.
Proof.
  intros T HT.
  unfold reactivity.
  pose proof (weight_integral_pos T HT) as Hw_pos.
  (* RInt(sv * w) <= sv_max * RInt(w), then divide *)
  assert (Hnum_le :
    RInt (fun E : R => sv E * exp (- E / T)) E_lo E_hi <=
    sv_max * RInt (fun E : R => exp (- E / T)) E_lo E_hi).
  { assert (Hex_w : ex_RInt (fun E : R => exp (- E / T)) E_lo E_hi)
      by (apply ex_RInt_weight; exact HT).
    assert (Hscal :
      sv_max * RInt (fun E : R => exp (- E / T)) E_lo E_hi =
      RInt (fun E : R => sv_max * exp (- E / T)) E_lo E_hi).
    { symmetry.
      transitivity (RInt (fun E : R =>
                      scal sv_max (exp (- E / T))) E_lo E_hi).
      - apply (@RInt_ext R_CompleteNormedModule).
        intros x _. reflexivity.
      - apply (@RInt_scal R_CompleteNormedModule). exact Hex_w. }
    rewrite Hscal.
    apply RInt_le.
    - apply E_lo_le_hi.
    - apply ex_RInt_sv_weight. exact HT.
    - apply (@ex_RInt_continuous R_CompleteNormedModule).
      intros x _.
      apply (continuous_scal_r sv_max (fun E => exp (- E / T))).
      apply continuous_exp_thermal. lra.
    - intros E [HE1 HE2].
      apply Rmult_le_compat_r; [apply Rlt_le, exp_pos |].
      apply sv_bound. split; lra. }
  apply Rle_trans with
    (sv_max * RInt (fun E : R => exp (- E / T)) E_lo E_hi /
     RInt (fun E : R => exp (- E / T)) E_lo E_hi).
  - unfold Rdiv. apply Rmult_le_compat_r.
    + apply Rlt_le, Rinv_0_lt_compat. exact Hw_pos.
    + exact Hnum_le.
  - assert (Hsimpl :
      sv_max * RInt (fun E : R => exp (- E / T)) E_lo E_hi /
        RInt (fun E : R => exp (- E / T)) E_lo E_hi = sv_max).
    { field. apply Rgt_not_eq. exact Hw_pos. }
    rewrite Hsimpl. apply Rle_refl.
Qed.

(* ================================================================== *)
(* === Temperature dependence of the primary rate === *)
(* ================================================================== *)

(* The primary p+11B fusion rate per unit volume at temperature T:
   R_primary(T) = n_p * n_B * <sigma v>(T). *)
Definition R_primary_thermal (n_p n_B T : R) : R :=
  n_p * n_B * reactivity T.

Theorem R_primary_thermal_nonneg :
  forall n_p n_B T, 0 <= n_p -> 0 <= n_B -> 0 < T ->
    0 <= R_primary_thermal n_p n_B T.
Proof.
  intros n_p n_B T Hnp HnB HT.
  unfold R_primary_thermal.
  apply Rmult_le_pos.
  - apply Rmult_le_pos; assumption.
  - apply reactivity_nonneg. exact HT.
Qed.

(* The primary rate is bounded by the densities times the peak
   reactivity. *)
Theorem R_primary_thermal_bound :
  forall n_p n_B T, 0 <= n_p -> 0 <= n_B -> 0 < T ->
    R_primary_thermal n_p n_B T <= n_p * n_B * sv_max.
Proof.
  intros n_p n_B T Hnp HnB HT.
  unfold R_primary_thermal.
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos; assumption.
  - apply reactivity_bound. exact HT.
Qed.

(* Monotone response: higher reactivity gives higher primary rate at
   fixed densities. *)
Theorem R_primary_thermal_monotone :
  forall n_p n_B T1 T2, 0 <= n_p -> 0 <= n_B -> 0 < T1 -> 0 < T2 ->
    reactivity T1 <= reactivity T2 ->
    R_primary_thermal n_p n_B T1 <= R_primary_thermal n_p n_B T2.
Proof.
  intros n_p n_B T1 T2 Hnp HnB HT1 HT2 Hr.
  unfold R_primary_thermal.
  apply Rmult_le_compat_l; [apply Rmult_le_pos; assumption | exact Hr].
Qed.

End ThermalAverage.

Print Assumptions RInt_exp_thermal.
Print Assumptions reactivity_bound.
Print Assumptions R_primary_thermal_bound.
