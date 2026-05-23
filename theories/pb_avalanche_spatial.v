(******************************************************************************)
(*                                                                            *)
(*     Spatial reactor profile via volumetric integration (item 25)           *)
(*                                                                            *)
(*     Promotes the zero-dimensional PlasmaState to a radial profile          *)
(*     PlasmaProfile := R -> PlasmaState. The volumetric multiplication       *)
(*     factor is the radius-weighted average                                  *)
(*                                                                            *)
(*       M_volumetric := integral_0^R r^2 * M(s(r)) dr                        *)
(*                       / integral_0^R r^2 dr                                *)
(*                                                                            *)
(*     For pointwise-subcritical profiles M(s(r)) < 1, the volumetric         *)
(*     average satisfies M_volumetric < 1.                                    *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.

From PBAvalanche Require Import pb_avalanche pb_avalanche_integral.

Open Scope R_scope.

(* ================================================================== *)
(* === Radial plasma profile === *)
(* ================================================================== *)

Definition PlasmaProfile := R -> PlasmaState.

(* The volumetric multiplication factor: r^2-weighted average of M
   over [0, R]. The function M(s) : PlasmaState -> R is the abstract
   multiplication factor for a given plasma state. *)
Definition M_volumetric_integrand
  (M : PlasmaState -> R) (profile : PlasmaProfile) (r : R) : R :=
  r * r * M (profile r).

Definition r_squared (r : R) : R := r * r.

(* The denominator: integral_0^R r^2 dr = R^3 / 3. *)
Lemma RInt_r_squared :
  forall R_max, 0 <= R_max ->
    RInt r_squared 0 R_max = R_max ^ 3 / 3.
Proof.
  intros R_max HR.
  set (F := fun x : R => x * x * x / 3).
  assert (HF_deriv : forall x : R, is_derive F x (r_squared x)).
  { intro x. unfold F, r_squared.
    pose proof (@Derive.is_derive_mult (fun y : R => y * y)
                  (fun y : R => y) x (1*x + x*1) 1) as Hp.
    assert (Hd1 : is_derive (fun y : R => y * y) x (1 * x + x * 1)).
    { apply (@Derive.is_derive_mult (fun y : R => y) (fun y : R => y) x 1 1).
      - apply (@is_derive_id R_AbsRing).
      - apply (@is_derive_id R_AbsRing). }
    assert (Hd2 : is_derive (fun y : R => y) x 1).
    { apply (@is_derive_id R_AbsRing). }
    pose proof (Hp Hd1 Hd2) as Hp'. clear Hp.
    cbv beta in Hp'.
    (* Hp' : is_derive (fun y => y*y * y) x ((1*x+x*1) * x + (x*x) * 1)
       Want: is_derive (fun y => y * y * y / 3) x (x * x). *)
    assert (Hscal : is_derive (fun y : R => y * y * y / 3) x
                              (((1 * x + x * 1) * x + x * x * 1) * / 3)).
    { unfold Rdiv.
      apply (is_derive_scal_l (fun y : R => y * y * y) x _ (/ 3)).
      exact Hp'. }
    assert (Hval : ((1 * x + x * 1) * x + x * x * 1) * / 3 = x * x)
      by field.
    rewrite Hval in Hscal. exact Hscal. }
  assert (Hir : is_RInt r_squared 0 R_max (minus (F R_max) (F 0))).
  { apply (@is_RInt_derive R_CompleteNormedModule F r_squared 0 R_max).
    - intros x _. apply HF_deriv.
    - intros x _. unfold r_squared.
      apply (continuous_mult (fun y : R => y) (fun y : R => y));
        apply continuous_id. }
  rewrite (is_RInt_unique _ _ _ _ Hir).
  unfold minus, plus, opp; simpl. unfold F.
  field.
Qed.

Lemma RInt_r_squared_pos :
  forall R_max, 0 < R_max -> 0 < RInt r_squared 0 R_max.
Proof.
  intros R_max HR.
  rewrite (RInt_r_squared R_max (Rlt_le _ _ HR)).
  assert (HRcube : 0 < R_max ^ 3).
  { replace (R_max ^ 3) with (R_max * R_max * R_max) by (simpl; ring).
    repeat apply Rmult_lt_0_compat; lra. }
  unfold Rdiv.
  apply Rmult_lt_0_compat; [exact HRcube | lra].
Qed.

(* ================================================================== *)
(* === Volumetric multiplication factor === *)
(* ================================================================== *)

Definition M_volumetric (M : PlasmaState -> R) (profile : PlasmaProfile)
                        (R_max : R) : R :=
  RInt (M_volumetric_integrand M profile) 0 R_max /
  RInt r_squared 0 R_max.

(* Pointwise-subcritical implies volumetric-subcritical:
   if M(s) <= K for every plasma state s and K < 1, and the profile
   takes values in PlasmaState, then the volume-weighted average
   M_volumetric <= K < 1. *)
Theorem M_volumetric_pointwise_bound :
  forall M profile R_max K,
    0 < R_max -> K >= 0 ->
    (forall r, 0 <= r <= R_max -> 0 <= M (profile r) <= K) ->
    (forall r, 0 <= r <= R_max -> continuous (M_volumetric_integrand M profile) r) ->
    M_volumetric M profile R_max <= K.
Proof.
  intros M profile R_max K HR HK Hbound Hcont.
  unfold M_volumetric.
  pose proof (RInt_r_squared_pos R_max HR) as Hden_pos.
  assert (Hnum_le :
    RInt (M_volumetric_integrand M profile) 0 R_max <=
    K * RInt r_squared 0 R_max).
  { assert (Hex_int : ex_RInt (M_volumetric_integrand M profile) 0 R_max).
    { apply (@ex_RInt_continuous R_CompleteNormedModule).
      intros x Hx.
      rewrite Rmin_left in Hx by lra.
      rewrite Rmax_right in Hx by lra.
      apply Hcont. lra. }
    assert (Hex_r2 : ex_RInt r_squared 0 R_max).
    { apply (@ex_RInt_continuous R_CompleteNormedModule).
      intros x _. unfold r_squared.
      apply (continuous_mult (fun y : R => y) (fun y : R => y));
        apply continuous_id. }
    transitivity (RInt (fun r => K * r_squared r) 0 R_max).
    - apply RInt_le; [lra | exact Hex_int | |].
      + apply (@ex_RInt_continuous R_CompleteNormedModule).
        intros x _.
        apply (continuous_scal_r K r_squared). unfold r_squared.
        apply (continuous_mult (fun y : R => y) (fun y : R => y));
          apply continuous_id.
      + intros x Hx.
        unfold M_volumetric_integrand, r_squared.
        destruct Hx as [Hx1 Hx2].
        assert (Hx_in : 0 <= x <= R_max) by lra.
        pose proof (Hbound x Hx_in) as [HM1 HM2].
        nra.
    - rewrite RInt_scal_R by exact Hex_r2. apply Rle_refl. }
  apply Rle_trans with
    (K * RInt r_squared 0 R_max / RInt r_squared 0 R_max).
  - unfold Rdiv. apply Rmult_le_compat_r.
    + apply Rlt_le, Rinv_0_lt_compat; exact Hden_pos.
    + exact Hnum_le.
  - assert (Hsimpl : K * RInt r_squared 0 R_max /
                       RInt r_squared 0 R_max = K).
    { field. apply Rgt_not_eq; exact Hden_pos. }
    rewrite Hsimpl. apply Rle_refl.
Qed.

(* For a uniform profile (constant M), the volumetric average is
   exactly M. *)
Theorem M_volumetric_uniform :
  forall M profile R_max M0,
    0 < R_max ->
    (forall r, 0 <= r <= R_max -> M (profile r) = M0) ->
    M_volumetric M profile R_max = M0.
Proof.
  intros M profile R_max M0 HR Hconst.
  unfold M_volumetric.
  pose proof (RInt_r_squared_pos R_max HR) as Hden_pos.
  assert (Hnum :
    RInt (M_volumetric_integrand M profile) 0 R_max =
    M0 * RInt r_squared 0 R_max).
  { assert (Hex_r2 : ex_RInt r_squared 0 R_max).
    { apply (@ex_RInt_continuous R_CompleteNormedModule).
      intros x _. unfold r_squared.
      apply (continuous_mult (fun y : R => y) (fun y : R => y));
        apply continuous_id. }
    transitivity (RInt (fun r => M0 * r_squared r) 0 R_max).
    - apply (@RInt_ext R_CompleteNormedModule).
      intros x Hx.
      rewrite Rmin_left in Hx by lra.
      rewrite Rmax_right in Hx by lra.
      change ((fun r => M_volumetric_integrand M profile r) x =
              (fun r => M0 * r_squared r) x).
      cbv beta.
      unfold M_volumetric_integrand, r_squared.
      rewrite (Hconst x ltac:(lra)). ring.
    - apply RInt_scal_R. exact Hex_r2. }
  rewrite Hnum. field. apply Rgt_not_eq, Hden_pos.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions RInt_r_squared.
Print Assumptions M_volumetric_pointwise_bound.
Print Assumptions M_volumetric_uniform.
