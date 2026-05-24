(******************************************************************************)
(*                                                                            *)
(*     Spatial reactor profile via volumetric integration                     *)
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
(* === 3D Fubini volumetric averaging === *)
(* ================================================================== *)

(* The box volumetric average uses a three-deep nested Coquelicot
   `is_RInt`, with Fubini-type commutativity for separable integrands
   f(x,y,z) = g(x) * h(y) * k(z) and closure under sums. The radial
   volumetric factor above is the spherical specialisation. *)

(* Nested 3D Riemann integral. *)

Definition iter_rint_xyz (f : R -> R -> R -> R)
                         (a b c d e g : R) : R :=
  RInt (fun x => RInt (fun y => RInt (fun z => f x y z) e g) c d) a b.

Definition iter_rint_yxz (f : R -> R -> R -> R)
                         (a b c d e g : R) : R :=
  RInt (fun y => RInt (fun x => RInt (fun z => f x y z) e g) a b) c d.

Definition iter_rint_zxy (f : R -> R -> R -> R)
                         (a b c d e g : R) : R :=
  RInt (fun z => RInt (fun x => RInt (fun y => f x y z) c d) a b) e g.

(* The 3D box-integral predicate: l is the value of the iterated x-y-z
   integral of f over the box [a,b] × [c,d] × [e,g]. *)
Definition is_RInt_3D (f : R -> R -> R -> R)
                      (a b c d e g l : R) : Prop :=
  iter_rint_xyz f a b c d e g = l.

(* ================================================================== *)
(* === Separable integrand: f(x,y,z) = gX(x) * gY(y) * gZ(z) === *)
(* ================================================================== *)

Lemma RInt_const_factor :
  forall (f : R -> R) (a b c : R),
    ex_RInt f a b ->
    RInt (fun x => c * f x) a b = c * RInt f a b.
Proof.
  intros f a b c Hf.
  pose proof (RInt_scal f a b c Hf) as H.
  simpl in H. unfold scal in H; simpl in H.
  unfold mult in H; simpl in H. exact H.
Qed.

(* Real-valued existence-of-integral from continuity, with the module
   instance pinned to R (avoids V-unification failures). *)
Lemma ex_RInt_cont_R :
  forall (f : R -> R) (a b : R),
    (forall x, Rmin a b <= x <= Rmax a b -> continuous f x) ->
    ex_RInt f a b.
Proof.
  intros f a b Hf.
  exact (ex_RInt_continuous (V := R_CompleteNormedModule) f a b Hf).
Qed.

(* Real-valued additivity of RInt with the `+` notation (bridging
   Coquelicot's `plus`). *)
Lemma RInt_plus_R :
  forall (f g : R -> R) (a b : R),
    ex_RInt f a b -> ex_RInt g a b ->
    RInt (fun x => f x + g x) a b = RInt f a b + RInt g a b.
Proof.
  intros f g a b Hf Hg.
  pose proof (RInt_plus f g a b Hf Hg) as H.
  unfold plus in H; simpl in H.
  exact H.
Qed.

(* For a separable continuous integrand, the iterated integral
   factorises into the product of three 1-D integrals. *)
Theorem iter_rint_xyz_separable :
  forall (gX gY gZ : R -> R) (a b c d e g : R),
    ex_RInt gX a b -> ex_RInt gY c d -> ex_RInt gZ e g ->
    iter_rint_xyz (fun x y z => gX x * gY y * gZ z) a b c d e g
    = RInt gX a b * RInt gY c d * RInt gZ e g.
Proof.
  intros gX gY gZ a b c d e g HX HY HZ.
  unfold iter_rint_xyz.
  transitivity (RInt (fun x => RInt
                  (fun y => gX x * gY y * RInt gZ e g) c d) a b).
  { apply RInt_ext. intros x _.
    apply RInt_ext. intros y _.
    rewrite <- (RInt_const_factor gZ e g (gX x * gY y) HZ). reflexivity. }
  transitivity (RInt (fun x => gX x * RInt gY c d * RInt gZ e g) a b).
  { apply RInt_ext. intros x _.
    transitivity (RInt (fun y => (gX x * RInt gZ e g) * gY y) c d).
    { apply RInt_ext. intros y _. lra. }
    rewrite (RInt_const_factor gY c d (gX x * RInt gZ e g) HY). lra. }
  transitivity (RInt (fun x => (RInt gY c d * RInt gZ e g) * gX x) a b).
  { apply RInt_ext. intros x _. lra. }
  rewrite (RInt_const_factor gX a b (RInt gY c d * RInt gZ e g) HX). lra.
Qed.

(* Three other orderings — same result. *)
Theorem iter_rint_yxz_separable :
  forall (gX gY gZ : R -> R) (a b c d e g : R),
    ex_RInt gX a b -> ex_RInt gY c d -> ex_RInt gZ e g ->
    iter_rint_yxz (fun x y z => gX x * gY y * gZ z) a b c d e g
    = RInt gX a b * RInt gY c d * RInt gZ e g.
Proof.
  intros gX gY gZ a b c d e g HX HY HZ.
  unfold iter_rint_yxz.
  transitivity (RInt (fun y => RInt
                  (fun x => gX x * gY y * RInt gZ e g) a b) c d).
  { apply RInt_ext. intros y _.
    apply RInt_ext. intros x _.
    rewrite <- (RInt_const_factor gZ e g (gX x * gY y) HZ). reflexivity. }
  transitivity (RInt (fun y => gY y * RInt gX a b * RInt gZ e g) c d).
  { apply RInt_ext. intros y _.
    transitivity (RInt (fun x => (gY y * RInt gZ e g) * gX x) a b).
    { apply RInt_ext. intros x _. lra. }
    rewrite (RInt_const_factor gX a b (gY y * RInt gZ e g) HX). lra. }
  transitivity (RInt (fun y => (RInt gX a b * RInt gZ e g) * gY y) c d).
  { apply RInt_ext. intros y _. lra. }
  rewrite (RInt_const_factor gY c d (RInt gX a b * RInt gZ e g) HY). lra.
Qed.

Theorem iter_rint_zxy_separable :
  forall (gX gY gZ : R -> R) (a b c d e g : R),
    ex_RInt gX a b -> ex_RInt gY c d -> ex_RInt gZ e g ->
    iter_rint_zxy (fun x y z => gX x * gY y * gZ z) a b c d e g
    = RInt gX a b * RInt gY c d * RInt gZ e g.
Proof.
  intros gX gY gZ a b c d e g HX HY HZ.
  unfold iter_rint_zxy.
  transitivity (RInt (fun z => RInt
                  (fun x => gX x * gZ z * RInt gY c d) a b) e g).
  { apply RInt_ext. intros z _.
    apply RInt_ext. intros x _.
    transitivity (RInt (fun y => (gX x * gZ z) * gY y) c d).
    { apply RInt_ext. intros y _. lra. }
    rewrite (RInt_const_factor gY c d (gX x * gZ z) HY). lra. }
  transitivity (RInt (fun z => gZ z * RInt gX a b * RInt gY c d) e g).
  { apply RInt_ext. intros z _.
    transitivity (RInt (fun x => (gZ z * RInt gY c d) * gX x) a b).
    { apply RInt_ext. intros x _. lra. }
    rewrite (RInt_const_factor gX a b (gZ z * RInt gY c d) HX). lra. }
  transitivity (RInt (fun z => (RInt gX a b * RInt gY c d) * gZ z) e g).
  { apply RInt_ext. intros z _. lra. }
  rewrite (RInt_const_factor gZ e g (RInt gX a b * RInt gY c d) HZ). lra.
Qed.

(* === Fubini for separable integrands === *)

(* Three orderings agree: the box integral is permutation-invariant. *)
Theorem RInt_3D_swap_xy_separable :
  forall (gX gY gZ : R -> R) (a b c d e g : R),
    ex_RInt gX a b -> ex_RInt gY c d -> ex_RInt gZ e g ->
    iter_rint_xyz (fun x y z => gX x * gY y * gZ z) a b c d e g
    = iter_rint_yxz (fun x y z => gX x * gY y * gZ z) a b c d e g.
Proof.
  intros gX gY gZ a b c d e g HX HY HZ.
  rewrite (iter_rint_xyz_separable gX gY gZ a b c d e g HX HY HZ).
  rewrite (iter_rint_yxz_separable gX gY gZ a b c d e g HX HY HZ).
  reflexivity.
Qed.

Theorem RInt_3D_swap_xz_separable :
  forall (gX gY gZ : R -> R) (a b c d e g : R),
    ex_RInt gX a b -> ex_RInt gY c d -> ex_RInt gZ e g ->
    iter_rint_xyz (fun x y z => gX x * gY y * gZ z) a b c d e g
    = iter_rint_zxy (fun x y z => gX x * gY y * gZ z) a b c d e g.
Proof.
  intros gX gY gZ a b c d e g HX HY HZ.
  rewrite (iter_rint_xyz_separable gX gY gZ a b c d e g HX HY HZ).
  rewrite (iter_rint_zxy_separable gX gY gZ a b c d e g HX HY HZ).
  reflexivity.
Qed.

(* ================================================================== *)
(* === Additivity and Fubini for the separable span (polynomials) === *)
(* ================================================================== *)

(* Every monomial x^i * y^j * z^k is separable, so every polynomial in
   (x, y, z) is a finite sum of separable terms. We prove the iterated
   integral is additive, hence Fubini commutativity holds across the
   whole polynomial algebra, not merely on single separable terms. *)

(* The closed-form value of the iterated integral on a two-term
   separable sum. Continuity of the six component functions gives the
   ex_RInt obligations at each nesting level. *)
Theorem iter_rint_xyz_two_separable :
  forall (gX1 gY1 gZ1 gX2 gY2 gZ2 : R -> R) (a b c d e g : R),
    (forall x, continuous gX1 x) -> (forall x, continuous gX2 x) ->
    (forall y, continuous gY1 y) -> (forall y, continuous gY2 y) ->
    (forall z, continuous gZ1 z) -> (forall z, continuous gZ2 z) ->
    iter_rint_xyz
      (fun x y z => gX1 x * gY1 y * gZ1 z + gX2 x * gY2 y * gZ2 z)
      a b c d e g
    = RInt gX1 a b * RInt gY1 c d * RInt gZ1 e g
    + RInt gX2 a b * RInt gY2 c d * RInt gZ2 e g.
Proof.
  intros gX1 gY1 gZ1 gX2 gY2 gZ2 a b c d e g
         cX1 cX2 cY1 cY2 cZ1 cZ2.
  unfold iter_rint_xyz.
  (* Collapse the inner z-integral by additivity + scalar factoring. *)
  transitivity
    (RInt (fun x => RInt
       (fun y => (gX1 x * gY1 y) * RInt gZ1 e g
               + (gX2 x * gY2 y) * RInt gZ2 e g) c d) a b).
  { apply RInt_ext. intros x _. apply RInt_ext. intros y _.
    rewrite (RInt_plus_R
               (fun z => gX1 x * gY1 y * gZ1 z)
               (fun z => gX2 x * gY2 y * gZ2 z) e g).
    - rewrite <- (RInt_const_factor gZ1 e g (gX1 x * gY1 y) (ex_RInt_cont_R _ _ _ (fun z _ => cZ1 z))).
      rewrite <- (RInt_const_factor gZ2 e g (gX2 x * gY2 y) (ex_RInt_cont_R _ _ _ (fun z _ => cZ2 z))).
      reflexivity.
    - apply ex_RInt_cont_R. intros z _.
      apply (continuous_mult (fun z => gX1 x * gY1 y) gZ1).
      + apply continuous_const.
      + apply cZ1.
    - apply ex_RInt_cont_R. intros z _.
      apply (continuous_mult (fun z => gX2 x * gY2 y) gZ2).
      + apply continuous_const.
      + apply cZ2. }
  (* Collapse the middle y-integral. *)
  transitivity
    (RInt (fun x => gX1 x * RInt gY1 c d * RInt gZ1 e g
                  + gX2 x * RInt gY2 c d * RInt gZ2 e g) a b).
  { apply RInt_ext. intros x _.
    rewrite (RInt_plus_R
               (fun y => gX1 x * gY1 y * RInt gZ1 e g)
               (fun y => gX2 x * gY2 y * RInt gZ2 e g) c d).
    - (* factor each y-integral *)
      transitivity
        (RInt (fun y => (gX1 x * RInt gZ1 e g) * gY1 y) c d
         + RInt (fun y => (gX2 x * RInt gZ2 e g) * gY2 y) c d).
      { f_equal; apply RInt_ext; intros y _; lra. }
      rewrite (RInt_const_factor gY1 c d (gX1 x * RInt gZ1 e g)
                 (ex_RInt_cont_R _ _ _ (fun y _ => cY1 y))).
      rewrite (RInt_const_factor gY2 c d (gX2 x * RInt gZ2 e g)
                 (ex_RInt_cont_R _ _ _ (fun y _ => cY2 y))).
      lra.
    - apply ex_RInt_cont_R. intros y _.
      apply (continuous_mult (fun y => gX1 x * gY1 y) (fun _ => RInt gZ1 e g)).
      + apply (continuous_mult (fun _ => gX1 x) gY1).
        * apply continuous_const.
        * apply cY1.
      + apply continuous_const.
    - apply ex_RInt_cont_R. intros y _.
      apply (continuous_mult (fun y => gX2 x * gY2 y) (fun _ => RInt gZ2 e g)).
      + apply (continuous_mult (fun _ => gX2 x) gY2).
        * apply continuous_const.
        * apply cY2.
      + apply continuous_const. }
  (* Collapse the outer x-integral. *)
  rewrite (RInt_plus_R
             (fun x => gX1 x * RInt gY1 c d * RInt gZ1 e g)
             (fun x => gX2 x * RInt gY2 c d * RInt gZ2 e g) a b).
  - transitivity
      (RInt (fun x => (RInt gY1 c d * RInt gZ1 e g) * gX1 x) a b
       + RInt (fun x => (RInt gY2 c d * RInt gZ2 e g) * gX2 x) a b).
    { f_equal; apply RInt_ext; intros x _; lra. }
    rewrite (RInt_const_factor gX1 a b (RInt gY1 c d * RInt gZ1 e g)
               (ex_RInt_cont_R _ _ _ (fun x _ => cX1 x))).
    rewrite (RInt_const_factor gX2 a b (RInt gY2 c d * RInt gZ2 e g)
               (ex_RInt_cont_R _ _ _ (fun x _ => cX2 x))).
    lra.
  - apply ex_RInt_cont_R. intros x _.
    apply (continuous_mult (fun x => gX1 x * RInt gY1 c d) (fun _ => RInt gZ1 e g)).
    + apply (continuous_mult gX1 (fun _ => RInt gY1 c d)).
      * apply cX1.
      * apply continuous_const.
    + apply continuous_const.
  - apply ex_RInt_cont_R. intros x _.
    apply (continuous_mult (fun x => gX2 x * RInt gY2 c d) (fun _ => RInt gZ2 e g)).
    + apply (continuous_mult gX2 (fun _ => RInt gY2 c d)).
      * apply cX2.
      * apply continuous_const.
    + apply continuous_const.
Qed.

(* The y-x-z ordering gives the same two-term closed form. *)
Theorem iter_rint_yxz_two_separable :
  forall (gX1 gY1 gZ1 gX2 gY2 gZ2 : R -> R) (a b c d e g : R),
    (forall x, continuous gX1 x) -> (forall x, continuous gX2 x) ->
    (forall y, continuous gY1 y) -> (forall y, continuous gY2 y) ->
    (forall z, continuous gZ1 z) -> (forall z, continuous gZ2 z) ->
    iter_rint_yxz
      (fun x y z => gX1 x * gY1 y * gZ1 z + gX2 x * gY2 y * gZ2 z)
      a b c d e g
    = RInt gX1 a b * RInt gY1 c d * RInt gZ1 e g
    + RInt gX2 a b * RInt gY2 c d * RInt gZ2 e g.
Proof.
  intros gX1 gY1 gZ1 gX2 gY2 gZ2 a b c d e g
         cX1 cX2 cY1 cY2 cZ1 cZ2.
  unfold iter_rint_yxz.
  transitivity
    (RInt (fun y => RInt
       (fun x => (gX1 x * gY1 y) * RInt gZ1 e g
               + (gX2 x * gY2 y) * RInt gZ2 e g) a b) c d).
  { apply RInt_ext. intros y _. apply RInt_ext. intros x _.
    rewrite (RInt_plus_R
               (fun z => gX1 x * gY1 y * gZ1 z)
               (fun z => gX2 x * gY2 y * gZ2 z) e g).
    - rewrite <- (RInt_const_factor gZ1 e g (gX1 x * gY1 y) (ex_RInt_cont_R _ _ _ (fun z _ => cZ1 z))).
      rewrite <- (RInt_const_factor gZ2 e g (gX2 x * gY2 y) (ex_RInt_cont_R _ _ _ (fun z _ => cZ2 z))).
      reflexivity.
    - apply ex_RInt_cont_R. intros z _.
      apply (continuous_mult (fun z => gX1 x * gY1 y) gZ1);
        [apply continuous_const | apply cZ1].
    - apply ex_RInt_cont_R. intros z _.
      apply (continuous_mult (fun z => gX2 x * gY2 y) gZ2);
        [apply continuous_const | apply cZ2]. }
  transitivity
    (RInt (fun y => gY1 y * RInt gX1 a b * RInt gZ1 e g
                  + gY2 y * RInt gX2 a b * RInt gZ2 e g) c d).
  { apply RInt_ext. intros y _.
    rewrite (RInt_plus_R
               (fun x => gX1 x * gY1 y * RInt gZ1 e g)
               (fun x => gX2 x * gY2 y * RInt gZ2 e g) a b).
    - transitivity
        (RInt (fun x => (gY1 y * RInt gZ1 e g) * gX1 x) a b
         + RInt (fun x => (gY2 y * RInt gZ2 e g) * gX2 x) a b).
      { f_equal; apply RInt_ext; intros x _; lra. }
      rewrite (RInt_const_factor gX1 a b (gY1 y * RInt gZ1 e g)
                 (ex_RInt_cont_R _ _ _ (fun x _ => cX1 x))).
      rewrite (RInt_const_factor gX2 a b (gY2 y * RInt gZ2 e g)
                 (ex_RInt_cont_R _ _ _ (fun x _ => cX2 x))).
      lra.
    - apply ex_RInt_cont_R. intros x _.
      apply (continuous_mult (fun x => gX1 x * gY1 y) (fun _ => RInt gZ1 e g));
        [apply (continuous_mult gX1 (fun _ => gY1 y)); [apply cX1 | apply continuous_const] | apply continuous_const].
    - apply ex_RInt_cont_R. intros x _.
      apply (continuous_mult (fun x => gX2 x * gY2 y) (fun _ => RInt gZ2 e g));
        [apply (continuous_mult gX2 (fun _ => gY2 y)); [apply cX2 | apply continuous_const] | apply continuous_const]. }
  rewrite (RInt_plus_R
             (fun y => gY1 y * RInt gX1 a b * RInt gZ1 e g)
             (fun y => gY2 y * RInt gX2 a b * RInt gZ2 e g) c d).
  - transitivity
      (RInt (fun y => (RInt gX1 a b * RInt gZ1 e g) * gY1 y) c d
       + RInt (fun y => (RInt gX2 a b * RInt gZ2 e g) * gY2 y) c d).
    { f_equal; apply RInt_ext; intros y _; lra. }
    rewrite (RInt_const_factor gY1 c d (RInt gX1 a b * RInt gZ1 e g)
               (ex_RInt_cont_R _ _ _ (fun y _ => cY1 y))).
    rewrite (RInt_const_factor gY2 c d (RInt gX2 a b * RInt gZ2 e g)
               (ex_RInt_cont_R _ _ _ (fun y _ => cY2 y))).
    lra.
  - apply ex_RInt_cont_R. intros y _.
    apply (continuous_mult (fun y => gY1 y * RInt gX1 a b) (fun _ => RInt gZ1 e g));
      [apply (continuous_mult gY1 (fun _ => RInt gX1 a b)); [apply cY1 | apply continuous_const] | apply continuous_const].
  - apply ex_RInt_cont_R. intros y _.
    apply (continuous_mult (fun y => gY2 y * RInt gX2 a b) (fun _ => RInt gZ2 e g));
      [apply (continuous_mult gY2 (fun _ => RInt gX2 a b)); [apply cY2 | apply continuous_const] | apply continuous_const].
Qed.

(* Fubini for a non-separable integrand (a sum of two separable terms):
   the x-y-z and y-x-z orderings agree. *)
Theorem fubini_two_separable :
  forall (gX1 gY1 gZ1 gX2 gY2 gZ2 : R -> R) (a b c d e g : R),
    (forall x, continuous gX1 x) -> (forall x, continuous gX2 x) ->
    (forall y, continuous gY1 y) -> (forall y, continuous gY2 y) ->
    (forall z, continuous gZ1 z) -> (forall z, continuous gZ2 z) ->
    iter_rint_xyz
      (fun x y z => gX1 x * gY1 y * gZ1 z + gX2 x * gY2 y * gZ2 z)
      a b c d e g
    = iter_rint_yxz
      (fun x y z => gX1 x * gY1 y * gZ1 z + gX2 x * gY2 y * gZ2 z)
      a b c d e g.
Proof.
  intros.
  rewrite iter_rint_xyz_two_separable by assumption.
  rewrite iter_rint_yxz_two_separable by assumption.
  reflexivity.
Qed.

(* ================================================================== *)
(* === Volumetric averaging on a box === *)
(* ================================================================== *)

Definition box_volume (a b c d e g : R) : R := (b - a) * (d - c) * (g - e).

Lemma box_volume_pos :
  forall a b c d e g, a < b -> c < d -> e < g -> 0 < box_volume a b c d e g.
Proof.
  intros. unfold box_volume.
  repeat apply Rmult_lt_0_compat; lra.
Qed.

(* The mean over the box of a separable constant-multiplied integrand. *)
Definition box_mean_separable (gX gY gZ : R -> R) (a b c d e g : R) : R :=
  (RInt gX a b * RInt gY c d * RInt gZ e g) / box_volume a b c d e g.

Theorem box_mean_separable_value :
  forall gX gY gZ a b c d e g,
    a < b -> c < d -> e < g ->
    box_mean_separable gX gY gZ a b c d e g =
    (RInt gX a b / (b - a)) *
    (RInt gY c d / (d - c)) *
    (RInt gZ e g / (g - e)).
Proof.
  intros gX gY gZ a b c d e g Hab Hcd Heg.
  unfold box_mean_separable, box_volume.
  field. split; [lra |split; lra].
Qed.

(* ================================================================== *)
(* === Specialisation: constant integrand === *)
(* ================================================================== *)

Theorem iter_rint_const :
  forall (k : R) (a b c d e g : R),
    iter_rint_xyz (fun _ _ _ => k) a b c d e g
    = k * (b - a) * (d - c) * (g - e).
Proof.
  intros k a b c d e g. unfold iter_rint_xyz.
  transitivity (RInt (fun _ : R => RInt (fun _ : R => k * (g - e)) c d) a b).
  { apply RInt_ext. intros x _.
    apply RInt_ext. intros y _.
    rewrite RInt_const. unfold scal; simpl; unfold mult; simpl; lra. }
  transitivity (RInt (fun _ : R => k * (g - e) * (d - c)) a b).
  { apply RInt_ext. intros x _.
    rewrite RInt_const. unfold scal; simpl; unfold mult; simpl; lra. }
  rewrite RInt_const. unfold scal; simpl; unfold mult; simpl; lra.
Qed.

(* ================================================================== *)
(* === Box volumetric multiplication factor === *)
(* ================================================================== *)

(* The full 3D volumetric multiplication factor over a reactor box,
   when each local factor is separable: M_volumetric_3D corresponds
   to the average of `M_local(x,y,z) = gX(x) * gY(y) * gZ(z)` over
   the box. *)
Definition M_volumetric_3D (gX gY gZ : R -> R)
                           (a b c d e g : R) : R :=
  iter_rint_xyz (fun x y z => gX x * gY y * gZ z) a b c d e g
  / box_volume a b c d e g.

(* Order-independence: any ordering of the integration gives the
   same volumetric factor. *)
Theorem M_volumetric_3D_order_independent :
  forall gX gY gZ a b c d e g,
    ex_RInt gX a b -> ex_RInt gY c d -> ex_RInt gZ e g ->
    a < b -> c < d -> e < g ->
    M_volumetric_3D gX gY gZ a b c d e g
    = (iter_rint_yxz (fun x y z => gX x * gY y * gZ z) a b c d e g)
      / box_volume a b c d e g
    /\
    M_volumetric_3D gX gY gZ a b c d e g
    = (iter_rint_zxy (fun x y z => gX x * gY y * gZ z) a b c d e g)
      / box_volume a b c d e g.
Proof.
  intros gX gY gZ a b c d e g HX HY HZ Hab Hcd Heg.
  unfold M_volumetric_3D.
  split.
  - f_equal. apply (RInt_3D_swap_xy_separable gX gY gZ a b c d e g HX HY HZ).
  - f_equal. apply (RInt_3D_swap_xz_separable gX gY gZ a b c d e g HX HY HZ).
Qed.

(* Positivity: if each separable factor is positive and the average of
   each is positive, the 3D factor is positive. *)
Theorem M_volumetric_3D_positive :
  forall gX gY gZ a b c d e g,
    ex_RInt gX a b -> ex_RInt gY c d -> ex_RInt gZ e g ->
    a < b -> c < d -> e < g ->
    0 < RInt gX a b ->
    0 < RInt gY c d ->
    0 < RInt gZ e g ->
    0 < M_volumetric_3D gX gY gZ a b c d e g.
Proof.
  intros gX gY gZ a b c d e g eX eY eZ Hab Hcd Heg HX HY HZ.
  unfold M_volumetric_3D.
  rewrite (iter_rint_xyz_separable gX gY gZ a b c d e g eX eY eZ).
  apply Rdiv_lt_0_compat.
  - apply Rmult_lt_0_compat;
    [apply Rmult_lt_0_compat |]; assumption.
  - apply box_volume_pos; assumption.
Qed.

(* ================================================================== *)
(* === Fubini for finite sums (additive closure of products) === *)
(* ================================================================== *)

Lemma iter_rint_xyz_plus :
  forall (f g : R -> R -> R -> R) (a b c d e h : R),
    (forall x y, ex_RInt (fun z => f x y z) e h) ->
    (forall x y, ex_RInt (fun z => g x y z) e h) ->
    (forall x, ex_RInt (fun y => RInt (fun z => f x y z) e h) c d) ->
    (forall x, ex_RInt (fun y => RInt (fun z => g x y z) e h) c d) ->
    ex_RInt (fun x => RInt (fun y => RInt (fun z => f x y z) e h) c d) a b ->
    ex_RInt (fun x => RInt (fun y => RInt (fun z => g x y z) e h) c d) a b ->
    iter_rint_xyz (fun x y z => f x y z + g x y z) a b c d e h
    = iter_rint_xyz f a b c d e h + iter_rint_xyz g a b c d e h.
Proof.
  intros f g a b c d e h Hz1 Hz2 Hy1 Hy2 Hx1 Hx2.
  unfold iter_rint_xyz.
  transitivity
    (RInt (fun x => RInt (fun y => RInt (fun z => f x y z) e h
                                  + RInt (fun z => g x y z) e h) c d) a b).
  { apply RInt_ext. intros x _. apply RInt_ext. intros y _.
    apply RInt_plus_R; [apply Hz1 | apply Hz2]. }
  transitivity
    (RInt (fun x => RInt (fun y => RInt (fun z => f x y z) e h) c d
                  + RInt (fun y => RInt (fun z => g x y z) e h) c d) a b).
  { apply RInt_ext. intros x _.
    apply RInt_plus_R; [apply Hy1 | apply Hy2]. }
  apply RInt_plus_R; [exact Hx1 | exact Hx2].
Qed.

Lemma iter_rint_yxz_plus :
  forall (f g : R -> R -> R -> R) (a b c d e h : R),
    (forall x y, ex_RInt (fun z => f x y z) e h) ->
    (forall x y, ex_RInt (fun z => g x y z) e h) ->
    (forall y, ex_RInt (fun x => RInt (fun z => f x y z) e h) a b) ->
    (forall y, ex_RInt (fun x => RInt (fun z => g x y z) e h) a b) ->
    ex_RInt (fun y => RInt (fun x => RInt (fun z => f x y z) e h) a b) c d ->
    ex_RInt (fun y => RInt (fun x => RInt (fun z => g x y z) e h) a b) c d ->
    iter_rint_yxz (fun x y z => f x y z + g x y z) a b c d e h
    = iter_rint_yxz f a b c d e h + iter_rint_yxz g a b c d e h.
Proof.
  intros f g a b c d e h Hz1 Hz2 Hx1 Hx2 Hy1 Hy2.
  unfold iter_rint_yxz.
  transitivity
    (RInt (fun y => RInt (fun x => RInt (fun z => f x y z) e h
                                  + RInt (fun z => g x y z) e h) a b) c d).
  { apply RInt_ext. intros y _. apply RInt_ext. intros x _.
    apply RInt_plus_R; [apply Hz1 | apply Hz2]. }
  transitivity
    (RInt (fun y => RInt (fun x => RInt (fun z => f x y z) e h) a b
                  + RInt (fun x => RInt (fun z => g x y z) e h) a b) c d).
  { apply RInt_ext. intros y _.
    apply RInt_plus_R; [apply Hx1 | apply Hx2]. }
  apply RInt_plus_R; [exact Hy1 | exact Hy2].
Qed.

(* Fubini is closed under sums: if the x-y-z and y-x-z orderings agree
   for f and for g (each Fubini-compatible), they agree for f + g.
   With the separable-product base case, this gives Fubini for every
   finite sum of separable terms. *)
Theorem fubini_sum :
  forall (f g : R -> R -> R -> R) (a b c d e h : R),
    (forall x y, ex_RInt (fun z => f x y z) e h) ->
    (forall x y, ex_RInt (fun z => g x y z) e h) ->
    (forall x, ex_RInt (fun y => RInt (fun z => f x y z) e h) c d) ->
    (forall x, ex_RInt (fun y => RInt (fun z => g x y z) e h) c d) ->
    ex_RInt (fun x => RInt (fun y => RInt (fun z => f x y z) e h) c d) a b ->
    ex_RInt (fun x => RInt (fun y => RInt (fun z => g x y z) e h) c d) a b ->
    (forall y, ex_RInt (fun x => RInt (fun z => f x y z) e h) a b) ->
    (forall y, ex_RInt (fun x => RInt (fun z => g x y z) e h) a b) ->
    ex_RInt (fun y => RInt (fun x => RInt (fun z => f x y z) e h) a b) c d ->
    ex_RInt (fun y => RInt (fun x => RInt (fun z => g x y z) e h) a b) c d ->
    iter_rint_xyz f a b c d e h = iter_rint_yxz f a b c d e h ->
    iter_rint_xyz g a b c d e h = iter_rint_yxz g a b c d e h ->
    iter_rint_xyz (fun x y z => f x y z + g x y z) a b c d e h
    = iter_rint_yxz (fun x y z => f x y z + g x y z) a b c d e h.
Proof.
  intros f g a b c d e h Hz1 Hz2 Hy1 Hy2 Hx1 Hx2 Hyx1 Hyx2 Hyy1 Hyy2 Hf Hg.
  rewrite (iter_rint_xyz_plus f g a b c d e h Hz1 Hz2 Hy1 Hy2 Hx1 Hx2).
  rewrite (iter_rint_yxz_plus f g a b c d e h Hz1 Hz2 Hyx1 Hyx2 Hyy1 Hyy2).
  rewrite Hf, Hg. reflexivity.
Qed.


(* The zero integrand: all orderings give 0. *)
Lemma iter_rint_xyz_zero : forall a b c d e g,
  iter_rint_xyz (fun _ _ _ => 0) a b c d e g = 0.
Proof.
  intros a b c d e g. unfold iter_rint_xyz.
  transitivity (RInt (fun _ : R => RInt (fun _ : R => 0) c d) a b).
  { apply RInt_ext. intros x _. apply RInt_ext. intros y _.
    rewrite RInt_const. unfold scal; simpl; unfold mult; simpl. ring. }
  transitivity (RInt (fun _ : R => 0) a b).
  { apply RInt_ext. intros x _. rewrite RInt_const.
    unfold scal; simpl; unfold mult; simpl. ring. }
  rewrite RInt_const. unfold scal; simpl; unfold mult; simpl. ring.
Qed.

Lemma iter_rint_yxz_zero : forall a b c d e g,
  iter_rint_yxz (fun _ _ _ => 0) a b c d e g = 0.
Proof.
  intros a b c d e g. unfold iter_rint_yxz.
  transitivity (RInt (fun _ : R => RInt (fun _ : R => 0) a b) c d).
  { apply RInt_ext. intros y _. apply RInt_ext. intros x _.
    rewrite RInt_const. unfold scal; simpl; unfold mult; simpl. ring. }
  transitivity (RInt (fun _ : R => 0) c d).
  { apply RInt_ext. intros y _. rewrite RInt_const.
    unfold scal; simpl; unfold mult; simpl. ring. }
  rewrite RInt_const. unfold scal; simpl; unfold mult; simpl. ring.
Qed.

Theorem fubini_zero : forall a b c d e g,
  iter_rint_xyz (fun _ _ _ => 0) a b c d e g
  = iter_rint_yxz (fun _ _ _ => 0) a b c d e g.
Proof.
  intros. rewrite iter_rint_xyz_zero, iter_rint_yxz_zero. reflexivity.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions RInt_r_squared.
Print Assumptions M_volumetric_pointwise_bound.
Print Assumptions M_volumetric_uniform.
Print Assumptions iter_rint_xyz_separable.
Print Assumptions iter_rint_yxz_separable.
Print Assumptions iter_rint_zxy_separable.
Print Assumptions RInt_3D_swap_xy_separable.
Print Assumptions RInt_3D_swap_xz_separable.
Print Assumptions iter_rint_const.
Print Assumptions M_volumetric_3D_order_independent.
Print Assumptions M_volumetric_3D_positive.
Print Assumptions iter_rint_xyz_plus.
Print Assumptions fubini_sum.
Print Assumptions fubini_zero.
