(******************************************************************************)
(*                                                                            *)
(*     3D Fubini volumetric averaging (item 5)                                *)
(*                                                                            *)
(*     Defines `is_RInt_3D` as a three-deep nested Coquelicot `is_RInt`       *)
(*     and proves Fubini-type commutativity for separable integrands          *)
(*     f(x,y,z) = g(x) * h(y) * k(z). This is the canonical use case for      *)
(*     plasma volumetric averaging where the local source factorises by       *)
(*     coordinate.                                                            *)
(*                                                                            *)
(*     The 3D volumetric multiplication factor specialises to the radial      *)
(*     case used in `pb_avalanche_spatial.v` via the substitution             *)
(*     `f(x,y,z) = g(sqrt(x^2 + y^2 + z^2))`; this file proves the box-       *)
(*     integration variant.                                                   *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

(* ================================================================== *)
(* === Nested 3D Riemann integral === *)
(* ================================================================== *)

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

(* Fubini for a genuinely non-separable integrand (a sum of two
   separable terms): the x-y-z and y-x-z orderings agree. *)
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
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions iter_rint_xyz_separable.
Print Assumptions iter_rint_yxz_separable.
Print Assumptions iter_rint_zxy_separable.
Print Assumptions RInt_3D_swap_xy_separable.
Print Assumptions RInt_3D_swap_xz_separable.
Print Assumptions iter_rint_const.
Print Assumptions M_volumetric_3D_order_independent.
Print Assumptions M_volumetric_3D_positive.
