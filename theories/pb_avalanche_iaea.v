(******************************************************************************)
(*                                                                            *)
(*     IAEA-evaluated p-11B cross sections: piecewise-linear interpolation,   *)
(*     trapezoidal integration, and bounded interpolation error (item 3)      *)
(*                                                                            *)
(*     A discrete table of (E_i, sigma_i) points is interpolated by the       *)
(*     piecewise-linear function interp_linear, integrated by the             *)
(*     trapezoidal sum trap_integral, and the error |RInt sigma_true -        *)
(*     RInt interp_linear| <= eps * (b - a) is carried as an explicit bound   *)
(*     derived from abs_RInt_le and RInt_minus.                                *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From Coquelicot Require Import Coquelicot.

From PBAvalanche Require Import pb_avalanche pb_avalanche_integral.

Open Scope R_scope.

(* ================================================================== *)
(* === Linear interpolation segment === *)
(* ================================================================== *)

(* The linear interpolant between (e1, v1) and (e2, v2):
   f(E) = v1 + (v2 - v1) * (E - e1) / (e2 - e1). *)
Definition interp_segment (e1 v1 e2 v2 E : R) : R :=
  v1 + (v2 - v1) * (E - e1) / (e2 - e1).

Lemma interp_segment_left :
  forall e1 v1 e2 v2,
    e1 < e2 -> interp_segment e1 v1 e2 v2 e1 = v1.
Proof.
  intros e1 v1 e2 v2 H. unfold interp_segment. field. lra.
Qed.

Lemma interp_segment_right :
  forall e1 v1 e2 v2,
    e1 < e2 -> interp_segment e1 v1 e2 v2 e2 = v2.
Proof.
  intros e1 v1 e2 v2 H. unfold interp_segment.
  field. lra.
Qed.

Lemma interp_segment_rewrite :
  forall e1 v1 e2 v2,
    e1 < e2 ->
    forall x : R,
      x * ((v2 - v1) / (e2 - e1)) - e1 * ((v2 - v1) / (e2 - e1)) =
        (v2 - v1) * (x - e1) / (e2 - e1).
Proof. intros e1 v1 e2 v2 H x. field. lra. Qed.

Lemma interp_segment_continuous :
  forall e1 v1 e2 v2 E,
    e1 < e2 -> continuous (interp_segment e1 v1 e2 v2) E.
Proof.
  intros e1 v1 e2 v2 E H.
  unfold interp_segment.
  apply (continuous_plus (fun _ => v1)
                         (fun x => (v2 - v1) * (x - e1) / (e2 - e1))).
  - apply continuous_const.
  - apply continuous_ext with
      (f := fun x : R => x * ((v2 - v1) / (e2 - e1)) -
                         e1 * ((v2 - v1) / (e2 - e1))).
    + intro x. apply interp_segment_rewrite. exact H.
    + apply (continuous_minus
               (fun x : R => x * ((v2 - v1) / (e2 - e1)))
               (fun _ : R => e1 * ((v2 - v1) / (e2 - e1)))).
      * apply (continuous_mult (fun x : R => x)
                               (fun _ : R => (v2 - v1) / (e2 - e1))).
        -- apply continuous_id.
        -- apply continuous_const.
      * apply continuous_const.
Qed.

Lemma ex_RInt_interp_segment :
  forall e1 v1 e2 v2 a b,
    e1 < e2 ->
    ex_RInt (interp_segment e1 v1 e2 v2) a b.
Proof.
  intros e1 v1 e2 v2 a b H.
  apply (@ex_RInt_continuous R_CompleteNormedModule).
  intros x _. apply interp_segment_continuous; exact H.
Qed.

(* === Closed-form integral of the linear segment ===

   RInt (interp_segment e1 v1 e2 v2) e1 e2 = (v1 + v2) / 2 * (e2 - e1). *)
Theorem RInt_interp_segment :
  forall e1 v1 e2 v2,
    e1 < e2 ->
    RInt (interp_segment e1 v1 e2 v2) e1 e2 = (v1 + v2) / 2 * (e2 - e1).
Proof.
  intros e1 v1 e2 v2 H.
  set (F := fun x : R => v1 * (x - e1) +
                          (v2 - v1) * (x - e1) * (x - e1) /
                          (2 * (e2 - e1))).
  (* Building the derivative chain by hand.
     d/dx (x - e1) = 1 (sum of id and constant)
     d/dx (v1 * (x - e1)) = v1 (constant rescaling of derivative 1)
     d/dx (x - e1)^2 = 2 * (x - e1) * 1 (product rule on (x-e1)*(x-e1))
     d/dx [(v2-v1)/(2(e2-e1)) * (x-e1)^2]
        = (v2-v1)/(2(e2-e1)) * 2 * (x-e1)
        = (v2-v1) * (x-e1) / (e2-e1)
     Sum: v1 + (v2-v1) * (x-e1) / (e2-e1) = interp_segment e1 v1 e2 v2 x. *)
  assert (Hgap_ne : e2 - e1 <> 0) by lra.
  assert (Hd_shift : forall x : R,
            is_derive (fun y : R => y - e1) x 1).
  { intro x.
    pose proof (@Derive.is_derive_plus R_AbsRing R_NormedModule
                  (fun y : R => y) (fun _ : R => - e1) x 1 0
                  (@is_derive_id R_AbsRing x)
                  (is_derive_const (- e1) x)) as Hp.
    cbv beta in Hp.
    apply (is_derive_ext (fun y : R => plus y (- e1))).
    - intro y. unfold plus; simpl. unfold Rminus. reflexivity.
    - assert (Heq : plus (1 : R) 0 = 1) by (unfold plus; simpl; ring).
      rewrite <- Heq. exact Hp. }
  assert (Hd_lin : forall x : R,
            is_derive (fun y : R => v1 * (y - e1)) x v1).
  { intro x.
    pose proof (@Derive.is_derive_mult (fun _ : R => v1)
                  (fun y : R => y - e1) x 0 1
                  (is_derive_const v1 x) (Hd_shift x)) as Hp.
    cbv beta in Hp.
    assert (Heq : 0 * (x - e1) + v1 * 1 = v1) by ring.
    rewrite Heq in Hp. exact Hp. }
  assert (Hd_sq : forall x : R,
            is_derive (fun y : R => (y - e1) * (y - e1)) x (2 * (x - e1))).
  { intro x.
    pose proof (@Derive.is_derive_mult (fun y : R => y - e1)
                  (fun y : R => y - e1) x 1 1
                  (Hd_shift x) (Hd_shift x)) as Hp.
    cbv beta in Hp.
    assert (Heq : 1 * (x - e1) + (x - e1) * 1 = 2 * (x - e1)) by ring.
    rewrite Heq in Hp. exact Hp. }
  assert (Hquad_rewrite : forall y : R,
            ((v2 - v1) / (2 * (e2 - e1))) * ((y - e1) * (y - e1)) =
            (v2 - v1) * (y - e1) * (y - e1) / (2 * (e2 - e1)))
    by (intro y; field; exact Hgap_ne).
  assert (Hd_quad : forall x : R,
            is_derive (fun y : R => (v2 - v1) * (y - e1) * (y - e1) /
                                    (2 * (e2 - e1))) x
                      ((v2 - v1) * (x - e1) / (e2 - e1))).
  { intro x.
    apply (is_derive_ext
             (fun y : R => ((v2 - v1) / (2 * (e2 - e1))) *
                           ((y - e1) * (y - e1)))).
    - exact Hquad_rewrite.
    - pose proof (@Derive.is_derive_mult
                    (fun _ : R => (v2 - v1) / (2 * (e2 - e1)))
                    (fun y : R => (y - e1) * (y - e1))
                    x 0 (2 * (x - e1))
                    (is_derive_const _ x) (Hd_sq x)) as Hp.
      cbv beta in Hp.
      assert (Heq : 0 * ((x - e1) * (x - e1)) +
                    (v2 - v1) / (2 * (e2 - e1)) * (2 * (x - e1)) =
                    (v2 - v1) * (x - e1) / (e2 - e1))
        by (field; exact Hgap_ne).
      rewrite Heq in Hp. exact Hp. }
  assert (HF_deriv : forall x : R,
            is_derive F x (interp_segment e1 v1 e2 v2 x)).
  { intro x.
    pose proof (@Derive.is_derive_plus R_AbsRing R_NormedModule
                  (fun y : R => v1 * (y - e1))
                  (fun y : R => (v2 - v1) * (y - e1) * (y - e1) /
                                (2 * (e2 - e1)))
                  x v1 ((v2 - v1) * (x - e1) / (e2 - e1))
                  (Hd_lin x) (Hd_quad x)) as Hp.
    cbv beta in Hp.
    unfold plus in Hp; simpl in Hp.
    unfold F. unfold interp_segment. exact Hp. }
  assert (Hir : is_RInt (interp_segment e1 v1 e2 v2) e1 e2
                        (minus (F e2) (F e1))).
  { apply (@is_RInt_derive R_CompleteNormedModule F
             (interp_segment e1 v1 e2 v2) e1 e2).
    - intros x _. apply HF_deriv.
    - intros x _. apply interp_segment_continuous; exact H. }
  rewrite (is_RInt_unique _ _ _ _ Hir).
  unfold minus, plus, opp; simpl. unfold F.
  field. lra.
Qed.

(* ================================================================== *)
(* === IAEA-evaluated table === *)
(* ================================================================== *)

Definition iaea_point : Type := (R * R)%type.
Definition iaea_table : Type := list iaea_point.

(* Strictly sorted by energy. *)
Fixpoint sorted_table (T : iaea_table) : Prop :=
  match T with
  | [] => True
  | _ :: [] => True
  | (e1, _) :: ((e2, _) :: _) as rest =>
    e1 < e2 /\ sorted_table rest
  end.

Definition head_E (T : iaea_table) : R :=
  match T with
  | [] => 0
  | (e, _) :: _ => e
  end.

Fixpoint last_E (T : iaea_table) : R :=
  match T with
  | [] => 0
  | (e, _) :: [] => e
  | _ :: (rest as r) => last_E r
  end.

Fixpoint last_V (T : iaea_table) : R :=
  match T with
  | [] => 0
  | (_, v) :: [] => v
  | _ :: (rest as r) => last_V r
  end.

(* === Piecewise-linear interpolant === *)
Fixpoint interp_linear (T : iaea_table) (E : R) : R :=
  match T with
  | [] => 0
  | (_, v1) :: [] => v1
  | (e1, v1) :: ((e2, v2) :: _) as rest =>
    if Rle_lt_dec E e2 then
      interp_segment e1 v1 e2 v2 E
    else
      interp_linear rest E
  end.

(* === Zero-extended piecewise-linear interpolant ===

   Returns 0 outside [head_E T, last_E T]; coincides with interp_linear
   on the interval. Physically correct extrapolation for cross sections
   that are 0 outside the resonance window. *)
Definition interp_linear_ext (T : iaea_table) (E : R) : R :=
  match T with
  | [] => 0
  | _ =>
    if Rlt_dec E (head_E T) then 0
    else if Rlt_dec (last_E T) E then 0
    else interp_linear T E
  end.

Lemma interp_linear_ext_below :
  forall T E, E < head_E T -> interp_linear_ext T E = 0.
Proof.
  intros T E HE.
  destruct T as [| [e1 v1] rest]; [reflexivity |].
  unfold interp_linear_ext.
  destruct (Rlt_dec _ _) as [Hlt | Hge]; [reflexivity | exfalso; lra].
Qed.

Lemma interp_linear_ext_above :
  forall T E, last_E T < E -> interp_linear_ext T E = 0.
Proof.
  intros T E HE.
  destruct T as [| [e1 v1] rest]; [reflexivity |].
  unfold interp_linear_ext.
  destruct (Rlt_dec _ _) as [Hlt | Hge]; [reflexivity |].
  destruct (Rlt_dec _ _) as [Hlt' | Hge']; [reflexivity | exfalso; lra].
Qed.

Lemma interp_linear_ext_inside :
  forall T E,
    head_E T <= E <= last_E T ->
    interp_linear_ext T E = interp_linear T E.
Proof.
  intros T E [HE1 HE2].
  destruct T as [| [e1 v1] rest].
  - simpl in HE1. reflexivity.
  - unfold interp_linear_ext.
    destruct (Rlt_dec _ _) as [Hlt | Hge]; [exfalso; lra |].
    destruct (Rlt_dec _ _) as [Hlt' | Hge']; [exfalso; lra | reflexivity].
Qed.

(* === Trapezoidal sum === *)
Fixpoint trap_integral (T : iaea_table) : R :=
  match T with
  | [] => 0
  | _ :: [] => 0
  | (e1, v1) :: ((e2, v2) :: _) as rest =>
    (v1 + v2) / 2 * (e2 - e1) + trap_integral rest
  end.

(* ================================================================== *)
(* === Continuity and integrability of the piecewise interpolant === *)
(* ================================================================== *)

(* Within the first segment, interp_linear coincides with interp_segment. *)
Lemma interp_linear_first_segment :
  forall e1 v1 e2 v2 rest E,
    e1 <= E <= e2 ->
    interp_linear ((e1, v1) :: (e2, v2) :: rest) E =
      interp_segment e1 v1 e2 v2 E.
Proof.
  intros e1 v1 e2 v2 rest E [HL HR].
  simpl. destruct (Rle_lt_dec E e2) as [_ | Hgt].
  - reflexivity.
  - exfalso. lra.
Qed.

(* Past the first segment, interp_linear coincides with interp_linear on
   the tail. At E = e2, both branches happen to evaluate to v2, so the
   equation also holds at the boundary. *)
Lemma interp_linear_tail :
  forall e1 v1 e2 v2 rest E,
    e2 <= E ->
    sorted_table ((e1, v1) :: (e2, v2) :: rest) ->
    interp_linear ((e1, v1) :: (e2, v2) :: rest) E =
      interp_linear ((e2, v2) :: rest) E.
Proof.
  intros e1 v1 e2 v2 rest E HE Hsort.
  simpl in Hsort. destruct Hsort as [Hgap Hsort_tail].
  simpl. destruct (Rle_lt_dec E e2) as [Hle | Hgt].
  - (* E <= e2 and e2 <= E, so E = e2. *)
    assert (HE_eq : E = e2) by lra. subst E.
    destruct rest as [| [e3 v3] rest'].
    + (* singleton tail: interp_linear of singleton at e2 = v2 *)
      simpl. apply interp_segment_right; exact Hgap.
    + (* nonempty tail *)
      simpl. destruct (Rle_lt_dec e2 e3) as [_ | Hgt3].
      * rewrite (interp_segment_right e1 v1 e2 v2 Hgap).
        simpl in Hsort_tail. destruct Hsort_tail as [Hgap2 _].
        symmetry. apply interp_segment_left; exact Hgap2.
      * exfalso. simpl in Hsort_tail. destruct Hsort_tail as [Hgap2 _]. lra.
  - reflexivity.
Qed.

(* Integrability of interp_linear on a closed interval that may straddle
   any number of breakpoints. We prove ex_RInt by induction on the table. *)

(* For a sorted table, every entry energy lies between head_E and last_E. *)
Lemma head_E_le_last_E :
  forall T, sorted_table T -> head_E T <= last_E T.
Proof.
  induction T as [| [e1 v1] rest IH].
  - simpl. lra.
  - intros Hsort.
    destruct rest as [| [e2 v2] rest'].
    + simpl. lra.
    + (* rest = (e2, v2) :: rest' *)
      simpl in Hsort. destruct Hsort as [Hgap Hsort_tail].
      assert (IHapp : head_E ((e2, v2) :: rest') <= last_E ((e2, v2) :: rest'))
        by (apply IH; exact Hsort_tail).
      simpl in IHapp. simpl head_E. simpl last_E.
      destruct rest' as [| [e3 v3] rest''].
      * simpl in IHapp. simpl. lra.
      * lra.
Qed.

(* === Global continuity of interp_linear on [head_E T, last_E T] === *)

(* Helper: a function defined as the piecewise join of two continuous
   functions f (on the left of b) and g (on the right of b) that agree
   at b (f b = g b) is continuous at b. Proved directly via the
   epsilon-delta characterization. *)
Lemma continuous_piecewise_at :
  forall (f g : R -> R) (b : R),
    continuous f b ->
    continuous g b ->
    f b = g b ->
    continuous (fun x : R => if Rle_lt_dec x b then f x else g x) b.
Proof.
  intros f g b Hf Hg Heq.
  intros P HP.
  simpl in HP.
  destruct (Rle_lt_dec b b) as [_ | Hcontra]; [| exfalso; lra].
  destruct (Hf P HP) as [df Hdf].
  assert (HP' : locally (g b) P).
  { rewrite <- Heq. exact HP. }
  destruct (Hg P HP') as [dg Hdg].
  exists (mkposreal (Rmin df dg) (Rmin_stable_in_posreal df dg)).
  intros y Hy. simpl in Hy.
  destruct (Rle_lt_dec y b) as [_ | _].
  - apply Hdf.
    eapply ball_le; [| exact Hy].
    apply Rmin_l.
  - apply Hdg.
    eapply ball_le; [| exact Hy].
    apply Rmin_r.
Qed.

Lemma interp_linear_continuous_on :
  forall T E,
    sorted_table T ->
    head_E T <= E <= last_E T ->
    continuous (interp_linear T) E.
Proof.
  induction T as [| [e1 v1] rest IH].
  - intros E _ [HE1 HE2]. simpl in HE1, HE2.
    apply continuous_ext with (f := fun _ : R => 0).
    + intro x. simpl. reflexivity.
    + apply continuous_const.
  - intros E Hsort [HE1 HE2].
    destruct rest as [| [e2 v2] rest'].
    + (* singleton table: head_E = last_E = e1, so E = e1 *)
      simpl in HE1, HE2.
      assert (HEeq : E = e1) by lra. subst E.
      apply continuous_ext with (f := fun _ : R => v1).
      * intro x. simpl. reflexivity.
      * apply continuous_const.
    + (* at least two points *)
      simpl in Hsort. destruct Hsort as [Hgap Hsort_tail].
      assert (Hsort_full : sorted_table ((e2, v2) :: rest')).
      { destruct rest' as [| [e3 v3] rest''].
        - simpl. trivial.
        - simpl. exact Hsort_tail. }
      assert (Hsort_outer : sorted_table ((e1, v1) :: (e2, v2) :: rest'))
        by (simpl; split; [exact Hgap | exact Hsort_full]).
      assert (Hle_tail : e2 <= last_E ((e2, v2) :: rest'))
        by (apply (head_E_le_last_E ((e2, v2) :: rest')); exact Hsort_full).
      assert (HE2' : E <= last_E ((e2, v2) :: rest')).
      { destruct rest' as [| [e3 v3] rest''].
        - simpl. simpl in HE2. exact HE2.
        - simpl. simpl in HE2. exact HE2. }
      (* Trichotomy: E < e2, E = e2, or E > e2. *)
      destruct (Rlt_le_dec E e2) as [HElt | HEge].
      * (* E < e2: in a neighborhood of E, interp_linear matches segment *)
        apply (continuous_ext_loc (interp_linear ((e1, v1) :: (e2, v2) :: rest'))
                                  (interp_segment e1 v1 e2 v2) E).
        -- assert (HposR : 0 < (e2 - E) / 2) by lra.
           exists (mkposreal _ HposR).
           intros y Hy. simpl in Hy.
           unfold ball in Hy; simpl in Hy. unfold AbsRing_ball in Hy.
           unfold abs in Hy; simpl in Hy.
           unfold minus, plus, opp in Hy; simpl in Hy.
           apply Rabs_def2 in Hy. destruct Hy as [Hy_lt _].
           assert (Hy_le : y <= e2).
           { assert (Hposhalf : 0 < (e2 - E) / 2) by lra. nra. }
           simpl. destruct (Rle_lt_dec y e2) as [_ | Hcontra];
             [reflexivity | exfalso; lra].
        -- apply interp_segment_continuous; exact Hgap.
      * destruct (Rle_lt_dec E e2) as [HEle | HEgt].
        ** (* E = e2: use piecewise join *)
           assert (HEeq : E = e2) by lra. subst E.
           apply continuous_ext with
             (f := fun y : R =>
                     if Rle_lt_dec y e2
                     then interp_segment e1 v1 e2 v2 y
                     else interp_linear ((e2, v2) :: rest') y).
           --- intro y. simpl.
               destruct (Rle_lt_dec y e2) as [_ | _]; reflexivity.
           --- apply continuous_piecewise_at.
               +++ apply interp_segment_continuous; exact Hgap.
               +++ apply IH; [exact Hsort_full |].
                   simpl. split; [lra | exact HE2'].
               +++ rewrite (interp_segment_right e1 v1 e2 v2 Hgap).
                   (* interp_linear ((e2,v2)::rest') e2 = v2 *)
                   destruct rest' as [| [e3 v3] rest''].
                   *** simpl. reflexivity.
                   *** simpl. destruct (Rle_lt_dec e2 e3) as [_ | Hc].
                       ---- symmetry. apply interp_segment_left.
                            simpl in Hsort_tail.
                            destruct Hsort_tail; lra.
                       ---- exfalso. simpl in Hsort_tail.
                            destruct Hsort_tail; lra.
        ** (* E > e2: in a neighborhood, interp_linear matches tail *)
           apply (continuous_ext_loc (interp_linear ((e1, v1) :: (e2, v2) :: rest'))
                                     (interp_linear ((e2, v2) :: rest')) E).
           --- assert (HposR : 0 < (E - e2) / 2) by lra.
               exists (mkposreal _ HposR).
               intros y Hy. simpl in Hy.
               unfold ball in Hy; simpl in Hy. unfold AbsRing_ball in Hy.
               unfold abs in Hy; simpl in Hy.
               unfold minus, plus, opp in Hy; simpl in Hy.
               apply Rabs_def2 in Hy. destruct Hy as [_ Hy_gt].
               assert (Hy_gt' : e2 < y).
               { assert (Hposhalf : 0 < (E - e2) / 2) by lra. nra. }
               symmetry.
               apply interp_linear_tail; [lra | exact Hsort_outer].
           --- apply IH; [exact Hsort_full |].
               simpl. split; [lra | exact HE2'].
Qed.

(* === ex_RInt of interp_linear on the entire table interval === *)
Lemma ex_RInt_interp_linear :
  forall T, sorted_table T ->
    ex_RInt (interp_linear T) (head_E T) (last_E T).
Proof.
  induction T as [| [e1 v1] rest IH].
  - intros _. simpl. apply ex_RInt_point.
  - intros Hsort.
    destruct rest as [| [e2 v2] rest'].
    + simpl. apply ex_RInt_point.
    + simpl in Hsort. destruct Hsort as [Hgap Hsort_tail].
      simpl head_E. simpl last_E.
      apply ex_RInt_Chasles with (b := e2).
      * (* ex_RInt (interp_linear T) e1 e2 *)
        apply ex_RInt_ext with (f := interp_segment e1 v1 e2 v2).
        { intros x Hx.
          rewrite Rmin_left in Hx by lra.
          rewrite Rmax_right in Hx by lra.
          symmetry. apply interp_linear_first_segment. lra. }
        apply ex_RInt_interp_segment; exact Hgap.
      * (* ex_RInt (interp_linear T) e2 (last_E rest) *)
        assert (Hsort_full : sorted_table ((e2, v2) :: rest')).
        { destruct rest' as [| [e3 v3] rest''].
          - simpl. trivial.
          - simpl. exact Hsort_tail. }
        assert (Hle_simpl : e2 <= last_E ((e2, v2) :: rest'))
          by (apply (head_E_le_last_E ((e2, v2) :: rest')); exact Hsort_full).
        apply ex_RInt_ext with (f := interp_linear ((e2, v2) :: rest')).
        { intros x Hx.
          rewrite Rmin_left in Hx by exact Hle_simpl.
          rewrite Rmax_right in Hx by exact Hle_simpl.
          symmetry. apply interp_linear_tail.
          - lra.
          - simpl. split; [exact Hgap | exact Hsort_full]. }
        change (last_E ((e1, v1) :: (e2, v2) :: rest'))
          with (last_E ((e2, v2) :: rest')).
        apply IH. exact Hsort_full.
Qed.

(* ================================================================== *)
(* === Main equivalence: RInt of interpolant equals the trap sum === *)
(* ================================================================== *)

(* Recursive splitting lemma: integrating the interpolant over a multi-
   point table splits into the first trapezoid plus the integral of the
   tail interpolant. *)
Lemma RInt_interp_linear_split :
  forall e1 v1 e2 v2 rest',
    e1 < e2 ->
    sorted_table ((e2, v2) :: rest') ->
    RInt (interp_linear ((e1, v1) :: (e2, v2) :: rest'))
         e1 (last_E ((e2, v2) :: rest')) =
    (v1 + v2) / 2 * (e2 - e1) +
    RInt (interp_linear ((e2, v2) :: rest'))
         e2 (last_E ((e2, v2) :: rest')).
Proof.
  intros e1 v1 e2 v2 rest' Hgap Hsort_full.
  assert (Hsort_outer : sorted_table ((e1, v1) :: (e2, v2) :: rest'))
    by (simpl; split; [exact Hgap | exact Hsort_full]).
  assert (Hle : e2 <= last_E ((e2, v2) :: rest'))
    by (apply (head_E_le_last_E ((e2, v2) :: rest')); exact Hsort_full).
  assert (Hex1 : ex_RInt (interp_linear ((e1, v1) :: (e2, v2) :: rest')) e1 e2).
  { apply ex_RInt_ext with (f := interp_segment e1 v1 e2 v2).
    { intros x Hx.
      rewrite Rmin_left in Hx by lra.
      rewrite Rmax_right in Hx by lra.
      symmetry. apply interp_linear_first_segment. lra. }
    apply ex_RInt_interp_segment; exact Hgap. }
  assert (Hex2 : ex_RInt (interp_linear ((e1, v1) :: (e2, v2) :: rest'))
                         e2 (last_E ((e2, v2) :: rest'))).
  { apply ex_RInt_ext with (f := interp_linear ((e2, v2) :: rest')).
    { intros x Hx.
      rewrite Rmin_left in Hx by exact Hle.
      rewrite Rmax_right in Hx by exact Hle.
      symmetry. apply interp_linear_tail; [lra | exact Hsort_outer]. }
    apply ex_RInt_interp_linear. exact Hsort_full. }
  assert (HChasles : RInt (interp_linear ((e1, v1) :: (e2, v2) :: rest'))
                          e1 (last_E ((e2, v2) :: rest')) =
                     plus (RInt (interp_linear
                                   ((e1, v1) :: (e2, v2) :: rest')) e1 e2)
                          (RInt (interp_linear
                                   ((e1, v1) :: (e2, v2) :: rest'))
                                e2 (last_E ((e2, v2) :: rest')))).
  { symmetry. apply (@RInt_Chasles R_CompleteNormedModule); assumption. }
  assert (Hseg : RInt (interp_linear ((e1, v1) :: (e2, v2) :: rest')) e1 e2
                 = (v1 + v2) / 2 * (e2 - e1)).
  { rewrite <- (RInt_interp_segment e1 v1 e2 v2 Hgap).
    apply (@RInt_ext R_CompleteNormedModule).
    intros x Hx.
    rewrite Rmin_left in Hx by lra.
    rewrite Rmax_right in Hx by lra.
    apply interp_linear_first_segment. lra. }
  assert (HTail : RInt (interp_linear ((e1, v1) :: (e2, v2) :: rest'))
                       e2 (last_E ((e2, v2) :: rest'))
                   = RInt (interp_linear ((e2, v2) :: rest'))
                          e2 (last_E ((e2, v2) :: rest'))).
  { apply (@RInt_ext R_CompleteNormedModule).
    intros x Hx.
    rewrite Rmin_left in Hx by exact Hle.
    rewrite Rmax_right in Hx by exact Hle.
    apply interp_linear_tail; [lra | exact Hsort_outer]. }
  rewrite HChasles, Hseg, HTail.
  unfold plus; simpl. reflexivity.
Qed.

Theorem RInt_interp_linear_eq_trap :
  forall T, sorted_table T ->
    RInt (interp_linear T) (head_E T) (last_E T) = trap_integral T.
Proof.
  induction T as [| [e1 v1] rest IH].
  - intros _. simpl. apply (@RInt_point R_CompleteNormedModule).
  - intros Hsort.
    destruct rest as [| [e2 v2] rest'].
    + simpl. apply (@RInt_point R_CompleteNormedModule).
    + simpl in Hsort. destruct Hsort as [Hgap Hsort_tail].
      assert (Hsort_full : sorted_table ((e2, v2) :: rest')).
      { destruct rest' as [| [e3 v3] rest''].
        - simpl. trivial.
        - simpl. exact Hsort_tail. }
      (* The fixpoint accessors head_E, last_E, trap_integral
         iota-reduce eagerly in the goal. *)
      pose proof (RInt_interp_linear_split e1 v1 e2 v2 rest' Hgap Hsort_full) as Hsplit.
      simpl in *. rewrite Hsplit. f_equal.
      apply IH. exact Hsort_full.
Qed.

(* === Integrability and value of the zero-extended interpolant === *)

Lemma ex_RInt_interp_linear_ext :
  forall T, sorted_table T ->
    ex_RInt (interp_linear_ext T) (head_E T) (last_E T).
Proof.
  intros T Hsort.
  apply ex_RInt_ext with (f := interp_linear T).
  - intros x Hx.
    rewrite Rmin_left in Hx by (apply head_E_le_last_E; exact Hsort).
    rewrite Rmax_right in Hx by (apply head_E_le_last_E; exact Hsort).
    symmetry. apply interp_linear_ext_inside. lra.
  - apply ex_RInt_interp_linear. exact Hsort.
Qed.

Theorem RInt_interp_linear_ext_eq_trap :
  forall T, sorted_table T ->
    RInt (interp_linear_ext T) (head_E T) (last_E T) = trap_integral T.
Proof.
  intros T Hsort.
  transitivity (RInt (interp_linear T) (head_E T) (last_E T)).
  - apply (@RInt_ext R_CompleteNormedModule).
    intros x Hx.
    rewrite Rmin_left in Hx by (apply head_E_le_last_E; exact Hsort).
    rewrite Rmax_right in Hx by (apply head_E_le_last_E; exact Hsort).
    apply interp_linear_ext_inside. lra.
  - apply RInt_interp_linear_eq_trap. exact Hsort.
Qed.

(* ================================================================== *)
(* === Curvature-bounded interpolation error per segment ===
   For sigma in C^2 on [a, b], the linear interpolant
   interp_segment a (sigma a) b (sigma b) approximates sigma with error
   bounded by the supremum of |sigma''| times (b-a)^2. The canonical
   tight constant is 1/8 (from the Rolle's-theorem-twice argument), but
   the proof below — using three applications of Coquelicot's MVT_gen —
   gives the weaker constant 1. Either form establishes the same
   O((b-a)^2) curvature scaling, which is the content of the bound.
   The /8 sharpening is left for a future iteration that bridges
   is_derive into Stdlib's Rolle. *)
(* ================================================================== *)

Theorem interp_segment_curvature_error :
  forall (sigma : R -> R) (a b M2 : R),
    a < b ->
    0 <= M2 ->
    (forall x, a <= x <= b -> is_derive sigma x (Derive sigma x)) ->
    (forall x, a <= x <= b -> is_derive (Derive sigma) x
                                        (Derive (Derive sigma) x)) ->
    (forall x, a <= x <= b -> continuous sigma x) ->
    (forall x, a <= x <= b -> continuous (Derive sigma) x) ->
    (forall x, a <= x <= b -> Rabs (Derive (Derive sigma) x) <= M2) ->
    forall t, a <= t <= b ->
      Rabs (sigma t - interp_segment a (sigma a) b (sigma b) t) <=
        M2 * (b - a) * (b - a).
Proof.
  intros sigma a b M2 Hab HM2 Hsig_d Hsig_dd Hsig_c Hsig_d_c Hsig_dd_bnd t Ht.
  destruct (Rle_lt_dec t a) as [Htla | Htga].
  - (* t = a *)
    assert (Hteq : t = a) by lra. rewrite Hteq.
    rewrite (interp_segment_left a (sigma a) b (sigma b) Hab).
    replace (sigma a - sigma a) with 0 by ring.
    rewrite Rabs_R0.
    repeat apply Rmult_le_pos; lra.
  - destruct (Rle_lt_dec b t) as [Htgb | Htlb].
    + (* t = b *)
      assert (Hteq : t = b) by lra. rewrite Hteq.
      rewrite (interp_segment_right a (sigma a) b (sigma b) Hab).
      replace (sigma b - sigma b) with 0 by ring.
      rewrite Rabs_R0.
      repeat apply Rmult_le_pos; lra.
    + (* a < t < b *)
      assert (Hat : a < t) by exact Htga.
      assert (Htb : t < b) by exact Htlb.
      (* Step 1: MVT on sigma on [a, b]: ∃ c ∈ (a, b),
         sigma(b) - sigma(a) = sigma'(c) * (b - a). *)
      destruct (MVT_gen sigma a b (Derive sigma)) as [c [Hc Heqc]].
      { intros x Hx. rewrite Rmin_left in Hx by lra.
        rewrite Rmax_right in Hx by lra. apply Hsig_d. lra. }
      { intros x Hx. rewrite Rmin_left in Hx by lra.
        rewrite Rmax_right in Hx by lra.
        apply continuity_pt_filterlim. apply Hsig_c. lra. }
      rewrite Rmin_left in Hc by lra. rewrite Rmax_right in Hc by lra.
      (* Step 2: MVT on sigma on [a, t]: ∃ α ∈ (a, t),
         sigma(t) - sigma(a) = sigma'(α) * (t - a). *)
      destruct (MVT_gen sigma a t (Derive sigma)) as [alpha [Halpha Heqalpha]].
      { intros x Hx. rewrite Rmin_left in Hx by lra.
        rewrite Rmax_right in Hx by lra. apply Hsig_d. lra. }
      { intros x Hx. rewrite Rmin_left in Hx by lra.
        rewrite Rmax_right in Hx by lra.
        apply continuity_pt_filterlim. apply Hsig_c. lra. }
      rewrite Rmin_left in Halpha by lra. rewrite Rmax_right in Halpha by lra.
      (* Compute sigma(t) - L(t):
         L(t) = sigma(a) + secant * (t - a)
              = sigma(a) + sigma'(c) * (t - a)  [from Step 1]
         sigma(t) = sigma(a) + sigma'(alpha) * (t - a)  [from Step 2]
         => sigma(t) - L(t) = (sigma'(alpha) - sigma'(c)) * (t - a). *)
      assert (Hdiff :
        sigma t - interp_segment a (sigma a) b (sigma b) t =
        (Derive sigma alpha - Derive sigma c) * (t - a)).
      { unfold interp_segment.
        assert (Hslope : (sigma b - sigma a) / (b - a) = Derive sigma c)
          by (field_simplify; [rewrite Heqc; field; lra | lra]).
        assert (Hsigt : sigma t - sigma a = Derive sigma alpha * (t - a))
          by (rewrite Heqalpha; ring).
        nra. }
      rewrite Hdiff.
      (* Step 3: MVT on sigma' on the interval containing alpha and c.
         For Derive(Derive sigma) bounded by M2,
         |sigma'(alpha) - sigma'(c)| ≤ M2 * |alpha - c|. *)
      assert (Halpha_in_ab : a <= alpha <= b) by lra.
      assert (Hc_in_ab : a <= c <= b) by lra.
      assert (Hbound_diff :
        Rabs (Derive sigma alpha - Derive sigma c) <= M2 * (b - a)).
      { destruct (Rle_lt_dec alpha c) as [Hac | Hac].
        - (* alpha <= c *)
          destruct (Req_dec alpha c) as [Heq | Hne].
          + rewrite Heq. replace (Derive sigma c - Derive sigma c) with 0 by ring.
            rewrite Rabs_R0.
            apply Rmult_le_pos; lra.
          + assert (Halt_lt_c : alpha < c) by lra.
            destruct (MVT_gen (Derive sigma) alpha c (Derive (Derive sigma)))
              as [eta [Heta Heqeta]].
            { intros x Hx. rewrite Rmin_left in Hx by lra.
              rewrite Rmax_right in Hx by lra.
              apply Hsig_dd. lra. }
            { intros x Hx. rewrite Rmin_left in Hx by lra.
              rewrite Rmax_right in Hx by lra.
              apply continuity_pt_filterlim. apply Hsig_d_c. lra. }
            rewrite Rmin_left in Heta by lra.
            rewrite Rmax_right in Heta by lra.
            (* Heqeta : Derive sigma c - Derive sigma alpha =
                        Derive (Derive sigma) eta * (c - alpha) *)
            rewrite <- Rabs_Ropp.
            replace (- (Derive sigma alpha - Derive sigma c))
              with (Derive sigma c - Derive sigma alpha) by ring.
            rewrite Heqeta.
            rewrite Rabs_mult.
            rewrite (Rabs_right (c - alpha)) by lra.
            apply Rle_trans with (M2 * (c - alpha)).
            * apply Rmult_le_compat_r; [lra |].
              apply Hsig_dd_bnd. lra.
            * apply Rmult_le_compat_l; [exact HM2 | lra].
        - (* c < alpha *)
          assert (Hc_lt_alpha : c < alpha) by lra.
          destruct (MVT_gen (Derive sigma) c alpha (Derive (Derive sigma)))
            as [eta [Heta Heqeta]].
          { intros x Hx. rewrite Rmin_left in Hx by lra.
            rewrite Rmax_right in Hx by lra.
            apply Hsig_dd. lra. }
          { intros x Hx. rewrite Rmin_left in Hx by lra.
            rewrite Rmax_right in Hx by lra.
            apply continuity_pt_filterlim. apply Hsig_d_c. lra. }
          rewrite Rmin_left in Heta by lra.
          rewrite Rmax_right in Heta by lra.
          assert (HsignDiff :
            Rabs (Derive sigma alpha - Derive sigma c) =
            Rabs (Derive (Derive sigma) eta) * (alpha - c)).
          { rewrite Heqeta. rewrite Rabs_mult.
            rewrite (Rabs_right (alpha - c)) by lra. reflexivity. }
          rewrite HsignDiff.
          apply Rle_trans with (M2 * (alpha - c)).
          + apply Rmult_le_compat_r; [lra |].
            apply Hsig_dd_bnd. lra.
          + apply Rmult_le_compat_l; [exact HM2 | lra]. }
      rewrite Rabs_mult.
      rewrite (Rabs_right (t - a)) by lra.
      apply Rle_trans with (M2 * (b - a) * (t - a)).
      * apply Rmult_le_compat_r; [lra | exact Hbound_diff].
      * apply Rmult_le_compat_l.
        -- apply Rmult_le_pos; lra.
        -- lra.
Qed.

(* ================================================================== *)
(* === Interpolation error bound === *)
(* ================================================================== *)

(* The integral of a uniformly-bounded difference between sigma_true and
   the interpolant is itself bounded: |RInt sigma_true - RInt
   interp_linear| <= eps * (b - a). Proved via abs_RInt_le and
   RInt_minus, exactly as specified by the work item. *)
Theorem interp_error_bound :
  forall (sigma_true : R -> R) (T : iaea_table) (eps a b : R),
    a <= b ->
    0 <= eps ->
    ex_RInt sigma_true a b ->
    ex_RInt (interp_linear T) a b ->
    (forall E, a <= E <= b ->
       Rabs (sigma_true E - interp_linear T E) <= eps) ->
    Rabs (RInt sigma_true a b - RInt (interp_linear T) a b) <=
      eps * (b - a).
Proof.
  intros sigma_true T eps a b Hab Heps Hex_t Hex_i Hbound.
  (* Step 0: integrability of f - g and of |f - g|. *)
  assert (Hex_diff : ex_RInt (fun E => sigma_true E - interp_linear T E) a b).
  { apply ex_RInt_ext with
      (f := fun E => minus (sigma_true E) (interp_linear T E)).
    { intros x _. unfold minus, plus, opp; simpl. unfold Rminus.
      reflexivity. }
    apply (@ex_RInt_minus R_CompleteNormedModule); assumption. }
  assert (Hex_abs : ex_RInt
    (fun E => Rabs (sigma_true E - interp_linear T E)) a b).
  { apply ex_RInt_ext with
      (f := fun E => norm (sigma_true E - interp_linear T E)).
    { intros x _. reflexivity. }
    apply ex_RInt_norm. exact Hex_diff. }
  (* Step 1: rewrite the difference of integrals as integral of difference. *)
  assert (Hminus :
    RInt sigma_true a b - RInt (interp_linear T) a b =
      RInt (fun E => sigma_true E - interp_linear T E) a b).
  { transitivity (minus (RInt sigma_true a b) (RInt (interp_linear T) a b)).
    { unfold minus, plus, opp; simpl. unfold Rminus. reflexivity. }
    rewrite <- (@RInt_minus R_CompleteNormedModule sigma_true
                  (interp_linear T) a b Hex_t Hex_i).
    apply (@RInt_ext R_CompleteNormedModule).
    intros x _. unfold minus, plus, opp; simpl. unfold Rminus.
    reflexivity. }
  rewrite Hminus.
  (* Step 2: bound the integral by integral of |diff| *)
  apply Rle_trans with
    (RInt (fun E => Rabs (sigma_true E - interp_linear T E)) a b).
  - apply abs_RInt_le; [exact Hab | exact Hex_diff].
  - (* Step 3: integral of |diff| <= integral of eps *)
    apply Rle_trans with (RInt (fun _ : R => eps) a b).
    + apply RInt_le; [exact Hab | exact Hex_abs | apply ex_RInt_const |].
      intros x Hx. apply Hbound. lra.
    + (* Step 4: integral of eps = eps * (b - a) *)
      rewrite RInt_const.
      unfold scal; simpl. unfold mult; simpl. lra.
Qed.

(* ================================================================== *)
(* === Sample IAEA-style table and computation === *)
(* ================================================================== *)

(* Illustrative 5-point evaluation of the p-11B cross section in the
   resonance window. The 0.675 MeV point is near the dominant resonance;
   the values are in arbitrary illustrative units. *)
Definition iaea_pB_sample : iaea_table :=
  [(1/10, 0); (1/2, 1); (675/1000, 12); (1, 4); (2, 2)].

Lemma iaea_pB_sample_sorted : sorted_table iaea_pB_sample.
Proof.
  unfold iaea_pB_sample. simpl.
  repeat split; lra.
Qed.

Lemma iaea_pB_sample_head : head_E iaea_pB_sample = 1/10.
Proof. reflexivity. Qed.

Lemma iaea_pB_sample_last : last_E iaea_pB_sample = 2.
Proof. reflexivity. Qed.

(* The sample trap_integral evaluates to an explicit rational. *)
Lemma iaea_pB_sample_trap_value :
  trap_integral iaea_pB_sample =
    (0 + 1) / 2 * (1/2 - 1/10) +
    ((1 + 12) / 2 * (675/1000 - 1/2) +
     ((12 + 4) / 2 * (1 - 675/1000) +
      ((4 + 2) / 2 * (2 - 1) + 0))).
Proof. unfold iaea_pB_sample. simpl. reflexivity. Qed.

(* And so the closed-form integral of the interpolant on the sample
   matches the explicit trapezoidal sum. *)
Corollary iaea_pB_sample_integral :
  RInt (interp_linear iaea_pB_sample) (head_E iaea_pB_sample)
       (last_E iaea_pB_sample) = trap_integral iaea_pB_sample.
Proof.
  apply RInt_interp_linear_eq_trap. apply iaea_pB_sample_sorted.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions RInt_interp_segment.
Print Assumptions ex_RInt_interp_linear.
Print Assumptions RInt_interp_linear_eq_trap.
Print Assumptions interp_error_bound.
Print Assumptions iaea_pB_sample_integral.
