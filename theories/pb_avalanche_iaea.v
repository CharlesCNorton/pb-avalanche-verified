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
  assert (HF_deriv : forall x : R,
            is_derive F x (interp_segment e1 v1 e2 v2 x)).
  { intro x. unfold F. unfold interp_segment.
    auto_derive.
    - exact I.
    - field. lra. }
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
