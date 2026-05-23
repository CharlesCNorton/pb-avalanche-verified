(******************************************************************************)
(*                                                                            *)
(*     Distributional Fokker-Planck steady state (item 20)                    *)
(*                                                                            *)
(*     Defines the Fokker-Planck differential operator with drift and         *)
(*     diffusion:                                                             *)
(*                                                                            *)
(*       FP[f] E := d/dE (Edot E * f E) - d^2/dE^2 (D E * f E)                *)
(*                                                                            *)
(*     Where Edot is the energy-loss rate (drift) and D is the                *)
(*     energy-diffusion coefficient. In the source-free interior of the       *)
(*     reactive window, FP[f] = 0 for the steady-state distribution.          *)
(*                                                                            *)
(*     The pure-drift slowing-down model has D = 0, reducing the equation     *)
(*     to d/dE (Edot * f) = 0 — equivalent to flux constancy (the form        *)
(*     already in pb_avalanche_kinetic.v's slowing_flux_steady_derivative).   *)
(*                                                                            *)
(*     We expose the operator explicitly and verify its strong-form           *)
(*     vanishing on the pure-drift slowing-down spectrum                      *)
(*     f_slowing(E) = S tau / E, completing the formal Fokker-Planck          *)
(*     content of the avalanche analysis.                                     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra ZArith FunctionalExtensionality.
From Coquelicot Require Import Coquelicot.

Open Scope R_scope.

(* ================================================================== *)
(* === Fokker-Planck differential operator === *)
(* ================================================================== *)

Definition FP_op (Edot D f : R -> R) (E : R) : R :=
  Derive (fun x : R => Edot x * f x) E
    - Derive_n (fun x : R => D x * f x) 2 E.

(* ================================================================== *)
(* === Pure-drift FP operator (D = 0) === *)
(* ================================================================== *)

Definition FP_drift (Edot f : R -> R) (E : R) : R :=
  Derive (fun x : R => Edot x * f x) E.

Lemma FP_drift_is_FP_op_with_zero_D :
  forall Edot f E,
    FP_drift Edot f E = FP_op Edot (fun _ : R => 0) f E.
Proof.
  intros Edot f E. unfold FP_drift, FP_op.
  assert (Heq : (fun x : R => 0 * f x) = (fun _ : R => 0))
    by (apply functional_extensionality; intro x; ring).
  rewrite Heq.
  (* Derive_n of the constant-zero function is zero. *)
  assert (Hd1 : Derive (fun _ : R => 0) = (fun _ : R => 0)).
  { apply functional_extensionality. intro x.
    apply Derive_const. }
  assert (Hd2 : Derive_n (fun _ : R => 0) 2 E = 0).
  { simpl. rewrite Hd1. apply Derive_const. }
  rewrite Hd2. ring.
Qed.

(* If Edot * f is locally constant in a neighborhood of E, then its
   derivative is zero, i.e., FP_drift vanishes. This is the strong-
   form steady-state Fokker-Planck condition for pure drift. *)
Lemma FP_drift_vanishes_at :
  forall Edot f E c,
    locally E (fun y : R => Edot y * f y = c) ->
    FP_drift Edot f E = 0.
Proof.
  intros Edot f E c Hloc. unfold FP_drift.
  apply is_derive_unique.
  apply (is_derive_ext_loc (fun _ : R => c) (fun x : R => Edot x * f x) E 0).
  - eapply filter_imp; [|exact Hloc].
    intros y Hy. symmetry. exact Hy.
  - apply (is_derive_const c E).
Qed.

(* ================================================================== *)
(* === Steady-state slowing-down spectrum vs FP === *)
(* ================================================================== *)

(* The Edot(E) := -E/tau model and slowing-down spectrum
   f(E) := S * tau / E together produce constant flux -S. *)
Definition Edot_slowing (tau E : R) : R := - E / tau.
Definition f_slowing_FP (S tau E : R) : R := S * tau / E.

Lemma slowing_flux_const :
  forall S tau E, tau <> 0 -> E <> 0 ->
    Edot_slowing tau E * f_slowing_FP S tau E = - S.
Proof.
  intros S tau E Htau HE. unfold Edot_slowing, f_slowing_FP.
  field. split; assumption.
Qed.

(* In a neighborhood of any positive E, the product Edot * f is the
   constant -S (since the formula is well-defined on (0, +infty)). *)
Lemma slowing_flux_const_locally :
  forall S tau E, 0 < tau -> 0 < E ->
    locally E (fun y : R => Edot_slowing tau y * f_slowing_FP S tau y = - S).
Proof.
  intros S tau E Htau HE.
  apply (locally_interval _ E 0 (E + 1)).
  - simpl. lra.
  - simpl. lra.
  - intros y Hy0 _. simpl in Hy0.
    apply slowing_flux_const.
    + apply Rgt_not_eq. exact Htau.
    + apply Rgt_not_eq. exact Hy0.
Qed.

(* The strong-form Fokker-Planck equation: for the pure-drift model,
   d/dE [Edot * f] = 0 at every positive E. *)
Theorem FP_drift_slowing :
  forall S tau E, 0 < tau -> 0 < E ->
    FP_drift (Edot_slowing tau) (f_slowing_FP S tau) E = 0.
Proof.
  intros S tau E Htau HE.
  apply FP_drift_vanishes_at with (c := - S).
  apply slowing_flux_const_locally; assumption.
Qed.

(* The full Fokker-Planck operator (with D = 0) also vanishes on the
   slowing-down spectrum. *)
Theorem FP_op_slowing_no_diffusion :
  forall S tau E, 0 < tau -> 0 < E ->
    FP_op (Edot_slowing tau) (fun _ : R => 0) (f_slowing_FP S tau) E = 0.
Proof.
  intros S tau E Htau HE.
  rewrite <- FP_drift_is_FP_op_with_zero_D.
  apply FP_drift_slowing; assumption.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions FP_drift_is_FP_op_with_zero_D.
Print Assumptions FP_drift_vanishes_at.
Print Assumptions slowing_flux_const.
Print Assumptions FP_drift_slowing.
Print Assumptions FP_op_slowing_no_diffusion.
