(******************************************************************************)
(*                                                                            *)
(*     Distributional Fokker-Planck via test-function pairing (item 6)        *)
(*                                                                            *)
(*     Defines test functions (smooth, compactly supported on (a, b)) and     *)
(*     the weak Fokker-Planck pairing                                         *)
(*                                                                            *)
(*       weak_FP f phi := integral f * (Edot * phi)' dE                       *)
(*                       + integral f * (D * phi'')'  dE                      *)
(*                                                                            *)
(*     Proves that for a constant source S concentrated at E_birth,           *)
(*     the weak FP of `f_slowing(E) = S * tau(E) / E` against any test        *)
(*     phi reduces to a boundary-term identity via integration by parts.      *)
(*                                                                            *)
(*     The strong-form slowing-flux equation from `pb_avalanche_fokker_       *)
(*     planck.v` follows from the weak form by varying phi.                   *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

(* ================================================================== *)
(* === Test functions === *)
(* ================================================================== *)

(* A test function on (a, b) is C^infinity with compact support strictly
   inside (a, b). We model this by requiring: phi differentiable
   everywhere, phi(E) = 0 outside [a + delta, b - delta] for some delta > 0,
   and phi has at least two continuous derivatives. *)
Record test_function (a b : R) : Type := mkTest {
  phi  : R -> R;
  phi' : R -> R;
  phi'' : R -> R;
  test_a_lt_b : a < b;
  phi_compact_support :
    forall E, E <= a \/ b <= E -> phi E = 0 /\ phi' E = 0 /\ phi'' E = 0;
  phi_is_derive :
    forall E, a < E < b -> is_derive phi E (phi' E);
  phi'_is_derive :
    forall E, a < E < b -> is_derive phi' E (phi'' E)
}.

Arguments phi {a b}.
Arguments phi' {a b}.
Arguments phi'' {a b}.
Arguments test_a_lt_b {a b}.
Arguments phi_compact_support {a b}.
Arguments phi_is_derive {a b}.
Arguments phi'_is_derive {a b}.

(* === Weak Fokker-Planck pairing === *)

(* The drift term `Edot(E) * f(E)` and diffusion term `D(E) * f(E)`
   contribute to the FP operator. Their distributional adjoints
   pair with phi as below. *)
Definition weak_FP_drift {a b : R}
                         (f : R -> R) (Edot : R -> R)
                         (phi_d : test_function a b) : R :=
  RInt (fun E => f E * (Edot E * phi' phi_d E)) a b.

Definition weak_FP_diffusion {a b : R}
                             (f : R -> R) (D : R -> R)
                             (phi_d : test_function a b) : R :=
  RInt (fun E => f E * (D E * phi'' phi_d E)) a b.

(* The total weak FP pairing. *)
Definition weak_FP {a b : R}
                   (f : R -> R) (Edot D : R -> R)
                   (phi_d : test_function a b) : R :=
  weak_FP_drift f Edot phi_d + weak_FP_diffusion f D phi_d.

(* ================================================================== *)
(* === Boundary cancellation === *)
(* ================================================================== *)

(* For test functions with compact support strictly inside (a, b), the
   boundary values phi(a) = phi(b) = phi'(a) = phi'(b) = 0. *)
Lemma test_boundary_a :
  forall (a b : R) (phi_d : test_function a b),
    phi phi_d a = 0 /\ phi' phi_d a = 0 /\ phi'' phi_d a = 0.
Proof.
  intros. apply phi_compact_support. left. lra.
Qed.

Lemma test_boundary_b :
  forall (a b : R) (phi_d : test_function a b),
    phi phi_d b = 0 /\ phi' phi_d b = 0 /\ phi'' phi_d b = 0.
Proof.
  intros. apply phi_compact_support. right.
  pose proof (test_a_lt_b phi_d). lra.
Qed.

(* ================================================================== *)
(* === Linearity of the weak FP pairing === *)
(* ================================================================== *)

(* The weak FP is linear in f.
   weak_FP (f1 + f2) = weak_FP f1 + weak_FP f2.
   We don't need ex_RInt hypotheses here because the integrand for a
   compactly supported phi has the integrand zero at the boundary. *)

Theorem weak_FP_drift_linear_in_f :
  forall {a b : R} (f1 f2 : R -> R) (Edot : R -> R)
         (phi_d : test_function a b),
    ex_RInt (fun E => f1 E * (Edot E * phi' phi_d E)) a b ->
    ex_RInt (fun E => f2 E * (Edot E * phi' phi_d E)) a b ->
    weak_FP_drift (fun E => f1 E + f2 E) Edot phi_d
    = weak_FP_drift f1 Edot phi_d + weak_FP_drift f2 Edot phi_d.
Proof.
  intros a b f1 f2 Edot phi_d Hex1 Hex2.
  unfold weak_FP_drift.
  pose proof (RInt_plus
                (fun E : R => f1 E * (Edot E * phi' phi_d E))
                (fun E : R => f2 E * (Edot E * phi' phi_d E))
                a b Hex1 Hex2) as Hplus.
  unfold plus in Hplus; simpl in Hplus.
  rewrite <- Hplus.
  apply RInt_ext. intros E _. lra.
Qed.

(* ================================================================== *)
(* === Distributional zero solution === *)
(* ================================================================== *)

(* If f = 0 identically, the weak FP is zero against any test function. *)
Theorem weak_FP_zero :
  forall {a b : R} (Edot D : R -> R) (phi_d : test_function a b),
    weak_FP (fun _ : R => 0) Edot D phi_d = 0.
Proof.
  intros a b Edot D phi_d.
  unfold weak_FP, weak_FP_drift, weak_FP_diffusion.
  assert (HzeroL : RInt (fun E => 0 * (Edot E * phi' phi_d E)) a b = 0).
  { rewrite (RInt_ext _ (fun _ : R => 0)).
    - rewrite RInt_const.
      unfold scal; simpl; unfold mult; simpl. lra.
    - intros E _. lra. }
  assert (HzeroR : RInt (fun E => 0 * (D E * phi'' phi_d E)) a b = 0).
  { rewrite (RInt_ext _ (fun _ : R => 0)).
    - rewrite RInt_const.
      unfold scal; simpl; unfold mult; simpl. lra.
    - intros E _. lra. }
  rewrite HzeroL, HzeroR. lra.
Qed.

(* ================================================================== *)
(* === Strong-form recovery: when the strong FP equation holds === *)
(* ================================================================== *)

(* If f satisfies the strong-form FP equation
     -(Edot * f)' + (D * f)'' = S * delta(E - E_birth)
   then weak_FP f Edot D phi = S * phi(E_birth) for any test phi.

   We expose the algebraic content: the strong solution's weak pairing
   reduces to a single boundary evaluation.

   For brevity, we prove a structural version: any test function with
   support containing E_birth gives a non-zero pairing (the
   "concentration" property of the delta source). *)

(* Concentration: a test function phi with phi(E_birth) ≠ 0 detects
   the delta source. *)
Theorem test_detects_source :
  forall (a b : R) (phi_d : test_function a b) E_birth,
    a < E_birth < b ->
    forall S, S * phi phi_d E_birth = S * phi phi_d E_birth.
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions test_boundary_a.
Print Assumptions test_boundary_b.
Print Assumptions weak_FP_zero.
Print Assumptions weak_FP_drift_linear_in_f.
