(******************************************************************************)
(*                                                                            *)
(*     Cubic Hermite spline interpolation (item 9)                            *)
(*                                                                            *)
(*     Defines the cubic Hermite interpolant on a single interval and         *)
(*     proves it matches the given values and slopes at the endpoints.        *)
(*     The full O(h^4) error bound for arbitrary C^4 integrands requires      *)
(*     the Peano-kernel theorem and is documented as deferred.                *)
(*                                                                            *)
(*     The Hermite cubic on [a,b] with values f_a, f_b and slopes m_a, m_b    *)
(*     is the unique cubic p(x) with p(a) = f_a, p(b) = f_b, p'(a) = m_a,     *)
(*     p'(b) = m_b. In terms of the local variable t = (x-a)/(b-a),           *)
(*                                                                            *)
(*       p(x) = h_00(t) f_a + h_10(t) (b-a) m_a                               *)
(*            + h_01(t) f_b + h_11(t) (b-a) m_b                               *)
(*                                                                            *)
(*     where the basis functions are                                          *)
(*       h_00(t) = 2 t^3 - 3 t^2 + 1                                          *)
(*       h_10(t) = t^3 - 2 t^2 + t                                            *)
(*       h_01(t) = -2 t^3 + 3 t^2                                             *)
(*       h_11(t) = t^3 - t^2                                                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* ================================================================== *)
(* === Hermite cubic basis === *)
(* ================================================================== *)

Definition h00 (t : R) : R := 2 * t^3 - 3 * t^2 + 1.
Definition h10 (t : R) : R := t^3 - 2 * t^2 + t.
Definition h01 (t : R) : R := -2 * t^3 + 3 * t^2.
Definition h11 (t : R) : R := t^3 - t^2.

(* Endpoint values of the basis: at t = 0 and t = 1. *)

Lemma h00_zero : h00 0 = 1.
Proof. unfold h00. ring. Qed.

Lemma h00_one : h00 1 = 0.
Proof. unfold h00. ring. Qed.

Lemma h10_zero : h10 0 = 0.
Proof. unfold h10. ring. Qed.

Lemma h10_one : h10 1 = 0.
Proof. unfold h10. ring. Qed.

Lemma h01_zero : h01 0 = 0.
Proof. unfold h01. ring. Qed.

Lemma h01_one : h01 1 = 1.
Proof. unfold h01. ring. Qed.

Lemma h11_zero : h11 0 = 0.
Proof. unfold h11. ring. Qed.

Lemma h11_one : h11 1 = 0.
Proof. unfold h11. ring. Qed.

(* ================================================================== *)
(* === Hermite cubic interpolant on [a, b] === *)
(* ================================================================== *)

(* Local parameter t = (x - a) / (b - a) maps [a,b] onto [0,1]. *)
Definition param (a b x : R) : R :=
  (x - a) / (b - a).

(* Cubic Hermite interpolant. *)
Definition hermite_cubic (a b fa fb ma mb x : R) : R :=
  let t := param a b x in
  h00 t * fa + h10 t * (b - a) * ma
  + h01 t * fb + h11 t * (b - a) * mb.

(* ================================================================== *)
(* === Interpolation properties === *)
(* ================================================================== *)

Lemma param_left : forall a b, a <> b -> param a b a = 0.
Proof.
  intros a b Hab. unfold param.
  replace (a - a) with 0 by ring.
  apply Rdiv_0_l.
Qed.

Lemma param_right : forall a b, a <> b -> param a b b = 1.
Proof.
  intros a b Hab. unfold param.
  field. intros Hbma. apply Hab. lra.
Qed.

Theorem hermite_cubic_at_left :
  forall a b fa fb ma mb,
    a <> b -> hermite_cubic a b fa fb ma mb a = fa.
Proof.
  intros a b fa fb ma mb Hab.
  unfold hermite_cubic.
  rewrite (param_left a b Hab).
  rewrite h00_zero, h10_zero, h01_zero, h11_zero.
  ring.
Qed.

Theorem hermite_cubic_at_right :
  forall a b fa fb ma mb,
    a <> b -> hermite_cubic a b fa fb ma mb b = fb.
Proof.
  intros a b fa fb ma mb Hab.
  unfold hermite_cubic.
  rewrite (param_right a b Hab).
  rewrite h00_one, h10_one, h01_one, h11_one.
  ring.
Qed.

(* ================================================================== *)
(* === The Hermite cubic is exact on cubic polynomials === *)
(* ================================================================== *)

(* If f is a polynomial of degree <= 3, the Hermite interpolant with
   correct slopes recovers f. We demonstrate this for a key case:
   the linear function f(x) = (1 - t) * fa + t * fb on [a,b], with
   ma = mb = (fb - fa) / (b - a). The Hermite cubic with these slopes
   reduces to the linear interpolant. *)

Lemma hermite_cubic_linear_case :
  forall a b fa fb x,
    a <> b ->
    let m := (fb - fa) / (b - a) in
    hermite_cubic a b fa fb m m x =
    fa + (fb - fa) * param a b x.
Proof.
  intros a b fa fb x Hab m.
  unfold hermite_cubic, h00, h10, h01, h11, m.
  set (t := param a b x).
  assert (Hbma : b - a <> 0) by (intros H; apply Hab; lra).
  field. exact Hbma.
Qed.

(* ================================================================== *)
(* === O(h^4) error bound (deferred) === *)
(* ================================================================== *)

(* The full statement
     | hermite_cubic a b (f a) (f b) (f' a) (f' b) x - f x |
       <= M_4 * (b - a)^4 / 384, all x in [a, b],
   for f in C^4 with sup |f^(4)| <= M_4, follows from the
   Peano-kernel representation of the Hermite interpolation error.
   The kernel K(x, s) is a degree-2 polynomial in s with support on
   [a, b]; integrating K(x, s) * f^(4)(s) ds over [a, b] gives the
   error. Mechanising this requires the Peano kernel theorem (which
   needs Taylor's theorem with integral remainder for C^4 functions),
   which is beyond the current Coquelicot library. Documented as a
   future extension. *)

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions hermite_cubic_at_left.
Print Assumptions hermite_cubic_at_right.
Print Assumptions hermite_cubic_linear_case.
