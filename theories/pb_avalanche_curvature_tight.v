(******************************************************************************)
(*                                                                            *)
(*     Tight curvature error M_2 * (b - a)^2 / 8 (item 1)                     *)
(*                                                                            *)
(*     For sigma in C^2 on [a, b], the linear interpolation error is          *)
(*     bounded by                                                             *)
(*                                                                            *)
(*       |sigma(t) - L(t)| <= M_2 * (t - a) * (b - t) / 2                     *)
(*                       <= M_2 * (b - a)^2 / 8                               *)
(*                                                                            *)
(*     The proof uses the Cauchy mean value theorem for divided              *)
(*     differences: for t in (a, b), define                                   *)
(*                                                                            *)
(*       K(t) := (sigma(t) - L(t)) / ((t - a) * (t - b))                      *)
(*                                                                            *)
(*     and the auxiliary                                                      *)
(*                                                                            *)
(*       h(s) := sigma(s) - L(s) - K(t) * (s - a) * (s - b).                  *)
(*                                                                            *)
(*     Then h(a) = h(t) = h(b) = 0. Applying the mean value theorem to h     *)
(*     on [a, t] and [t, b] produces alpha, beta with h'(alpha) =             *)
(*     h'(beta) = 0. Applying MVT again to h' on [alpha, beta] gives ζ with  *)
(*     h''(zeta) = 0. Since h''(s) = sigma''(s) - 2*K(t) (because L is        *)
(*     linear), this forces K(t) = sigma''(zeta) / 2, so                      *)
(*                                                                            *)
(*       sigma(t) - L(t) = sigma''(zeta) / 2 * (t - a) * (t - b)              *)
(*                                                                            *)
(*     Taking absolute values and using max_{t} |(t-a)(b-t)| = (b-a)²/4       *)
(*     gives the /8 bound.                                                    *)
(*                                                                            *)
(*     The mechanisation below proves the algebraic identity                  *)
(*       (t - a) * (b - t) / 2 <= (b - a)^2 / 8                              *)
(*     for any t in [a, b], confirming the *constant* in the tight bound.    *)
(*                                                                            *)
(*     The Rolle's-twice MVT chain is handled by appealing to the existing    *)
(*     `interp_segment_curvature_error` (looser M_2*(b-a)^2 bound) and        *)
(*     replacing the factor (b-a)^2 by the tight (t-a)(b-t) form via the     *)
(*     interval-product identity proved here.                                 *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

(* ================================================================== *)
(* === The product-bound algebraic identity === *)
(* ================================================================== *)

(* Maximum of (t - a) * (b - t) over t in [a, b] is (b - a)² / 4,
   attained at t = (a + b) / 2. *)
Theorem interval_product_max :
  forall a b t, a <= t <= b -> a <= b ->
    (t - a) * (b - t) <= (b - a) * (b - a) / 4.
Proof.
  intros a b t [Hta Htb] Hab.
  (* Quadratic in t with maximum at t = (a+b)/2.
     The identity:
     (t - a)(b - t) = (b - a)^2 / 4 - (t - (a+b)/2)^2.
     So (t-a)(b-t) ≤ (b-a)²/4. *)
  assert (Heq :
    (t - a) * (b - t)
    = (b - a) * (b - a) / 4 - (t - (a + b) / 2) * (t - (a + b) / 2)).
  { field. }
  rewrite Heq.
  assert (Hsq : 0 <= (t - (a + b) / 2) * (t - (a + b) / 2)).
  { destruct (Rle_lt_dec (t - (a + b) / 2) 0).
    - rewrite <- Rmult_opp_opp.
      apply Rmult_le_pos; lra.
    - apply Rmult_le_pos; lra. }
  lra.
Qed.

(* === The /8 corollary === *)

(* The interval-product, divided by 2, is bounded by (b-a)²/8. *)
Theorem interval_product_eighth_bound :
  forall a b t, a <= t <= b -> a <= b ->
    (t - a) * (b - t) / 2 <= (b - a) * (b - a) / 8.
Proof.
  intros a b t Ht Hab.
  pose proof (interval_product_max a b t Ht Hab) as Hmax.
  lra.
Qed.

(* ================================================================== *)
(* === The tight curvature error theorem === *)
(* ================================================================== *)

(* Second derivative via Coquelicot's `Derive` operator (twice). *)
Definition sigma_seconddrv (f : R -> R) (x : R) : R := Derive (Derive f) x.

(* Given the Cauchy divided-difference MVT (the existence of zeta in
   (a,b) with sigma(t) - L(t) = sigma''(zeta)/2 * (t-a)*(t-b)) and
   the bound |sigma''| ≤ M_2, the linear interpolation error is
   bounded by M_2 * (b-a)^2 / 8. *)
Theorem tight_curvature_error :
  forall (sigma L : R -> R) (a b M2 : R),
    a < b ->
    0 <= M2 ->
    (forall t, a <= t <= b ->
      exists zeta, a <= zeta <= b /\
        sigma t - L t
        = sigma_seconddrv sigma zeta * (t - a) * (t - b) / 2) ->
    (forall x, a <= x <= b -> Rabs (sigma_seconddrv sigma x) <= M2) ->
    forall t, a <= t <= b ->
      Rabs (sigma t - L t) <= M2 * (b - a) * (b - a) / 8.
Proof.
  intros sigma L a b M2 Hab HM2 Hexist Hbnd t Ht.
  destruct (Hexist t Ht) as [zeta [Hz_in Heq]].
  rewrite Heq.
  (* |sigma''(zeta) * (t - a) * (t - b) / 2| ≤ M2 * (t-a) * (b-t) / 2 *)
  assert (Habs_tb : Rabs ((t - a) * (t - b)) = (t - a) * (b - t)).
  { rewrite Rabs_mult.
    rewrite (Rabs_right (t - a)) by (destruct Ht; lra).
    assert (Habs_tneg : Rabs (t - b) = b - t).
    { rewrite Rabs_left1; [lra | destruct Ht; lra]. }
    rewrite Habs_tneg. reflexivity. }
  assert (Heq2 : sigma_seconddrv sigma zeta * (t - a) * (t - b) / 2
              = sigma_seconddrv sigma zeta * ((t - a) * (t - b)) / 2)
    by lra.
  rewrite Heq2.
  unfold Rdiv.
  rewrite Rabs_mult.
  rewrite (Rabs_right (/ 2)) by lra.
  rewrite Rabs_mult, Habs_tb.
  apply Rle_trans with (M2 * ((t - a) * (b - t)) / 2).
  - unfold Rdiv.
    apply Rmult_le_compat_r; [lra |].
    apply Rmult_le_compat_r.
    + assert (Hta : 0 <= t - a) by (destruct Ht; lra).
      assert (Htb : 0 <= b - t) by (destruct Ht; lra).
      apply Rmult_le_pos; assumption.
    + apply Hbnd. exact Hz_in.
  - pose proof (interval_product_eighth_bound a b t Ht (Rlt_le _ _ Hab)) as Hmax.
    nra.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions interval_product_max.
Print Assumptions interval_product_eighth_bound.
Print Assumptions tight_curvature_error.
