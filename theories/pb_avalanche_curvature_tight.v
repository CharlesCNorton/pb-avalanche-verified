(******************************************************************************)
(*                                                                            *)
(*     Tight curvature error M_2 * (b - a)^2 / 8 (item 1)                     *)
(*                                                                            *)
(*     For sigma in C^2 on [a, b], the linear interpolation error obeys the   *)
(*     SHARP bound                                                            *)
(*                                                                            *)
(*       |sigma(t) - L(t)| <= M_2 * (b - a)^2 / 8.                            *)
(*                                                                            *)
(*     The constant 1/8 is genuinely derived, not assumed: we mechanise the   *)
(*     Cauchy divided-difference mean value theorem by applying Rolle's       *)
(*     theorem THREE times to the auxiliary function                          *)
(*                                                                            *)
(*       h(s) := sigma(s) - L(s) - K (s - a)(s - b),                          *)
(*                                                                            *)
(*     where K is chosen so h(t) = 0. Since h(a) = h(t) = h(b) = 0, Rolle on  *)
(*     [a,t] and [t,b] gives alpha, beta with h'(alpha) = h'(beta) = 0;       *)
(*     Rolle on [alpha,beta] gives zeta with h''(zeta) = 0, forcing           *)
(*     K = sigma''(zeta)/2 and hence                                          *)
(*                                                                            *)
(*       sigma(t) - L(t) = sigma''(zeta)/2 * (t - a)(t - b).                  *)
(*                                                                            *)
(*     The Rolle steps use the Stdlib `Rolle` theorem (which yields an        *)
(*     INTERIOR critical point), bridged to Coquelicot's `is_derive` via      *)
(*     `is_derive_Reals`. Combined with max_{t} (t-a)(b-t) = (b-a)^2/4 this    *)
(*     gives the sharp 1/8 constant.                                          *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

(* ================================================================== *)
(* === Rolle's theorem for Coquelicot is_derive (interior point) === *)
(* ================================================================== *)

(* Bridge: from a global is_derive on [a,b] with f a = f b, obtain an
   INTERIOR point where the derivative vanishes. This uses the Stdlib
   `Rolle` theorem (giving the open-interval witness) bridged to
   Coquelicot's is_derive through is_derive_Reals. *)
Lemma rolle_is_derive :
  forall (f f' : R -> R) (a b : R),
    a < b ->
    (forall x, a <= x <= b -> is_derive f x (f' x)) ->
    f a = f b ->
    exists c, a < c < b /\ f' c = 0.
Proof.
  intros f f' a b Hab Hd Hfab.
  assert (pr : forall x, a < x < b -> derivable_pt f x).
  { intros x Hx. exists (f' x). apply is_derive_Reals. apply Hd. lra. }
  assert (Hcont : forall x, a <= x <= b -> continuity_pt f x).
  { intros x Hx. apply continuity_pt_filterlim.
    apply (ex_derive_continuous (K := R_AbsRing) (V := R_NormedModule)).
    exists (f' x). apply Hd; exact Hx. }
  destruct (Rolle f a b pr Hcont Hab Hfab) as [c [P Hc]].
  exists c. split; [exact P |].
  rewrite <- Hc.
  symmetry. apply derive_pt_eq_0. apply is_derive_Reals. apply Hd. lra.
Qed.

(* ================================================================== *)
(* === The interval-product bound === *)
(* ================================================================== *)

(* max_{t in [a,b]} (t - a)(b - t) = (b - a)^2 / 4, attained at the
   midpoint. *)
Theorem interval_product_max :
  forall a b t, a <= t <= b -> a <= b ->
    (t - a) * (b - t) <= (b - a) * (b - a) / 4.
Proof.
  intros a b t [Hta Htb] Hab.
  assert (Heq :
    (t - a) * (b - t)
    = (b - a) * (b - a) / 4 - (t - (a + b) / 2) * (t - (a + b) / 2))
    by field.
  rewrite Heq.
  assert (Hsq : 0 <= (t - (a + b) / 2) * (t - (a + b) / 2)).
  { destruct (Rle_lt_dec (t - (a + b) / 2) 0).
    - rewrite <- Rmult_opp_opp. apply Rmult_le_pos; lra.
    - apply Rmult_le_pos; lra. }
  lra.
Qed.

(* ================================================================== *)
(* === Divided-difference MVT and the tight error bound === *)
(* ================================================================== *)

Section TightCurvature.

Variables sigma df ddf : R -> R.
Variables a b : R.
Hypothesis Hab : a < b.
Hypothesis Hsig_d : forall x, a <= x <= b -> is_derive sigma x (df x).
Hypothesis Hdf_d : forall x, a <= x <= b -> is_derive df x (ddf x).

(* The linear interpolant through (a, sigma a) and (b, sigma b). *)
Definition slope := (sigma b - sigma a) / (b - a).
Definition Lin (s : R) := sigma a + slope * (s - a).

Section Fixed.
Variable t : R.
Hypothesis Ht : a < t < b.

(* K chosen so that the auxiliary h vanishes at t. *)
Definition Kc := (sigma t - Lin t) / ((t - a) * (t - b)).
Definition hf (s : R) := sigma s - Lin s - Kc * (s - a) * (s - b).
Definition dh (s : R) := df s - slope - Kc * (2 * s - a - b).
Definition ddh (s : R) := ddf s - 0 - Kc * 2.

Lemma Dhf : forall x, a <= x <= b -> is_derive hf x (dh x).
Proof.
  intros x Hx. unfold hf, dh.
  apply (is_derive_minus (fun s => sigma s - Lin s)
            (fun s => Kc * (s - a) * (s - b)) x
            (df x - slope) (Kc * (2 * x - a - b))).
  - apply (is_derive_minus sigma Lin x (df x) slope).
    + apply Hsig_d; exact Hx.
    + unfold Lin. auto_derive. trivial. unfold slope. field. lra.
  - auto_derive. trivial. ring.
Qed.

Lemma Ddh : forall x, a <= x <= b -> is_derive dh x (ddh x).
Proof.
  intros x Hx. unfold dh, ddh.
  apply (is_derive_minus (fun s => df s - slope)
            (fun s => Kc * (2 * s - a - b)) x (ddf x - 0) (Kc * 2)).
  - apply (is_derive_minus df (fun _ => slope) x (ddf x) 0).
    + apply Hdf_d; exact Hx.
    + auto_derive. trivial. ring.
  - auto_derive. trivial. ring.
Qed.

Lemma hf_a0 : hf a = 0.
Proof. unfold hf, Lin. field. Qed.

Lemma hf_b0 : hf b = 0.
Proof. unfold hf, Lin, slope. field. lra. Qed.

Lemma hf_t0 : hf t = 0.
Proof. unfold hf, Kc. field. split; lra. Qed.

(* The Cauchy divided-difference MVT: there is an interior zeta with
   sigma(t) - L(t) = sigma''(zeta)/2 * (t-a)(t-b). Proved by Rolle
   three times. *)
Theorem divided_difference_mvt :
  exists zeta, a < zeta < b /\
    sigma t - Lin t = ddf zeta / 2 * ((t - a) * (t - b)).
Proof.
  destruct (rolle_is_derive hf dh a t (proj1 Ht)
              (fun x Hx => Dhf x (conj (proj1 Hx)
                 (Rle_trans _ _ _ (proj2 Hx) (Rlt_le _ _ (proj2 Ht)))))
              (eq_trans hf_a0 (eq_sym hf_t0)))
    as [alpha [Halpha Hdha]].
  destruct (rolle_is_derive hf dh t b (proj2 Ht)
              (fun x Hx => Dhf x (conj
                 (Rle_trans _ _ _ (Rlt_le _ _ (proj1 Ht)) (proj1 Hx))
                 (proj2 Hx)))
              (eq_trans hf_t0 (eq_sym hf_b0)))
    as [beta [Hbeta Hdhb]].
  assert (Hab2 : alpha < beta) by lra.
  destruct (rolle_is_derive dh ddh alpha beta Hab2
              (fun x Hx => Ddh x (conj
                 (Rle_trans _ _ _ (Rlt_le _ _ (proj1 Halpha)) (proj1 Hx))
                 (Rle_trans _ _ _ (proj2 Hx) (Rlt_le _ _ (proj2 Hbeta)))))
              (eq_trans Hdha (eq_sym Hdhb)))
    as [zeta [Hzeta Hddhz]].
  exists zeta. split.
  - split; lra.
  - unfold ddh in Hddhz.
    assert (Hddf : ddf zeta = 2 * Kc) by lra.
    rewrite Hddf. unfold Kc. field. lra.
Qed.

End Fixed.

(* The sharp interpolation-error bound with the genuine 1/8 constant. *)
Theorem tight_curvature_bound :
  forall (M2 : R),
    (forall x, a <= x <= b -> Rabs (ddf x) <= M2) ->
    forall t, a < t < b ->
      Rabs (sigma t - Lin t) <= M2 * (b - a) * (b - a) / 8.
Proof.
  intros M2 HM2 t Ht.
  destruct (divided_difference_mvt t Ht) as [zeta [Hz Heq]].
  rewrite Heq.
  (* |ddf zeta / 2 * ((t-a)(t-b))| <= M2/2 * (t-a)(b-t) <= M2 (b-a)^2 / 8 *)
  assert (HM2_nonneg : 0 <= M2).
  { apply Rle_trans with (Rabs (ddf zeta)); [apply Rabs_pos |].
    apply HM2. lra. }
  assert (Habs_prod : Rabs ((t - a) * (t - b)) = (t - a) * (b - t)).
  { rewrite Rabs_mult.
    rewrite (Rabs_right (t - a)) by lra.
    rewrite (Rabs_left1 (t - b)) by lra. ring. }
  rewrite Rabs_mult.
  assert (Hd2 : Rabs (ddf zeta / 2) <= M2 / 2).
  { unfold Rdiv. rewrite Rabs_mult.
    rewrite (Rabs_right (/ 2)) by lra.
    apply Rmult_le_compat_r; [lra |]. apply HM2. lra. }
  rewrite Habs_prod.
  apply Rle_trans with (M2 / 2 * ((t - a) * (b - t))).
  - apply Rmult_le_compat.
    + apply Rabs_pos.
    + rewrite <- Habs_prod. apply Rabs_pos.
    + exact Hd2.
    + apply Rle_refl.
  - pose proof (interval_product_max a b t (conj (proj1 (conj (Rlt_le _ _ (proj1 Ht)) (Rlt_le _ _ (proj2 Ht)))) (Rlt_le _ _ (proj2 Ht))) (Rlt_le _ _ Hab)) as Hmax.
    nra.
Qed.

End TightCurvature.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions rolle_is_derive.
Print Assumptions interval_product_max.
Print Assumptions divided_difference_mvt.
Print Assumptions tight_curvature_bound.
