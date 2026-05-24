(******************************************************************************)
(*                                                                            *)
(*     Cubic Hermite spline interpolation and tight curvature error           *)
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
From Coquelicot Require Import Coquelicot.
From PBAvalanche Require Import pb_avalanche_iaea.
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
(* === Tight curvature and trapezoidal-panel error bounds === *)
(* ================================================================== *)

(* The deferred O(h^4) bound above rests on a divided-difference mean
   value theorem; that machinery, the sharp 1/8 interpolation-curvature
   constant wired into the IAEA segment error, and the tight 1/12
   trapezoidal-panel error for C^2 integrands are developed here. *)

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

(* The sharp interpolation-error bound with the 1/8 constant. *)
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

(* The sharp 1/8 interpolation-error bound applied to the IAEA
   piecewise-linear segment interpolant. *)
Theorem interp_segment_curvature_error_sharp :
  forall (sigma df ddf : R -> R) (a b M2 : R),
    a < b ->
    0 <= M2 ->
    (forall x, a <= x <= b -> is_derive sigma x (df x)) ->
    (forall x, a <= x <= b -> is_derive df x (ddf x)) ->
    (forall x, a <= x <= b -> Rabs (ddf x) <= M2) ->
    forall t, a <= t <= b ->
      Rabs (sigma t - interp_segment a (sigma a) b (sigma b) t)
        <= M2 * (b - a) * (b - a) / 8.
Proof.
  intros sigma df ddf a b M2 Hab HM2 Hd1 Hd2 Hbnd t Ht.
  assert (Hlin : interp_segment a (sigma a) b (sigma b) t = Lin sigma a b t).
  { unfold interp_segment, Lin, slope. field. lra. }
  rewrite Hlin.
  assert (Hpos : 0 <= M2 * (b - a) * (b - a) / 8).
  { repeat apply Rmult_le_pos; lra. }
  destruct (Rle_lt_dec t a) as [Hta | Hta].
  - assert (Hte : t = a) by lra. subst t.
    unfold Lin, slope. replace (sigma a - (sigma a + _ * (a - a))) with 0 by ring.
    rewrite Rabs_R0. exact Hpos.
  - destruct (Rle_lt_dec b t) as [Htb | Htb].
    + assert (Hte : t = b) by lra. subst t.
      unfold Lin, slope.
      replace (sigma b - (sigma a + (sigma b - sigma a) / (b - a) * (b - a)))
        with 0 by (field; lra).
      rewrite Rabs_R0. exact Hpos.
    + apply (tight_curvature_bound sigma df ddf a b Hab Hd1 Hd2 M2 Hbnd t).
      split; assumption.
Qed.

(* ================================================================== *)
(* === General trapezoidal (Euler-Maclaurin order 2) error === *)
(* ================================================================== *)

Lemma RInt_parabola : forall a b, a <= b ->
  RInt (fun t => (t - a) * (b - t)) a b = (b - a)^3 / 6.
Proof.
  intros a b Hab.
  apply is_RInt_unique.
  replace ((b - a)^3 / 6)
    with ((- b^3/3 + (a+b)*b^2/2 - a*b*b) - (- a^3/3 + (a+b)*a^2/2 - a*b*a))
    by (simpl; field).
  apply (is_RInt_derive
           (fun t => - t^3/3 + (a+b)*t^2/2 - a*b*t)
           (fun t => (t - a) * (b - t)) a b).
  - intros x _. auto_derive. trivial. nra.
  - intros x _.
    apply (continuous_mult (fun t => t - a) (fun t => b - t));
      [ apply (continuous_minus (V:=R_NormedModule) (fun t => t) (fun _ => a));
          [apply continuous_id | apply continuous_const]
      | apply (continuous_minus (V:=R_NormedModule) (fun _ => b) (fun t => t));
          [apply continuous_const | apply continuous_id] ].
Qed.

(* RInt bridge helpers *)
Lemma RInt_scal_R : forall (f : R -> R) (a b k : R),
  ex_RInt f a b -> RInt (fun x => k * f x) a b = k * RInt f a b.
Proof.
  intros f a b k Hf. pose proof (RInt_scal f a b k Hf) as H.
  unfold scal in H; simpl in H; unfold mult in H; simpl in H. exact H.
Qed.

Lemma RInt_minus_R : forall (f g : R -> R) (a b : R),
  ex_RInt f a b -> ex_RInt g a b ->
  RInt (fun x => f x - g x) a b = RInt f a b - RInt g a b.
Proof.
  intros f g a b Hf Hg. pose proof (RInt_minus f g a b Hf Hg) as H.
  unfold minus in H; simpl in H; unfold plus, opp in H; simpl in H. exact H.
Qed.

Section T3.
Variables sigma df ddf : R -> R.
Variables a b M2 : R.
Hypothesis Hab : a < b.
Hypothesis HM2 : 0 <= M2.
Hypothesis Hd1 : forall x, a <= x <= b -> is_derive sigma x (df x).
Hypothesis Hd2 : forall x, a <= x <= b -> is_derive df x (ddf x).
Hypothesis Hbnd : forall x, a <= x <= b -> Rabs (ddf x) <= M2.

Lemma sigma_cont : forall x, a <= x <= b -> continuous sigma x.
Proof. intros x Hx. apply (ex_derive_continuous (K:=R_AbsRing)(V:=R_NormedModule)).
  exists (df x). apply Hd1; exact Hx. Qed.

Lemma interp_pointwise_bound :
  forall t, a <= t <= b ->
    Rabs (sigma t - Lin sigma a b t) <= M2 / 2 * ((t - a) * (b - t)).
Proof.
  intros t Ht.
  destruct (Rle_lt_dec t a) as [Hta|Hta].
  - assert (t = a) by lra; subst t.
    unfold Lin, slope. replace (sigma a - (sigma a + _ * (a - a))) with 0 by ring.
    rewrite Rabs_R0. replace (a - a) with 0 by ring. rewrite Rmult_0_l, Rmult_0_r. lra.
  - destruct (Rle_lt_dec b t) as [Htb|Htb].
    + assert (t = b) by lra; subst t.
      unfold Lin, slope.
      replace (sigma b - (sigma a + (sigma b - sigma a)/(b-a)*(b-a))) with 0 by (field; lra).
      rewrite Rabs_R0. replace (b - b) with 0 by ring. rewrite Rmult_0_r, Rmult_0_r. lra.
    + destruct (divided_difference_mvt sigma df ddf a b Hab Hd1 Hd2 t (conj Hta Htb))
        as [zeta [Hz Heq]].
      rewrite Heq.
      rewrite Rabs_mult.
      assert (Hpar : Rabs ((t - a) * (t - b)) = (t - a) * (b - t)).
      { rewrite Rabs_mult. rewrite (Rabs_right (t-a)) by lra.
        rewrite (Rabs_left1 (t-b)) by lra. ring. }
      rewrite Hpar.
      apply Rmult_le_compat_r; [ nra |].
      unfold Rdiv. rewrite Rabs_mult. rewrite (Rabs_right (/2)) by lra.
      apply Rmult_le_compat_r; [lra|]. apply Hbnd. lra.
Qed.
End T3.

Lemma Lin_continuous : forall sigma a b x, continuous (Lin sigma a b) x.
Proof.
  intros sigma a b x. unfold Lin.
  apply (continuous_plus (V:=R_NormedModule) (fun _ => sigma a)
           (fun t => slope sigma a b * (t - a)));
    [apply continuous_const
    | apply (continuous_mult (fun _ => slope sigma a b) (fun t => t - a));
       [apply continuous_const
       | apply (continuous_minus (V:=R_NormedModule) (fun t => t) (fun _ => a));
          [apply continuous_id | apply continuous_const]]].
Qed.

Lemma RInt_Lin : forall sigma a b, a < b ->
  RInt (Lin sigma a b) a b = (b - a) * (sigma a + sigma b) / 2.
Proof.
  intros sigma a b Hab.
  apply is_RInt_unique.
  replace ((b - a) * (sigma a + sigma b) / 2)
    with ((sigma a * b + slope sigma a b * (b - a)^2 / 2)
          - (sigma a * a + slope sigma a b * (a - a)^2 / 2))
    by (unfold slope; field; lra).
  apply (is_RInt_derive
           (fun t => sigma a * t + slope sigma a b * (t - a)^2 / 2)
           (Lin sigma a b) a b).
  - intros x _. unfold Lin. auto_derive. trivial. nra.
  - intros x _. apply Lin_continuous.
Qed.

Lemma ex_RInt_minus_R : forall (f g : R -> R) (a b : R),
  ex_RInt f a b -> ex_RInt g a b -> ex_RInt (fun x => f x - g x) a b.
Proof. intros f g a b Hf Hg. exact (ex_RInt_minus f g a b Hf Hg). Qed.

Lemma cont_parabola : forall a b x, continuous (fun x => (x - a) * (b - x)) x.
Proof.
  intros a b x.
  apply (continuous_mult (fun x => x-a) (fun x => b-x));
    [apply (continuous_minus (V:=R_NormedModule) (fun t=>t)(fun _=>a));
       [apply continuous_id|apply continuous_const]
    |apply (continuous_minus (V:=R_NormedModule) (fun _=>b)(fun t=>t));
       [apply continuous_const|apply continuous_id]].
Qed.

Theorem trapezoidal_panel_error :
  forall sigma df ddf a b M2, a < b -> 0 <= M2 ->
    (forall x, a <= x <= b -> is_derive sigma x (df x)) ->
    (forall x, a <= x <= b -> is_derive df x (ddf x)) ->
    (forall x, a <= x <= b -> Rabs (ddf x) <= M2) ->
    Rabs (RInt sigma a b - (b - a) * (sigma a + sigma b) / 2)
      <= M2 * (b - a)^3 / 12.
Proof.
  intros sigma df ddf a b M2 Hab HM2 Hd1 Hd2 Hbnd.
  assert (Hexs : ex_RInt sigma a b).
  { apply (ex_RInt_continuous (V:=R_CompleteNormedModule)). intros x Hx.
    rewrite Rmin_left in Hx by lra. rewrite Rmax_right in Hx by lra.
    apply (sigma_cont sigma df a b Hd1 x Hx). }
  assert (HexL : ex_RInt (Lin sigma a b) a b).
  { apply (ex_RInt_continuous (V:=R_CompleteNormedModule)). intros x _.
    apply Lin_continuous. }
  rewrite <- (RInt_Lin sigma a b Hab).
  rewrite <- (RInt_minus_R sigma (Lin sigma a b) a b Hexs HexL).
  assert (Hexd : ex_RInt (fun x => sigma x - Lin sigma a b x) a b)
    by (apply ex_RInt_minus_R; assumption).
  eapply Rle_trans;
    [apply (abs_RInt_le (fun x => sigma x - Lin sigma a b x) a b
              (Rlt_le _ _ Hab) Hexd) |].
  assert (HexAbs : ex_RInt (fun x => Rabs (sigma x - Lin sigma a b x)) a b).
  { apply (ex_RInt_continuous (V:=R_CompleteNormedModule)). intros x Hx.
    rewrite Rmin_left in Hx by lra. rewrite Rmax_right in Hx by lra.
    apply (continuous_comp (fun x => sigma x - Lin sigma a b x) Rabs).
    - apply (continuous_minus (V:=R_NormedModule) sigma (Lin sigma a b)).
      + apply (sigma_cont sigma df a b Hd1 x Hx).
      + apply Lin_continuous.
    - apply continuous_Rabs. }
  assert (HexPar : ex_RInt (fun x => M2 / 2 * ((x - a) * (b - x))) a b).
  { apply (ex_RInt_continuous (V:=R_CompleteNormedModule)). intros x _.
    apply (continuous_mult (fun _ => M2/2) (fun x => (x-a)*(b-x)));
      [apply continuous_const | apply cont_parabola]. }
  eapply Rle_trans;
    [apply (RInt_le (fun x => Rabs (sigma x - Lin sigma a b x))
              (fun x => M2 / 2 * ((x - a) * (b - x))) a b (Rlt_le _ _ Hab)
              HexAbs HexPar) |].
  - intros x Hx.
    apply (interp_pointwise_bound sigma df ddf a b M2 Hab Hd1 Hd2 Hbnd x). lra.
  - rewrite (RInt_scal_R (fun x => (x - a) * (b - x)) a b (M2/2)).
    + rewrite (RInt_parabola a b (Rlt_le _ _ Hab)). lra.
    + apply (ex_RInt_continuous (V:=R_CompleteNormedModule)). intros x _.
      apply cont_parabola.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions hermite_cubic_at_left.
Print Assumptions hermite_cubic_at_right.
Print Assumptions hermite_cubic_linear_case.
Print Assumptions rolle_is_derive.
Print Assumptions interp_segment_curvature_error_sharp.
Print Assumptions RInt_parabola.
Print Assumptions trapezoidal_panel_error.
Print Assumptions interval_product_max.
Print Assumptions divided_difference_mvt.
Print Assumptions tight_curvature_bound.
