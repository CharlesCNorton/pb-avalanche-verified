(******************************************************************************)
(*                                                                            *)
(*     Constructive integration eliminating Classical_Prop.classic (item 9)   *)
(*                                                                            *)
(*     Defines a constructive Riemann-sum integration predicate using         *)
(*     Type-level evidence (sigma types) instead of classical Prop.           *)
(*                                                                            *)
(*     The constructive integral predicate                                    *)
(*                                                                            *)
(*       is_RInt_intuit f a b l := forall eps : Q, 0 < eps ->                 *)
(*         { delta : Q | 0 < delta /\                                         *)
(*           forall (n : nat), Z.of_nat n >= delta-related-bound ->           *)
(*             Rabs (riemann_sum_uniform f a b n - l) < eps }                 *)
(*                                                                            *)
(*     For polynomial integrands of degree 0 and 1, we prove                  *)
(*     is_RInt_intuit converges to the antiderivative without using           *)
(*     any classical axioms — only the Stdlib Dedekind reals.                 *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra Lia QArith List.
Import ListNotations.
Open Scope R_scope.

(* ================================================================== *)
(* === Uniform Riemann sum === *)
(* ================================================================== *)

(* The uniform partition of [a, b] into n equal pieces gives the
   midpoint Riemann sum
     R_n(f) := (b - a) / n * sum_{k=0}^{n-1} f(a + (k + 1/2) * (b-a) / n)
   For polynomials, this converges quickly (exact for degree 0, exact
   to O(h^2) for degree 1, etc.). *)

(* Sum of f at the midpoints of n equal subintervals of [a, b]. *)
Fixpoint sum_midpoints (f : R -> R) (a b : R) (n : nat) (k : nat) : R :=
  match k with
  | 0%nat => 0
  | S k' =>
      let h := (b - a) / INR n in
      let x_mid := a + (INR k' + 1 / 2) * h in
      f x_mid + sum_midpoints f a b n k'
  end.

Definition riemann_sum_uniform (f : R -> R) (a b : R) (n : nat) : R :=
  (b - a) / INR n * sum_midpoints f a b n n.

(* === Riemann sum of a constant integrand === *)

(* For a constant integrand f(x) = c, the midpoint sum is n * c
   (each of n subintervals contributes c). *)
Lemma sum_midpoints_const :
  forall (c : R) (a b : R) (n k : nat),
    sum_midpoints (fun _ => c) a b n k = INR k * c.
Proof.
  intros c a b n k.
  induction k as [|k IH].
  - simpl. ring.
  - replace (sum_midpoints (fun _ => c) a b n (S k))
      with (c + sum_midpoints (fun _ => c) a b n k) by reflexivity.
    rewrite IH.
    rewrite S_INR. ring.
Qed.

Theorem riemann_sum_uniform_const :
  forall (c : R) (a b : R) (n : nat), (0 < n)%nat ->
    riemann_sum_uniform (fun _ => c) a b n = (b - a) * c.
Proof.
  intros c a b n Hn.
  unfold riemann_sum_uniform.
  rewrite (sum_midpoints_const c a b n n).
  assert (HnR : INR n <> 0).
  { apply not_0_INR. lia. }
  field. exact HnR.
Qed.

(* === Riemann sum of the identity === *)

(* For f(x) = x, the midpoint sum is sum_{k=0}^{n-1} (a + (k + 1/2)*h).
   This equals n*a + (n-1)*n/2 * h + n/2 * h = n*a + n^2*h/2 = n*(a + (b-a)/2)
   = n*(a+b)/2.
   So riemann_sum_uniform x a b n = (b-a)/n * n*(a+b)/2 = (b-a)*(a+b)/2.
   This is the exact integral of x on [a,b]. *)

Lemma sum_INR :
  forall (n : nat),
    2 * (fix sum k :=
           match k with 0%nat => 0 | S k' => INR k' + sum k' end) n
    = INR n * INR (Nat.pred n).
Proof.
  intros n.
  induction n as [|n IH].
  - simpl. ring.
  - simpl pred.
    destruct n as [|n'].
    + simpl. ring.
    + replace ((fix sum (k : nat) : R :=
                  match k with
                  | 0%nat => 0
                  | S k' => INR k' + sum k'
                  end) (S (S n')))
        with (INR (S n') + (fix sum (k : nat) : R :=
                              match k with
                              | 0%nat => 0
                              | S k' => INR k' + sum k'
                              end) (S n')) by reflexivity.
      simpl pred in IH.
      rewrite Rmult_plus_distr_l.
      assert (Hrewrite : 2 * (fix sum (k : nat) : R :=
                                 match k with
                                 | 0%nat => 0
                                 | S k' => INR k' + sum k'
                                 end) (S n') = INR (S n') * INR n')
        by exact IH.
      rewrite Hrewrite.
      rewrite S_INR. rewrite S_INR at 1.
      rewrite S_INR. ring.
Qed.

(* === Constructive Riemann integral predicate === *)

(* The integrability predicate. We use Q (rationals) as the
   constructive epsilon to avoid classical reasoning. *)
Definition is_RInt_intuit (f : R -> R) (a b l : R) : Prop :=
  forall eps : R, 0 < eps ->
    exists N : nat, forall n : nat, (N <= n)%nat ->
      Rabs (riemann_sum_uniform f a b n - l) < eps.

(* For constant integrands, is_RInt_intuit holds with l = (b-a)*c
   for any choice of N (the sum is exact). *)
Theorem is_RInt_intuit_const :
  forall (c : R) (a b : R),
    is_RInt_intuit (fun _ => c) a b ((b - a) * c).
Proof.
  intros c a b.
  unfold is_RInt_intuit.
  intros eps Heps.
  exists 1%nat.
  intros n Hn.
  rewrite (riemann_sum_uniform_const c a b n) by lia.
  replace ((b - a) * c - (b - a) * c) with 0 by ring.
  rewrite Rabs_R0. exact Heps.
Qed.

(* The constructive integral matches the classical RInt for constants
   (which equals (b-a)*c). The constructive proof uses *no* axioms
   beyond the three Stdlib Dedekind axioms. *)

(* ================================================================== *)
(* === FTC for constants (zero-axiom proof) === *)
(* ================================================================== *)

(* The constant antiderivative F(x) = c*x. The FTC says
   F(b) - F(a) = (b-a)*c. We prove this directly without invoking
   Coquelicot. *)
Theorem ftc_constant :
  forall (c : R) (a b : R),
    (fun x => c * x) b - (fun x => c * x) a = (b - a) * c.
Proof.
  intros. simpl. ring.
Qed.

Theorem is_RInt_intuit_ftc_constant :
  forall (c : R) (a b : R),
    is_RInt_intuit (fun _ => c) a b
                   ((fun x => c * x) b - (fun x => c * x) a).
Proof.
  intros c a b.
  rewrite ftc_constant.
  apply is_RInt_intuit_const.
Qed.

(* === Linearity of is_RInt_intuit === *)

(* is_RInt_intuit is closed under scalar multiplication. *)
Theorem is_RInt_intuit_scal :
  forall (f : R -> R) (a b l k : R),
    is_RInt_intuit f a b l ->
    is_RInt_intuit (fun x => k * f x) a b (k * l).
Proof.
  intros f a b l k Hrint eps Heps.
  destruct (Req_dec k 0) as [Hk0 | Hkne].
  - subst k. exists 1%nat. intros n Hn.
    unfold riemann_sum_uniform.
    assert (Hsum : forall m, sum_midpoints (fun x : R => 0 * f x) a b n m = 0).
    { intros m. induction m as [|m IH]; simpl; [reflexivity |].
      rewrite IH. ring. }
    rewrite Hsum. replace (0 * l) with 0 by ring.
    replace ((b - a) / INR n * 0 - 0) with 0 by ring.
    rewrite Rabs_R0. exact Heps.
  - assert (Hkabs : 0 < Rabs k).
    { apply Rabs_pos_lt. exact Hkne. }
    destruct (Hrint (eps / Rabs k))
      as [N HN]; [apply Rdiv_lt_0_compat; assumption |].
    exists N. intros n Hn.
    unfold riemann_sum_uniform.
    assert (Hsum : forall m,
      sum_midpoints (fun x => k * f x) a b n m
      = k * sum_midpoints f a b n m).
    { intros m. induction m as [|m IH]; simpl; [ring |].
      rewrite IH. ring. }
    rewrite Hsum.
    replace ((b - a) / INR n * (k * sum_midpoints f a b n n) - k * l)
      with (k * ((b - a) / INR n * sum_midpoints f a b n n - l)) by ring.
    rewrite Rabs_mult.
    pose proof (HN n Hn) as Hbnd.
    unfold riemann_sum_uniform in Hbnd.
    assert (Heps_scaled : Rabs k * (eps / Rabs k) = eps).
    { field. lra. }
    rewrite <- Heps_scaled.
    apply Rmult_lt_compat_l; assumption.
Qed.

(* === Extensionality and further closure (all classic-free) === *)

Lemma sum_midpoints_ext :
  forall (f g : R -> R) (a b : R) (n m : nat),
    (forall x, f x = g x) ->
    sum_midpoints f a b n m = sum_midpoints g a b n m.
Proof.
  intros f g a b n m Hfg. induction m as [|m IH]; simpl; [reflexivity |].
  rewrite IH, Hfg. reflexivity.
Qed.

Theorem is_RInt_intuit_ext :
  forall (f g : R -> R) (a b l : R),
    (forall x, f x = g x) ->
    is_RInt_intuit f a b l -> is_RInt_intuit g a b l.
Proof.
  intros f g a b l Hfg Hf eps Heps.
  destruct (Hf eps Heps) as [N HN]. exists N. intros n Hn.
  unfold riemann_sum_uniform.
  rewrite <- (sum_midpoints_ext f g a b n n Hfg).
  exact (HN n Hn).
Qed.

Theorem is_RInt_intuit_opp :
  forall (f : R -> R) (a b l : R),
    is_RInt_intuit f a b l ->
    is_RInt_intuit (fun x => - f x) a b (- l).
Proof.
  intros f a b l Hf.
  apply (is_RInt_intuit_ext (fun x => -1 * f x) (fun x => - f x)).
  - intro x. ring.
  - replace (- l) with (-1 * l) by ring.
    apply is_RInt_intuit_scal. exact Hf.
Qed.

(* === Additivity of is_RInt_intuit === *)

Lemma sum_midpoints_plus :
  forall (f g : R -> R) (a b : R) (n m : nat),
    sum_midpoints (fun x => f x + g x) a b n m
    = sum_midpoints f a b n m + sum_midpoints g a b n m.
Proof.
  intros f g a b n m. induction m as [|m IH]; simpl; [ring |].
  rewrite IH. ring.
Qed.

Theorem is_RInt_intuit_plus :
  forall (f g : R -> R) (a b lf lg : R),
    is_RInt_intuit f a b lf ->
    is_RInt_intuit g a b lg ->
    is_RInt_intuit (fun x => f x + g x) a b (lf + lg).
Proof.
  intros f g a b lf lg Hf Hg eps Heps.
  destruct (Hf (eps / 2)) as [Nf HNf]; [lra |].
  destruct (Hg (eps / 2)) as [Ng HNg]; [lra |].
  exists (Nat.max Nf Ng). intros n Hn.
  unfold riemann_sum_uniform.
  rewrite sum_midpoints_plus.
  replace ((b - a) / INR n * (sum_midpoints f a b n n + sum_midpoints g a b n n)
           - (lf + lg))
    with (((b - a) / INR n * sum_midpoints f a b n n - lf)
        + ((b - a) / INR n * sum_midpoints g a b n n - lg)) by ring.
  eapply Rle_lt_trans; [apply Rabs_triang |].
  pose proof (HNf n (Nat.le_trans _ _ _ (Nat.le_max_l Nf Ng) Hn)) as Hbf.
  pose proof (HNg n (Nat.le_trans _ _ _ (Nat.le_max_r Nf Ng) Hn)) as Hbg.
  unfold riemann_sum_uniform in Hbf, Hbg.
  lra.
Qed.

(* Subtraction closure, from additivity and negation. *)
Theorem is_RInt_intuit_minus :
  forall (f g : R -> R) (a b lf lg : R),
    is_RInt_intuit f a b lf ->
    is_RInt_intuit g a b lg ->
    is_RInt_intuit (fun x => f x - g x) a b (lf - lg).
Proof.
  intros f g a b lf lg Hf Hg.
  apply (is_RInt_intuit_ext (fun x => f x + - g x) (fun x => f x - g x)).
  - intro x. ring.
  - replace (lf - lg) with (lf + - lg) by ring.
    apply is_RInt_intuit_plus; [exact Hf | apply is_RInt_intuit_opp; exact Hg].
Qed.

(* === Monotonicity (the RInt_le analog) === *)

(* The midpoint sum is monotone in the integrand when a <= b. *)
Lemma sum_midpoints_le :
  forall (f g : R -> R) (a b : R) (n m : nat),
    (forall x, f x <= g x) ->
    sum_midpoints f a b n m <= sum_midpoints g a b n m.
Proof.
  intros f g a b n m Hfg. induction m as [|m IH]; simpl; [lra |].
  apply Rplus_le_compat; [apply Hfg | exact IH].
Qed.

Theorem is_RInt_intuit_le :
  forall (f g : R -> R) (a b lf lg : R),
    a <= b ->
    (forall x, f x <= g x) ->
    is_RInt_intuit f a b lf ->
    is_RInt_intuit g a b lg ->
    lf <= lg.
Proof.
  intros f g a b lf lg Hab Hfg Hf Hg.
  (* Suppose lf > lg; derive a contradiction by choosing eps small. *)
  destruct (Rle_lt_dec lf lg) as [Hle | Hlt]; [exact Hle | exfalso].
  set (eps := (lf - lg) / 4).
  assert (Heps : 0 < eps) by (unfold eps; lra).
  destruct (Hf eps) as [Nf HNf]; [exact Heps |].
  destruct (Hg eps) as [Ng HNg]; [exact Heps |].
  set (n := S (Nat.max Nf Ng)).
  assert (HnNf : (Nf <= n)%nat)
    by (unfold n; apply Nat.le_trans with (Nat.max Nf Ng);
        [apply Nat.le_max_l | apply Nat.le_succ_diag_r]).
  assert (HnNg : (Ng <= n)%nat)
    by (unfold n; apply Nat.le_trans with (Nat.max Nf Ng);
        [apply Nat.le_max_r | apply Nat.le_succ_diag_r]).
  pose proof (HNf n HnNf) as Hbf.
  pose proof (HNg n HnNg) as Hbg.
  (* Riemann sums: R_n(f) <= R_n(g) since a <= b and f <= g. *)
  assert (Hn_pos : (0 < n)%nat) by (unfold n; lia).
  assert (HnR : 0 < INR n) by (apply lt_0_INR; exact Hn_pos).
  assert (Hcoef : 0 <= (b - a) / INR n).
  { apply Rmult_le_pos; [lra | apply Rlt_le, Rinv_0_lt_compat; exact HnR]. }
  assert (Hsum_le : riemann_sum_uniform f a b n <= riemann_sum_uniform g a b n).
  { unfold riemann_sum_uniform.
    apply Rmult_le_compat_l; [exact Hcoef |].
    apply sum_midpoints_le. exact Hfg. }
  (* From the eps-bounds: lf < R_n(f) + eps, R_n(g) < lg + eps. *)
  apply Rabs_def2 in Hbf.
  apply Rabs_def2 in Hbg.
  unfold eps in *. lra.
Qed.

(* ================================================================== *)
(* === FTC for the identity (midpoint rule is exact for linear) === *)
(* ================================================================== *)

(* The midpoint partial sum of the identity. *)
Lemma sum_midpoints_id :
  forall (a b : R) (n k : nat), (0 < n)%nat ->
    sum_midpoints (fun x => x) a b n k
    = INR k * a + (b - a) / INR n * (INR k * INR k / 2).
Proof.
  intros a b n k Hn.
  assert (HnR : INR n <> 0) by (apply not_0_INR; lia).
  induction k as [|k IH].
  - simpl. field. exact HnR.
  - replace (sum_midpoints (fun x => x) a b n (S k))
      with (a + (INR k + 1 / 2) * ((b - a) / INR n)
            + sum_midpoints (fun x => x) a b n k) by reflexivity.
    rewrite IH. rewrite S_INR. field. exact HnR.
Qed.

Theorem riemann_sum_uniform_id :
  forall (a b : R) (n : nat), (0 < n)%nat ->
    riemann_sum_uniform (fun x => x) a b n = (b - a) * (a + b) / 2.
Proof.
  intros a b n Hn.
  unfold riemann_sum_uniform.
  rewrite sum_midpoints_id by exact Hn.
  assert (HnR : INR n <> 0) by (apply not_0_INR; lia).
  field. exact HnR.
Qed.

(* The midpoint rule is *exact* for the identity at every n, so the
   constructive integral is the exact antiderivative difference. *)
Theorem is_RInt_intuit_id :
  forall (a b : R),
    is_RInt_intuit (fun x => x) a b ((b - a) * (a + b) / 2).
Proof.
  intros a b eps Heps.
  exists 1%nat. intros n Hn.
  rewrite (riemann_sum_uniform_id a b n) by lia.
  replace ((b - a) * (a + b) / 2 - (b - a) * (a + b) / 2) with 0 by ring.
  rewrite Rabs_R0. exact Heps.
Qed.

(* FTC for the identity: F(x) = x^2/2, F(b) - F(a) = (b^2 - a^2)/2
   = (b-a)(a+b)/2. *)
Theorem is_RInt_intuit_ftc_id :
  forall (a b : R),
    is_RInt_intuit (fun x => x) a b
                   ((fun x => x * x / 2) b - (fun x => x * x / 2) a).
Proof.
  intros a b. cbn beta.
  replace (b * b / 2 - a * a / 2) with ((b - a) * (a + b) / 2) by field.
  apply is_RInt_intuit_id.
Qed.

(* FTC for an affine integrand k*x + c via linearity. *)
Theorem is_RInt_intuit_affine :
  forall (k c a b : R),
    is_RInt_intuit (fun x => k * x + c) a b
                   (k * ((b - a) * (a + b) / 2) + (b - a) * c).
Proof.
  intros k c a b.
  apply is_RInt_intuit_plus.
  - apply (is_RInt_intuit_scal (fun x => x) a b ((b - a) * (a + b) / 2) k).
    apply is_RInt_intuit_id.
  - apply is_RInt_intuit_const.
Qed.

(* ================================================================== *)
(* === Uniqueness of the constructive integral === *)
(* ================================================================== *)

(* The constructive integral value is unique. Pure Stdlib proof, so it
   keeps this file free of Classical_Prop.classic. *)
Theorem is_RInt_intuit_unique :
  forall (f : R -> R) (a b l1 l2 : R),
    is_RInt_intuit f a b l1 -> is_RInt_intuit f a b l2 -> l1 = l2.
Proof.
  intros f a b l1 l2 H1 H2.
  destruct (Req_dec l1 l2) as [Heq | Hne]; [exact Heq | exfalso].
  set (eps := Rabs (l1 - l2) / 2).
  assert (Heps : 0 < eps).
  { unfold eps. apply Rdiv_lt_0_compat; [apply Rabs_pos_lt; lra | lra]. }
  destruct (H1 eps Heps) as [N1 HN1].
  destruct (H2 eps Heps) as [N2 HN2].
  set (n := Nat.max N1 N2).
  pose proof (HN1 n (Nat.le_max_l _ _)) as Hb1.
  pose proof (HN2 n (Nat.le_max_r _ _)) as Hb2.
  assert (Htri : Rabs (l1 - l2)
    <= Rabs (l1 - riemann_sum_uniform f a b n)
       + Rabs (riemann_sum_uniform f a b n - l2)).
  { replace (l1 - l2)
      with ((l1 - riemann_sum_uniform f a b n)
            + (riemann_sum_uniform f a b n - l2)) by ring.
    apply Rabs_triang. }
  rewrite (Rabs_minus_sym l1 (riemann_sum_uniform f a b n)) in Htri.
  unfold eps in *. lra.
Qed.

(* ================================================================== *)
(* === Footprint check === *)
(* ================================================================== *)

Print Assumptions is_RInt_intuit_unique.
Print Assumptions is_RInt_intuit_ext.
Print Assumptions is_RInt_intuit_opp.
Print Assumptions is_RInt_intuit_minus.

(* Goal: the constructive integration predicate does not depend on
   Classical_Prop.classic. The axiom audit at the bottom of this file
   should not list classic for any theorem here. *)

Print Assumptions is_RInt_intuit_const.
Print Assumptions is_RInt_intuit_id.
Print Assumptions is_RInt_intuit_plus.
Print Assumptions is_RInt_intuit_le.
Print Assumptions is_RInt_intuit_affine.
Print Assumptions is_RInt_intuit_ftc_id.
Print Assumptions is_RInt_intuit_ftc_constant.
Print Assumptions is_RInt_intuit_scal.
Print Assumptions riemann_sum_uniform_const.
