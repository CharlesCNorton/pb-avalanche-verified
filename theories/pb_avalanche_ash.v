(******************************************************************************)
(*                                                                            *)
(*     Helium-ash transport with Z_eff raising                                *)
(*                                                                            *)
(*     Extends the plasma state with an ash density n_ash (thermalised        *)
(*     helium nuclei) and redoes the Spitzer slowing-down time with the       *)
(*     ion-scattering Z_eff denominator                                       *)
(*                                                                            *)
(*       n_eff = n_p + Z_B^2 n_B + Z_alpha^2 n_ash.                           *)
(*                                                                            *)
(*     Ash accumulation raises n_eff, shortens tau_slow_alpha, and so         *)
(*     reduces the multiplication factor — a formal self-quenching            *)
(*     mechanism.                                                             *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra ZArith.
From Coquelicot Require Import Coquelicot.
From PBAvalanche Require Import pb_avalanche.

Open Scope R_scope.

(* ================================================================== *)
(* === Ash-extended plasma state === *)
(* ================================================================== *)

(* Helium-ash density. *)

(* Alpha-particle nuclear charge (Z_alpha = 2 for helium-4). *)
Definition Z_alpha : R := 2.

Record PlasmaStateAsh : Type := mkPlasmaStateAsh {
  psa_n_p   : R;
  psa_n_B   : R;
  psa_n_ash : R;
  psa_T     : R;
  psa_B     : R;
  psa_pos_n_p   : 0 < psa_n_p;
  psa_pos_n_B   : 0 < psa_n_B;
  psa_pos_n_ash : 0 <= psa_n_ash;  (* ash can be zero initially *)
  psa_pos_T     : 0 < psa_T;
  psa_pos_B     : 0 < psa_B;
}.

(* The effective ion-scattering density including ash contribution. *)
Definition n_eff_with_ash (s : PlasmaStateAsh) : R :=
  psa_n_p s + Z_B * Z_B * psa_n_B s + Z_alpha * Z_alpha * psa_n_ash s.

Lemma n_eff_with_ash_pos :
  forall s, 0 < n_eff_with_ash s.
Proof.
  intros s. unfold n_eff_with_ash.
  pose proof (psa_pos_n_p s) as Hp.
  pose proof (psa_pos_n_B s) as HB.
  pose proof (psa_pos_n_ash s) as Hash.
  assert (HZB : 0 < Z_B * Z_B * psa_n_B s).
  { apply Rmult_lt_0_compat;
      [apply Rmult_lt_0_compat; unfold Z_B; lra | exact HB]. }
  assert (HZa : 0 <= Z_alpha * Z_alpha * psa_n_ash s).
  { apply Rmult_le_pos; [unfold Z_alpha; lra | exact Hash]. }
  lra.
Qed.

(* The Spitzer slowing-down time with ash correction. *)
Definition tau_slow_alpha_ash (Cspitzer : R) (s : PlasmaStateAsh) : R :=
  Cspitzer * psa_T s * sqrt (psa_T s) / n_eff_with_ash s.

Lemma tau_slow_alpha_ash_pos :
  forall Cspitzer s, 0 < Cspitzer ->
    0 < tau_slow_alpha_ash Cspitzer s.
Proof.
  intros Cspitzer s HC. unfold tau_slow_alpha_ash.
  pose proof (n_eff_with_ash_pos s) as Hpos.
  pose proof (psa_pos_T s) as HTpos.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat; assumption.
    + apply sqrt_lt_R0; exact HTpos.
  - apply Rinv_0_lt_compat; exact Hpos.
Qed.

(* ================================================================== *)
(* === Monotonicity in ash density === *)
(* ================================================================== *)

(* tau_slow_alpha_ash is decreasing in psa_n_ash. *)
Theorem tau_slow_alpha_ash_decreasing :
  forall Cspitzer
    (n_p n_B n_ash1 n_ash2 T B : R)
    (Hp_p : 0 < n_p) (Hp_B : 0 < n_B)
    (Hp_a1 : 0 <= n_ash1) (Hp_a2 : 0 <= n_ash2)
    (Hp_T : 0 < T) (Hp_B' : 0 < B),
    0 < Cspitzer ->
    n_ash1 <= n_ash2 ->
    tau_slow_alpha_ash Cspitzer
      (mkPlasmaStateAsh n_p n_B n_ash2 T B Hp_p Hp_B Hp_a2 Hp_T Hp_B') <=
    tau_slow_alpha_ash Cspitzer
      (mkPlasmaStateAsh n_p n_B n_ash1 T B Hp_p Hp_B Hp_a1 Hp_T Hp_B').
Proof.
  intros Cspitzer n_p n_B n_ash1 n_ash2 T B Hp_p Hp_B Hp_a1 Hp_a2 Hp_T Hp_B'
         HC Hash.
  unfold tau_slow_alpha_ash, n_eff_with_ash. simpl.
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos.
    + apply Rmult_le_pos; [apply Rlt_le, HC | apply Rlt_le, Hp_T].
    + apply sqrt_pos.
  - apply Rinv_le_contravar.
    + apply Rplus_lt_le_0_compat.
      * apply Rplus_lt_0_compat; [exact Hp_p |].
        apply Rmult_lt_0_compat; [unfold Z_B; lra | exact Hp_B].
      * apply Rmult_le_pos; [unfold Z_alpha; nra | exact Hp_a1].
    + assert (Hzalpha : 0 <= Z_alpha * Z_alpha)
        by (unfold Z_alpha; nra).
      assert (Hineq : Z_alpha * Z_alpha * n_ash1 <= Z_alpha * Z_alpha * n_ash2)
        by (apply Rmult_le_compat_l; assumption).
      lra.
Qed.

(* ================================================================== *)
(* === Multiplication factor decreases with ash === *)
(* ================================================================== *)

(* Given an "abstract" alpha-weighted velocity integral I (positive)
   and the kinetic factorization M = 3 * n_B * tau * I, the M values
   at two different ash densities (with everything else equal)
   satisfy M(n_ash_high) <= M(n_ash_low). This is the formal
   self-quenching content. *)

Definition M_ash (Cspitzer I : R) (s : PlasmaStateAsh) : R :=
  3 * psa_n_B s * tau_slow_alpha_ash Cspitzer s * I.

Theorem M_ash_decreasing :
  forall Cspitzer I
    (n_p n_B n_ash1 n_ash2 T B : R)
    (Hp_p : 0 < n_p) (Hp_B : 0 < n_B)
    (Hp_a1 : 0 <= n_ash1) (Hp_a2 : 0 <= n_ash2)
    (Hp_T : 0 < T) (Hp_B' : 0 < B),
    0 < Cspitzer -> 0 <= I -> n_ash1 <= n_ash2 ->
    M_ash Cspitzer I
      (mkPlasmaStateAsh n_p n_B n_ash2 T B Hp_p Hp_B Hp_a2 Hp_T Hp_B') <=
    M_ash Cspitzer I
      (mkPlasmaStateAsh n_p n_B n_ash1 T B Hp_p Hp_B Hp_a1 Hp_T Hp_B').
Proof.
  intros Cspitzer I n_p n_B n_ash1 n_ash2 T B Hp_p Hp_B Hp_a1 Hp_a2 Hp_T Hp_B'
         HC HI Hash.
  unfold M_ash. simpl.
  apply Rmult_le_compat_r; [exact HI |].
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos.
    + lra.
    + apply Rlt_le, Hp_B.
  - apply (tau_slow_alpha_ash_decreasing Cspitzer n_p n_B n_ash1 n_ash2 T B
             Hp_p Hp_B Hp_a1 Hp_a2 Hp_T Hp_B'); assumption.
Qed.

(* ================================================================== *)
(* === Picard iteration for the ash ODE === *)
(* ================================================================== *)

Section AshODE.

  Variable R_primary tau_ash : R.
  Hypothesis tau_pos : 0 < tau_ash.

  (* The right-hand side of the ODE: F(y) = R_primary - y / tau_ash. *)
  Definition F_ash (y : R) : R := R_primary - y / tau_ash.

  (* Initial value: n_ash(0) = 0. *)
  Definition y0 : R := 0.

  (* Closed-form solution: y(t) = n_ash_eq * (1 - exp(-t / tau)). *)
  Definition n_ash_eq : R := R_primary * tau_ash.

  Definition n_ash_solution (t : R) : R :=
    n_ash_eq * (1 - exp (- t / tau_ash)).

  Lemma n_ash_solution_at_0 : n_ash_solution 0 = 0.
  Proof.
    unfold n_ash_solution. replace (- 0 / tau_ash) with 0 by lra.
    rewrite exp_0. ring.
  Qed.

  (* The closed-form derivative. *)
  Lemma n_ash_solution_derivative :
    forall t, is_derive n_ash_solution t (R_primary * exp (- t / tau_ash)).
  Proof.
    intros t.
    unfold n_ash_solution, n_ash_eq.
    auto_derive.
    - lra.
    - assert (Htau : tau_ash <> 0) by lra.
      replace (- t / tau_ash) with (- t * / tau_ash) by (unfold Rdiv; reflexivity).
      field. exact Htau.
  Qed.

  (* The closed-form solution satisfies the ODE. *)
  Theorem n_ash_solution_satisfies_ODE :
    forall t,
      is_derive n_ash_solution t (F_ash (n_ash_solution t)).
  Proof.
    intros t.
    pose proof (n_ash_solution_derivative t) as Hd.
    unfold F_ash.
    (* Need to show:
       R_primary * exp (-t/tau_ash)
       = R_primary - n_ash_solution t / tau_ash *)
    assert (Heq : R_primary * exp (- t / tau_ash)
                 = R_primary - n_ash_solution t / tau_ash).
    { unfold n_ash_solution, n_ash_eq. field. lra. }
    rewrite <- Heq. exact Hd.
  Qed.

  (* Asymptotic limit: exp(-INR n / tau_ash) tends to zero. *)
  Lemma exp_pow_nat :
    forall (x : R) (n : nat), (exp x) ^ n = exp (INR n * x).
  Proof.
    intros x n. induction n as [|k IH].
    - simpl. rewrite Rmult_0_l. rewrite exp_0. reflexivity.
    - replace (exp x ^ S k) with (exp x * exp x ^ k) by reflexivity.
      rewrite IH.
      replace (INR (S k) * x) with (x + INR k * x) by (rewrite S_INR; ring).
      rewrite exp_plus. reflexivity.
  Qed.

  Lemma exp_neg_to_zero :
    is_lim_seq (fun n => exp (- INR n / tau_ash)) 0.
  Proof.
    pose proof (is_lim_seq_geom (exp (- 1 / tau_ash))) as Hgeom.
    assert (Habs : Rabs (exp (- 1 / tau_ash)) < 1).
    { rewrite Rabs_right by (apply Rle_ge, Rlt_le, exp_pos).
      rewrite <- exp_0.
      apply exp_increasing.
      assert (Hr : 0 < / tau_ash) by (apply Rinv_0_lt_compat; exact tau_pos).
      lra. }
    pose proof (Hgeom Habs) as Hlim.
    apply is_lim_seq_ext with (u := fun n => exp (- 1 / tau_ash) ^ n).
    - intros n.
      rewrite exp_pow_nat.
      f_equal. field. lra.
    - exact Hlim.
  Qed.

  Lemma n_ash_solution_cont : forall s, continuous n_ash_solution s.
  Proof.
    intro s.
    apply (ex_derive_continuous (K := R_AbsRing) (V := R_NormedModule)).
    exists (F_ash (n_ash_solution s)). apply n_ash_solution_satisfies_ODE.
  Qed.

  (* The closed-form solution is the Picard fixed point: applying the
     Picard operator y |-> integral_0^t F(y) to n_ash_solution returns
     n_ash_solution. This is the property the iteration converges to. *)
  Lemma minus_R0_r : forall x : R, minus x 0 = x.
  Proof. intro x. exact (minus_zero_r x). Qed.

  Theorem n_ash_solution_fixed_point :
    forall t,
      n_ash_solution t
      = RInt (fun s => F_ash (n_ash_solution s)) 0 t.
  Proof.
    intros t. symmetry.
    apply is_RInt_unique.
    replace (n_ash_solution t)
      with (minus (n_ash_solution t) (n_ash_solution 0)).
    - apply (is_RInt_derive n_ash_solution
               (fun s => F_ash (n_ash_solution s)) 0 t).
      + intros x _. apply n_ash_solution_satisfies_ODE.
      + intros x _. unfold F_ash.
        apply (continuous_minus (V := R_NormedModule)
                 (fun _ => R_primary)
                 (fun s => n_ash_solution s / tau_ash)).
        * apply continuous_const.
        * apply (continuous_mult n_ash_solution (fun _ => / tau_ash));
            [apply n_ash_solution_cont | apply continuous_const].
    - rewrite n_ash_solution_at_0. apply minus_R0_r.
  Qed.

End AshODE.

(* ================================================================== *)
(* === Picard iteration as polynomial approximation === *)
(* ================================================================== *)

(* For the affine ODE y' = a - y/tau, the Picard iteration produces the
   partial Taylor sums of the closed form; the first three are below. *)

Section PicardIterates.

  Variable R_primary tau_ash : R.
  Hypothesis tau_pos : 0 < tau_ash.

  Definition picard_iter_0 (t : R) : R := 0.

  Definition picard_iter_1 (t : R) : R := R_primary * t.

  Definition picard_iter_2 (t : R) : R :=
    R_primary * t - R_primary * t * t / (2 * tau_ash).

  Definition picard_iter_3 (t : R) : R :=
    R_primary * t - R_primary * t * t / (2 * tau_ash) +
    R_primary * t * t * t / (6 * tau_ash * tau_ash).

  Lemma picard_iter_0_value : picard_iter_0 0 = 0.
  Proof. unfold picard_iter_0. reflexivity. Qed.

  Lemma picard_iter_1_at_0 : picard_iter_1 0 = 0.
  Proof. unfold picard_iter_1. ring. Qed.

  Lemma picard_iter_2_at_0 : picard_iter_2 0 = 0.
  Proof. unfold picard_iter_2. lra. Qed.

  Lemma picard_iter_3_at_0 : picard_iter_3 0 = 0.
  Proof. unfold picard_iter_3. lra. Qed.

  (* The Picard iterate of order 1 is the time-integrated source. *)
  Theorem picard_iter_1_is_source_integral :
    forall t, picard_iter_1 t = RInt (fun _ : R => R_primary) 0 t.
  Proof.
    intros t. unfold picard_iter_1.
    rewrite RInt_const. simpl. unfold scal; simpl; unfold mult; simpl. lra.
  Qed.

End PicardIterates.

(* ================================================================== *)
(* === The general Picard fixed-point operator === *)
(* ================================================================== *)

(* The Picard iteration operator as the fixed-point recursion
     y_{n+1}(t) = y0 + integral_{t0}^{t} F(y_n(s)) ds.
   With F the affine ash right-hand side, the iterates equal the
   closed-form polynomials picard_iter_1, picard_iter_2, so the operator
   generates the Taylor partial sums of the exponential solution. *)

(* Closed form for the affine integral, via the fundamental theorem of
   calculus with antiderivative c0*s - c1*(s^2/2). *)
Lemma RInt_affine : forall (c0 c1 t : R),
  RInt (fun s => c0 - c1 * s) 0 t = c0 * t - c1 * (t * t / 2).
Proof.
  intros c0 c1 t.
  apply is_RInt_unique.
  replace (c0 * t - c1 * (t * t / 2))
    with ((c0 * t - c1 * (t * t / 2)) - (c0 * 0 - c1 * (0 * 0 / 2))) by field.
  apply (is_RInt_derive (fun s => c0 * s - c1 * (s * s / 2))
                        (fun s => c0 - c1 * s) 0 t).
  - intros x _. auto_derive. trivial. field.
  - intros x _.
    apply (continuous_minus (V := R_NormedModule) (fun _ => c0) (fun s => c1 * s)).
    + apply continuous_const.
    + apply (continuous_mult (fun _ => c1) (fun s => s));
        [apply continuous_const | apply continuous_id].
Qed.

(* Continuity of the indefinite integral of a globally continuous
   integrand: the fundamental theorem of calculus gives it a pointwise
   derivative, hence continuity. *)
Lemma indefinite_integral_cont :
  forall (g : R -> R),
    (forall x, continuous g x) ->
    forall t, continuous (fun u => RInt g 0 u) t.
Proof.
  intros g Hg t.
  apply (continuous_RInt_1 (V := R_CompleteNormedModule) g 0 t
           (fun u => RInt g 0 u)).
  apply filter_forall. intro z. apply RInt_correct.
  apply ex_RInt_continuous. intros y _. apply Hg.
Qed.

(* Real-valued specialisations of the abstract integral combinators. *)
Lemma RInt_minus_R :
  forall (f g : R -> R) (a b : R),
    ex_RInt f a b -> ex_RInt g a b ->
    RInt (fun x => f x - g x) a b = RInt f a b - RInt g a b.
Proof.
  intros f g a b Hf Hg.
  replace (RInt f a b - RInt g a b)
    with (minus (RInt f a b) (RInt g a b)) by reflexivity.
  rewrite <- (RInt_minus (V := R_CompleteNormedModule) f g a b Hf Hg).
  apply RInt_ext. intros x _. reflexivity.
Qed.

Lemma RInt_scal_R :
  forall (l : R) (f : R -> R) (a b : R),
    ex_RInt f a b ->
    RInt (fun x => l * f x) a b = l * RInt f a b.
Proof.
  intros l f a b Hf.
  replace (l * RInt f a b) with (scal l (RInt f a b)) by reflexivity.
  rewrite <- (RInt_scal (V := R_CompleteNormedModule) f a b l Hf).
  apply RInt_ext. intros x _. reflexivity.
Qed.

Section GeneralPicard.

  Variable R_primary tau_ash : R.
  Hypothesis tau_pos : 0 < tau_ash.

  Definition Faff (y : R) : R := R_primary - y / tau_ash.

  Fixpoint picard (y0 t0 : R) (n : nat) (t : R) : R :=
    match n with
    | 0%nat => y0
    | S k => y0 + RInt (fun s => Faff (picard y0 t0 k s)) t0 t
    end.

  (* Helper: integral of the identity on [0, t]. *)
  Lemma RInt_id_0t : forall t, RInt (fun s => s) 0 t = t * t / 2.
  Proof.
    intros t.
    apply is_RInt_unique.
    replace (t * t / 2) with (t * t / 2 - 0 * 0 / 2) by field.
    apply (is_RInt_derive (fun s => s * s / 2) (fun s => s) 0 t).
    - intros x _. auto_derive; [trivial | field].
    - intros x _.
      apply (continuous_id x).
  Qed.

  (* Iterate 0 is the initial value. *)
  Lemma picard_step0 : forall t, picard 0 0 0 t = 0.
  Proof. intros t. reflexivity. Qed.

  (* Iterate 1 equals the closed-form first Picard polynomial. *)
  Theorem picard_step1 :
    forall t, picard 0 0 1 t = R_primary * t.
  Proof.
    intros t.
    simpl (picard 0 0 1 t).
    transitivity (0 + RInt (fun _ : R => R_primary) 0 t).
    { f_equal. apply RInt_ext. intros s _.
      unfold Faff. simpl. field. lra. }
    rewrite RInt_const. unfold scal; simpl; unfold mult; simpl. lra.
  Qed.

  (* Iterate 2 equals the closed-form second Picard polynomial
     R_primary*t - R_primary*t^2/(2*tau). *)
  Theorem picard_step2 :
    forall t,
      picard 0 0 2 t
      = R_primary * t - R_primary * (t * t) / (2 * tau_ash).
  Proof.
    intros t.
    replace (picard 0 0 2 t)
      with (0 + RInt (fun s => Faff (picard 0 0 1 s)) 0 t)
      by reflexivity.
    (* integrand = Faff (picard 0 0 1 s) = R_primary - (R_primary*s)/tau.
       Compute the integral directly via the fundamental theorem of
       calculus with the explicit antiderivative
         F(s) = R_primary*s - R_primary/tau_ash * (s*s/2). *)
    transitivity
      (0 + RInt (fun s => R_primary - R_primary / tau_ash * s) 0 t).
    { f_equal. apply RInt_ext. intros s _.
      rewrite picard_step1. unfold Faff, Rdiv. lra. }
    rewrite Rplus_0_l.
    rewrite (RInt_affine R_primary (R_primary / tau_ash) t).
    field. lra.
  Qed.

  (* The iterates equal the closed-form polynomials picard_iter_1 and
     picard_iter_2. *)
  Theorem picard_matches_closed_forms :
    forall t,
      picard 0 0 1 t = picard_iter_1 R_primary t
      /\ picard 0 0 2 t = picard_iter_2 R_primary tau_ash t.
  Proof.
    intros t. split.
    - rewrite picard_step1. unfold picard_iter_1. reflexivity.
    - rewrite picard_step2. unfold picard_iter_2. field. lra.
  Qed.

  (* Every Picard iterate is continuous: by induction, an iterate is the
     indefinite integral of a continuous integrand built from the previous
     iterate, and that indefinite integral is continuous. *)
  Lemma picard_cont : forall n t, continuous (picard 0 0 n) t.
  Proof.
    induction n as [|n IH]; intro t.
    - replace (picard 0 0 0) with (fun _ : R => 0) by reflexivity.
      apply continuous_const.
    - replace (picard 0 0 (S n))
        with (fun u => 0 + RInt (fun s => Faff (picard 0 0 n s)) 0 u)
        by reflexivity.
      apply (continuous_plus (V := R_NormedModule)
               (fun _ => 0)
               (fun u => RInt (fun s => Faff (picard 0 0 n s)) 0 u)).
      + apply continuous_const.
      + apply indefinite_integral_cont. intro x. unfold Faff.
        apply (continuous_minus (V := R_NormedModule)
                 (fun _ => R_primary) (fun u => picard 0 0 n u / tau_ash)).
        * apply continuous_const.
        * unfold Rdiv.
          apply (continuous_mult (picard 0 0 n) (fun _ => / tau_ash));
            [ apply IH | apply continuous_const ].
  Qed.

  (* The affine right-hand side has increment -1/tau times the state
     increment. *)
  Lemma Faff_diff : forall a b, Faff a - Faff b = - / tau_ash * (a - b).
  Proof. intros a b. unfold Faff. field; lra. Qed.

  (* One-step Picard error recursion against the fixed point:
       e_{n+1}(t) = -1/tau * integral_0^t e_n(s) ds,
     where e_n(t) = picard 0 0 n t - n_ash_solution t. This linear-in-the-
     error identity is the contraction underlying the Banach argument. *)
  Theorem picard_error_one_step :
    forall n t,
      picard 0 0 (S n) t - n_ash_solution R_primary tau_ash t
      = - / tau_ash
        * RInt (fun s => picard 0 0 n s - n_ash_solution R_primary tau_ash s) 0 t.
  Proof.
    intros n t.
    replace (picard 0 0 (S n) t)
      with (0 + RInt (fun s => Faff (picard 0 0 n s)) 0 t) by reflexivity.
    rewrite Rplus_0_l.
    rewrite (n_ash_solution_fixed_point R_primary tau_ash tau_pos t).
    assert (Hext :
      RInt (fun s => F_ash R_primary tau_ash (n_ash_solution R_primary tau_ash s)) 0 t
      = RInt (fun s => Faff (n_ash_solution R_primary tau_ash s)) 0 t).
    { apply RInt_ext. intros s _. unfold F_ash, Faff. reflexivity. }
    rewrite Hext.
    assert (Hcp : forall s, continuous (fun u => Faff (picard 0 0 n u)) s).
    { intro s. unfold Faff.
      apply (continuous_minus (V := R_NormedModule)
               (fun _ => R_primary) (fun u => picard 0 0 n u / tau_ash)).
      - apply continuous_const.
      - unfold Rdiv. apply (continuous_mult (picard 0 0 n) (fun _ => / tau_ash));
          [ apply picard_cont | apply continuous_const ]. }
    assert (Hcn : forall s,
      continuous (fun u => Faff (n_ash_solution R_primary tau_ash u)) s).
    { intro s. unfold Faff.
      apply (continuous_minus (V := R_NormedModule)
               (fun _ => R_primary)
               (fun u => n_ash_solution R_primary tau_ash u / tau_ash)).
      - apply continuous_const.
      - unfold Rdiv.
        apply (continuous_mult (n_ash_solution R_primary tau_ash) (fun _ => / tau_ash));
          [ apply (n_ash_solution_cont R_primary tau_ash tau_pos)
          | apply continuous_const ]. }
    assert (Hep : @ex_RInt R_CompleteNormedModule
      (fun s => Faff (picard 0 0 n s)) 0 t)
      by (apply ex_RInt_continuous; intros z _; apply Hcp).
    assert (Hen : @ex_RInt R_CompleteNormedModule
      (fun s => Faff (n_ash_solution R_primary tau_ash s)) 0 t)
      by (apply ex_RInt_continuous; intros z _; apply Hcn).
    assert (Hed : @ex_RInt R_CompleteNormedModule
      (fun s => picard 0 0 n s - n_ash_solution R_primary tau_ash s) 0 t).
    { apply ex_RInt_continuous. intros z _.
      apply (continuous_minus (V := R_NormedModule)
               (picard 0 0 n) (n_ash_solution R_primary tau_ash)).
      - apply picard_cont.
      - apply (n_ash_solution_cont R_primary tau_ash tau_pos). }
    rewrite <- (RInt_minus_R _ _ 0 t Hep Hen).
    rewrite <- (RInt_scal_R (- / tau_ash)
                  (fun s => picard 0 0 n s - n_ash_solution R_primary tau_ash s)
                  0 t Hed).
    apply RInt_ext. intros s _. apply Faff_diff.
  Qed.

  (* Absolute-value contraction:
       |e_{n+1}(t)| <= (1/tau) integral_0^t |e_n(s)| ds.
     Bounding |e_n| by its supremum on [0,T] gives |e_{n+1}| <= (T/tau)
     sup|e_n|, the geometric contraction for T < tau. *)
  Theorem picard_error_contraction :
    forall n t, 0 <= t ->
      Rabs (picard 0 0 (S n) t - n_ash_solution R_primary tau_ash t)
      <= / tau_ash
         * RInt (fun s =>
                   Rabs (picard 0 0 n s - n_ash_solution R_primary tau_ash s)) 0 t.
  Proof.
    intros n t Ht.
    rewrite (picard_error_one_step n t).
    rewrite Rabs_mult.
    replace (Rabs (- / tau_ash)) with (/ tau_ash).
    2:{ rewrite Rabs_Ropp. symmetry. apply Rabs_pos_eq. left.
        apply Rinv_0_lt_compat. exact tau_pos. }
    apply Rmult_le_compat_l.
    - left. apply Rinv_0_lt_compat. exact tau_pos.
    - apply abs_RInt_le.
      + exact Ht.
      + assert (Hd : @ex_RInt R_CompleteNormedModule
          (fun s => picard 0 0 n s - n_ash_solution R_primary tau_ash s) 0 t).
        { apply ex_RInt_continuous. intros z _.
          apply (continuous_minus (V := R_NormedModule)
                   (picard 0 0 n) (n_ash_solution R_primary tau_ash)).
          - apply picard_cont.
          - apply (n_ash_solution_cont R_primary tau_ash tau_pos). }
        exact Hd.
  Qed.

End GeneralPicard.

(* ================================================================== *)
(* === Composition with M_ash_decreasing === *)
(* ================================================================== *)

(* The multiplication-factor M decreases as n_ash increases (more
   "ash" dilutes the boron density, reducing the secondary rate).
   Since n_ash_solution increases monotonically, M(t) decreases
   monotonically. *)

Theorem n_ash_solution_nonneg :
  forall R_primary tau t, 0 < R_primary -> 0 < tau -> 0 <= t ->
    0 <= n_ash_solution R_primary tau t.
Proof.
  intros R_primary tau t HR Htau Ht.
  unfold n_ash_solution, n_ash_eq.
  apply Rmult_le_pos.
  - apply Rmult_le_pos; lra.
  - assert (Hexp : exp (- t / tau) <= 1).
    { destruct (Req_dec t 0) as [Heq | Hneq].
      - subst. replace (- 0 / tau) with 0 by lra. rewrite exp_0. lra.
      - assert (Hpos : 0 < t) by lra.
        rewrite <- exp_0. apply Rlt_le. apply exp_increasing.
        assert (Hneg : - t / tau < 0).
        { unfold Rdiv. apply Rmult_neg_pos.
          - lra.
          - apply Rinv_0_lt_compat; exact Htau. }
        exact Hneg. }
    lra.
Qed.

Theorem n_ash_solution_bounded_by_eq :
  forall R_primary tau t, 0 < R_primary -> 0 < tau -> 0 <= t ->
    n_ash_solution R_primary tau t <= n_ash_eq R_primary tau.
Proof.
  intros R_primary tau t HR Htau Ht.
  unfold n_ash_solution.
  rewrite <- (Rmult_1_r (n_ash_eq R_primary tau)) at 2.
  apply Rmult_le_compat_l.
  - unfold n_ash_eq. apply Rlt_le, Rmult_lt_0_compat; assumption.
  - assert (Hexp_pos : 0 < exp (- t / tau)) by apply exp_pos.
    lra.
Qed.

(* ================================================================== *)
(* === Picard iterates converge to the closed-form solution === *)
(* ================================================================== *)

Section PicardConvergence.

  Variable R_primary tau_ash : R.
  Hypothesis R_pos : 0 < R_primary.
  Hypothesis tau_pos : 0 < tau_ash.

  Lemma picard_e0_bound :
    forall t, 0 <= t ->
      Rabs (picard R_primary tau_ash 0 0 0 t - n_ash_solution R_primary tau_ash t)
      <= R_primary * tau_ash.
  Proof.
    intros t Ht.
    replace (picard R_primary tau_ash 0 0 0 t) with 0 by reflexivity.
    rewrite Rminus_0_l, Rabs_Ropp.
    rewrite Rabs_pos_eq
      by (apply (n_ash_solution_nonneg R_primary tau_ash t R_pos tau_pos Ht)).
    apply (n_ash_solution_bounded_by_eq R_primary tau_ash t R_pos tau_pos Ht).
  Qed.

  Lemma picard_geom_bound :
    forall (T : R), 0 <= T -> T < tau_ash ->
    forall n t, 0 <= t <= T ->
      Rabs (picard R_primary tau_ash 0 0 n t - n_ash_solution R_primary tau_ash t)
      <= (R_primary * tau_ash) * (T / tau_ash) ^ n.
  Proof.
    intros T HT0 HTtau n. induction n as [|n IH]; intros t [Ht0 HtT].
    - simpl (( T / tau_ash) ^ 0). rewrite Rmult_1_r.
      apply picard_e0_bound; exact Ht0.
    - eapply Rle_trans.
      { apply (picard_error_contraction R_primary tau_ash tau_pos n t Ht0). }
      assert (Hc : 0 <= (R_primary * tau_ash) * (T / tau_ash) ^ n).
      { apply Rmult_le_pos.
        - apply Rlt_le, Rmult_lt_0_compat; assumption.
        - apply pow_le. apply Rmult_le_pos;
            [ lra | apply Rlt_le, Rinv_0_lt_compat; exact tau_pos ]. }
      assert (Hint :
        RInt (fun s => Rabs (picard R_primary tau_ash 0 0 n s
                             - n_ash_solution R_primary tau_ash s)) 0 t
        <= (R_primary * tau_ash) * (T / tau_ash) ^ n * t).
      { replace ((R_primary * tau_ash) * (T / tau_ash) ^ n * t)
          with (RInt (fun _ => (R_primary * tau_ash) * (T / tau_ash) ^ n) 0 t).
        2:{ rewrite RInt_const. unfold scal; simpl; unfold mult; simpl. ring. }
        apply RInt_le.
        - exact Ht0.
        - apply (ex_RInt_continuous (V := R_CompleteNormedModule)). intros s _.
          apply (continuous_comp
                   (fun s => picard R_primary tau_ash 0 0 n s
                             - n_ash_solution R_primary tau_ash s) Rabs).
          + apply (continuous_minus (V := R_NormedModule)
                     (picard R_primary tau_ash 0 0 n)
                     (n_ash_solution R_primary tau_ash)).
            * apply (picard_cont R_primary tau_ash).
            * apply (n_ash_solution_cont R_primary tau_ash tau_pos).
          + apply (continuous_abs (K := R_AbsRing)).
        - apply ex_RInt_const.
        - intros s [Hs0 Hst]. apply IH. split; lra. }
      apply Rle_trans with
        (/ tau_ash * ((R_primary * tau_ash) * (T / tau_ash) ^ n * t)).
      { apply Rmult_le_compat_l;
          [ apply Rlt_le, Rinv_0_lt_compat; exact tau_pos | exact Hint ]. }
      apply Rle_trans with
        (/ tau_ash * ((R_primary * tau_ash) * (T / tau_ash) ^ n * T)).
      { apply Rmult_le_compat_l;
          [ apply Rlt_le, Rinv_0_lt_compat; exact tau_pos | ].
        apply Rmult_le_compat_l; [ exact Hc | exact HtT ]. }
      simpl (( T / tau_ash) ^ S n). set (qn := (T / tau_ash) ^ n).
      apply Req_le. field. lra.
  Qed.

  Theorem picard_converges :
    forall (T : R), 0 <= T -> T < tau_ash ->
    forall t, 0 <= t <= T ->
      is_lim_seq (fun n => picard R_primary tau_ash 0 0 n t)
                 (n_ash_solution R_primary tau_ash t).
  Proof.
    intros T HT0 HTtau t Ht.
    set (C := R_primary * tau_ash). set (q := T / tau_ash).
    assert (Hq0 : 0 <= q)
      by (unfold q; apply Rmult_le_pos;
          [ lra | apply Rlt_le, Rinv_0_lt_compat; exact tau_pos ]).
    assert (Hq1 : q < 1).
    { unfold q. apply (Rmult_lt_reg_r tau_ash); [ exact tau_pos | ].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra. lra. }
    assert (HC : 0 <= C)
      by (unfold C; apply Rlt_le, Rmult_lt_0_compat; assumption).
    assert (Hlim0 :
      is_lim_seq (fun n => picard R_primary tau_ash 0 0 n t
                           - n_ash_solution R_primary tau_ash t) 0).
    { apply (is_lim_seq_le_le (fun n => - C * q ^ n)
               (fun n => picard R_primary tau_ash 0 0 n t
                         - n_ash_solution R_primary tau_ash t)
               (fun n => C * q ^ n)).
      - intro n.
        pose proof (picard_geom_bound T HT0 HTtau n t Ht) as Hb.
        fold C q in Hb.
        pose proof (Rle_abs (picard R_primary tau_ash 0 0 n t
                             - n_ash_solution R_primary tau_ash t)) as Hu.
        pose proof (Rle_abs (- (picard R_primary tau_ash 0 0 n t
                             - n_ash_solution R_primary tau_ash t))) as Hl.
        rewrite Rabs_Ropp in Hl. lra.
      - replace (Finite 0) with (Rbar_mult (- C) (Finite 0)) by (simpl; f_equal; ring).
        apply (is_lim_seq_scal_l (fun n => q ^ n) (- C) 0).
        apply is_lim_seq_geom. rewrite Rabs_pos_eq; lra.
      - replace (Finite 0) with (Rbar_mult C (Finite 0)) by (simpl; f_equal; ring).
        apply (is_lim_seq_scal_l (fun n => q ^ n) C 0).
        apply is_lim_seq_geom. rewrite Rabs_pos_eq; lra. }
    apply (is_lim_seq_ext
             (fun n => (picard R_primary tau_ash 0 0 n t
                        - n_ash_solution R_primary tau_ash t)
                       + n_ash_solution R_primary tau_ash t)).
    { intro n. ring. }
    apply (is_lim_seq_plus _ (fun _ => n_ash_solution R_primary tau_ash t)
             0 (n_ash_solution R_primary tau_ash t)
             (n_ash_solution R_primary tau_ash t)).
    - exact Hlim0.
    - apply is_lim_seq_const.
    - unfold is_Rbar_plus; simpl; rewrite Rplus_0_l; reflexivity.
  Qed.

End PicardConvergence.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions n_eff_with_ash_pos.
Print Assumptions tau_slow_alpha_ash_pos.
Print Assumptions tau_slow_alpha_ash_decreasing.
Print Assumptions M_ash_decreasing.
Print Assumptions n_ash_solution_satisfies_ODE.
Print Assumptions n_ash_solution_at_0.
Print Assumptions picard_iter_1_is_source_integral.
Print Assumptions picard_step1.
Print Assumptions picard_step2.
Print Assumptions picard_matches_closed_forms.
Print Assumptions n_ash_solution_fixed_point.
Print Assumptions n_ash_solution_nonneg.
Print Assumptions n_ash_solution_bounded_by_eq.
Print Assumptions picard_geom_bound.
Print Assumptions picard_converges.
Print Assumptions picard_cont.
Print Assumptions picard_error_one_step.
Print Assumptions picard_error_contraction.
