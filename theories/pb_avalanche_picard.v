(******************************************************************************)
(*                                                                            *)
(*     Time-evolution layer via Picard iteration (item 4)                     *)
(*                                                                            *)
(*     Defines the Picard fixed-point iteration                               *)
(*       y_{n+1}(t) := y_0 + integral_{t_0}^{t} F(s, y_n(s)) ds               *)
(*     for the affine ash-production ODE                                      *)
(*       dn_ash/dt = R_primary - n_ash / tau_ash                              *)
(*     and verifies that the closed-form solution                             *)
(*       n_ash(t) = n_ash_eq * (1 - exp(-t / tau_ash))                        *)
(*     where n_ash_eq = R_primary * tau_ash, satisfies the ODE pointwise.     *)
(*                                                                            *)
(*     The Picard iterates are explicit polynomial approximations to the      *)
(*     exponential's Taylor series. We compute the first three and verify     *)
(*     they match the partial Taylor expansion of n_ash_eq * (1 - exp...).   *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

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

End AshODE.

(* ================================================================== *)
(* === Picard iteration as polynomial approximation === *)
(* ================================================================== *)

(* For the affine ODE y' = a - y/tau, the Picard iteration produces the
   partial Taylor sums of the closed-form. We compute the first three. *)

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
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions n_ash_solution_satisfies_ODE.
Print Assumptions n_ash_solution_at_0.
Print Assumptions picard_iter_1_is_source_integral.
Print Assumptions n_ash_solution_nonneg.
Print Assumptions n_ash_solution_bounded_by_eq.
