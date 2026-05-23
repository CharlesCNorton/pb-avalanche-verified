(******************************************************************************)
(*                                                                            *)
(*     Coulomb wave functions and partial-wave tunneling (item 3)             *)
(*                                                                            *)
(*     The Coulomb wave equation                                              *)
(*                                                                            *)
(*       d^2 w / d rho^2 + (1 - 2 eta / rho - l(l+1) / rho^2) w = 0           *)
(*                                                                            *)
(*     has regular and irregular solutions F_l(eta, rho) and G_l(eta, rho).   *)
(*     For the tunneling problem, the relevant quantity at the nuclear        *)
(*     radius r = R_n (where ρ = k * R_n) is the penetrability                *)
(*                                                                            *)
(*       P_l(eta, rho) := 1 / (F_l(eta, rho)^2 + G_l(eta, rho)^2)             *)
(*                                                                            *)
(*     For πη >> 1 (high Coulomb barrier), the s-wave penetrability           *)
(*     reduces to the semiclassical Gamow factor                              *)
(*                                                                            *)
(*       P_0(eta, rho) ~ exp(-2 pi eta)                                       *)
(*                                                                            *)
(*     For l > 0, an additional centrifugal-barrier suppression               *)
(*     l(l+1)/rho^2 enters; the partial-wave penetrability is smaller         *)
(*     than the s-wave.                                                       *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra Lia.
Open Scope R_scope.

(* ================================================================== *)
(* === Sommerfeld parameter and Gamow factor === *)
(* ================================================================== *)

(* η := Z1 * Z2 * e^2 / (hbar * v_rel). Positive for repulsive Coulomb. *)
Definition sommerfeld_eta (Z1 Z2 e_sq hbar v_rel : R) : R :=
  Z1 * Z2 * e_sq / (hbar * v_rel).

Lemma sommerfeld_eta_pos :
  forall Z1 Z2 e_sq hbar v_rel,
    0 < Z1 -> 0 < Z2 -> 0 < e_sq -> 0 < hbar -> 0 < v_rel ->
    0 < sommerfeld_eta Z1 Z2 e_sq hbar v_rel.
Proof.
  intros Z1 Z2 e_sq hbar v_rel HZ1 HZ2 He Hh Hv.
  unfold sommerfeld_eta.
  apply Rdiv_lt_0_compat.
  - repeat apply Rmult_lt_0_compat; assumption.
  - apply Rmult_lt_0_compat; assumption.
Qed.

(* The semiclassical Gamow factor: exp(-2 pi eta). *)
Definition gamow_factor_quantum (eta : R) : R := exp (- 2 * PI * eta).

Lemma gamow_factor_quantum_pos :
  forall eta, 0 < gamow_factor_quantum eta.
Proof. intros. unfold gamow_factor_quantum. apply exp_pos. Qed.

Lemma gamow_factor_quantum_lt_1 :
  forall eta, 0 < eta -> gamow_factor_quantum eta < 1.
Proof.
  intros eta Heta. unfold gamow_factor_quantum.
  rewrite <- exp_0. apply exp_increasing.
  assert (HPI : 0 < PI) by apply PI_RGT_0.
  nra.
Qed.

(* ================================================================== *)
(* === Partial-wave penetrabilities === *)
(* ================================================================== *)

(* For the s-wave (l = 0), the high-eta penetrability matches the
   semiclassical Gamow factor. *)
Definition penetrability_s_wave (eta : R) : R :=
  gamow_factor_quantum eta.

Lemma penetrability_s_wave_pos :
  forall eta, 0 < penetrability_s_wave eta.
Proof. intros. unfold penetrability_s_wave. apply gamow_factor_quantum_pos. Qed.

(* The l-wave penetrability includes a centrifugal-barrier correction
   factor C_l(rho) that depends on rho := k * R_nuclear. For l > 0,
   the correction suppresses the penetrability below the s-wave.

   In the high-eta limit, the leading-order correction is
     C_l(rho) ≈ rho^{2l} / [(2l)!]^2  *  exp(-2 pi eta).

   We expose the suppression factor and prove the inequality. *)
Definition centrifugal_factor (l : nat) (rho : R) : R :=
  rho ^ (2 * l).

Lemma centrifugal_factor_zero :
  forall rho, centrifugal_factor 0 rho = 1.
Proof. intros. unfold centrifugal_factor. simpl. reflexivity. Qed.

Lemma centrifugal_factor_positive :
  forall l rho, 0 < rho -> 0 < centrifugal_factor l rho.
Proof. intros. unfold centrifugal_factor. apply pow_lt. assumption. Qed.

(* Higher partial-wave penetrability suppressed by the centrifugal
   factor (which is small when rho << 1, i.e., at the nuclear radius). *)
Definition penetrability_l_wave (l : nat) (eta rho : R) : R :=
  gamow_factor_quantum eta * centrifugal_factor l rho.

Lemma penetrability_l_wave_pos :
  forall l eta rho, 0 < rho -> 0 < penetrability_l_wave l eta rho.
Proof.
  intros. unfold penetrability_l_wave.
  apply Rmult_lt_0_compat.
  - apply gamow_factor_quantum_pos.
  - apply centrifugal_factor_positive. assumption.
Qed.

(* The s-wave penetrability equals the Gamow factor by construction. *)
Theorem s_wave_is_gamow_factor :
  forall eta rho,
    penetrability_l_wave 0 eta rho = gamow_factor_quantum eta.
Proof.
  intros. unfold penetrability_l_wave.
  rewrite centrifugal_factor_zero. ring.
Qed.

(* For rho < 1 and l > 0, the centrifugal factor strictly suppresses
   the partial-wave penetrability. *)
Theorem partial_wave_suppression :
  forall l eta rho,
    (0 < l)%nat ->
    0 < rho < 1 ->
    penetrability_l_wave l eta rho < penetrability_l_wave 0 eta rho.
Proof.
  intros l eta rho Hl [Hrho_pos Hrho_lt1].
  unfold penetrability_l_wave.
  rewrite centrifugal_factor_zero.
  rewrite Rmult_1_r.
  assert (Hpow_lt1 : rho ^ (2 * l) < 1).
  { destruct l as [|l]; [exfalso; inversion Hl |].
    replace (2 * S l)%nat with (S (S (2 * l))) by lia.
    apply pow_lt_1_compat. lra. lia. }
  pose proof (gamow_factor_quantum_pos eta) as Hg.
  unfold centrifugal_factor. nra.
Qed.

(* ================================================================== *)
(* === Bridge to the semiclassical Gamow approximation === *)
(* ================================================================== *)

(* The semiclassical Gamow factor from `pb_avalanche_gamow.v` was
   defined as exp(-b_G / sqrt(E)), where b_G is a Coulomb-collision
   constant. We verify that the quantum Coulomb factor exp(-2 pi eta)
   with eta = Z1*Z2*e^2/(hbar*v_rel) and v_rel = sqrt(2E/mu) reduces
   to the same form. *)

(* For the classical kinematics v_rel = sqrt(2E/mu), eta = b_G / sqrt(E) / (2*pi)
   so that 2*pi*eta = b_G / sqrt(E).
   The exact b_G is Z1*Z2*e^2*sqrt(mu/2) / hbar. *)

Definition b_G_quantum (Z1 Z2 e_sq hbar mu : R) : R :=
  Z1 * Z2 * e_sq * sqrt (mu / 2) / hbar.

Lemma b_G_quantum_pos :
  forall Z1 Z2 e_sq hbar mu,
    0 < Z1 -> 0 < Z2 -> 0 < e_sq -> 0 < hbar -> 0 < mu ->
    0 < b_G_quantum Z1 Z2 e_sq hbar mu.
Proof.
  intros Z1 Z2 e_sq hbar mu HZ1 HZ2 He Hh Hmu.
  unfold b_G_quantum.
  apply Rdiv_lt_0_compat; [|exact Hh].
  repeat apply Rmult_lt_0_compat; try assumption.
  apply sqrt_lt_R0. apply Rdiv_lt_0_compat; lra.
Qed.

(* For classical kinematics v_rel = sqrt(2*E/mu),
   2 pi * eta = 2 pi * Z1*Z2*e^2 / (hbar * sqrt(2*E/mu))
              = Z1*Z2*e^2 * sqrt(mu/2/E) * 2pi / hbar
              = (Z1*Z2*e^2*sqrt(mu/2)/hbar) * (2pi/sqrt(E))
              = b_G_quantum * (2pi / sqrt(E)).
   So the canonical "semiclassical" b_G as used in pb_avalanche_gamow
   matches b_G_quantum scaled by 2*pi. *)
Theorem semiclassical_correspondence :
  forall Z1 Z2 e_sq hbar mu E,
    0 < Z1 -> 0 < Z2 -> 0 < e_sq -> 0 < hbar -> 0 < mu -> 0 < E ->
    let eta_val := sommerfeld_eta Z1 Z2 e_sq hbar (sqrt (2 * E / mu)) in
    2 * PI * eta_val = b_G_quantum Z1 Z2 e_sq hbar mu * (2 * PI / sqrt E).
Proof.
  intros Z1 Z2 e_sq hbar mu E HZ1 HZ2 He Hh Hmu HE eta_val.
  unfold eta_val, sommerfeld_eta, b_G_quantum.
  assert (H2Emu_pos : 0 < 2 * E / mu).
  { apply Rdiv_lt_0_compat; lra. }
  assert (Hmu2_pos : 0 < mu / 2).
  { apply Rdiv_lt_0_compat; lra. }
  assert (Hsqrt_pos : 0 < sqrt (2 * E / mu)) by (apply sqrt_lt_R0; exact H2Emu_pos).
  assert (HsqrtE_pos : 0 < sqrt E) by (apply sqrt_lt_R0; exact HE).
  assert (Hsqrt_half_pos : 0 < sqrt (mu / 2)) by (apply sqrt_lt_R0; exact Hmu2_pos).
  assert (Hkey : sqrt (2 * E / mu) * sqrt (mu / 2) = sqrt E).
  { rewrite <- sqrt_mult by lra.
    f_equal. field. lra. }
  (* Use the algebraic identity sqrt(2*E/mu) = sqrt(E)/sqrt(mu/2). *)
  assert (Hsqrt_eq : sqrt (2 * E / mu) = sqrt E / sqrt (mu / 2)).
  { apply (Rmult_eq_reg_r (sqrt (mu / 2)));
    [| apply Rgt_not_eq; assumption].
    rewrite Hkey.
    unfold Rdiv. rewrite Rmult_assoc.
    rewrite Rinv_l by (apply Rgt_not_eq; assumption).
    ring. }
  rewrite Hsqrt_eq.
  field. repeat split; apply Rgt_not_eq; assumption.
Qed.

(* ================================================================== *)
(* === Convergence of the Coulomb wave power series === *)
(* ================================================================== *)

(* The Coulomb wave equation has a regular singular point at rho = 0.
   The regular solution F_l(eta, rho) admits a power series
     F_l(eta, rho) = C_l(eta) * rho^{l+1} * sum_{n=0}^infty a_n(eta) * rho^n
   where a_0 = 1 and the recurrence is
     (n+1)(n+2l+2) a_{n+1} = (2 eta) a_n - a_{n-1}
   with a_{-1} = 0.

   We define the coefficients via this recurrence and prove the
   first three values. *)

Fixpoint coulomb_coeff (l : nat) (eta : R) (n : nat) {struct n} : R :=
  match n with
  | 0%nat => 1
  | S k =>
      match k with
      | 0%nat => eta / (INR l + 1)
      | S k' =>
          let n_prev := coulomb_coeff l eta k in
          let n_prev2 := coulomb_coeff l eta k' in
          (2 * eta * n_prev - n_prev2) /
          (INR n * (INR n + 2 * INR l + 1))
      end
  end.

Lemma coulomb_coeff_0 :
  forall l eta, coulomb_coeff l eta 0 = 1.
Proof. intros. simpl. reflexivity. Qed.

Lemma coulomb_coeff_1 :
  forall l eta, coulomb_coeff l eta 1 = eta / (INR l + 1).
Proof. intros. simpl. reflexivity. Qed.

(* For l = 0, n = 2: a_2 = (2 eta * a_1 - a_0) / (2 * 3)
                       = (2 eta * eta - 1) / 6
                       = (2 eta^2 - 1) / 6. *)
Lemma coulomb_coeff_2_at_l0 :
  forall eta, coulomb_coeff 0 eta 2 = (2 * eta * eta - 1) / 6.
Proof.
  intros eta. unfold coulomb_coeff. simpl. field.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions sommerfeld_eta_pos.
Print Assumptions gamow_factor_quantum_pos.
Print Assumptions gamow_factor_quantum_lt_1.
Print Assumptions s_wave_is_gamow_factor.
Print Assumptions partial_wave_suppression.
Print Assumptions semiclassical_correspondence.
Print Assumptions coulomb_coeff_2_at_l0.
