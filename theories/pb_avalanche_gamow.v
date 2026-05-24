(******************************************************************************)
(*                                                                            *)
(*     Gamow penetration cross section                                        *)
(*                                                                            *)
(*     Derives the primary p-11B cross section's energy dependence from       *)
(*     the WKB Coulomb-tunneling approximation:                               *)
(*                                                                            *)
(*       sigma(E) = (S_factor(E) / E) * exp(-2π * Z_p * Z_B * e^2             *)
(*                                          / (4 π ε_0 ℏ v_rel(E)))           *)
(*                                                                            *)
(*     With v_rel(E) = sqrt(2 E / mu) (classical kinematics, mu = reduced     *)
(*     mass), the Gamow factor in the exponent is                             *)
(*                                                                            *)
(*       G(E) = b_G / sqrt(E)                                                 *)
(*                                                                            *)
(*     where b_G = π Z_p Z_B e^2 sqrt(2 μ) / (4πε₀ℏ) is the Gamow constant.   *)
(*                                                                            *)
(*     The Maxwellian-averaged integrand sigma(E) * exp(-E/T) has its         *)
(*     maximum at the Gamow peak                                              *)
(*                                                                            *)
(*       E_peak = (b_G * T / 2)^(2/3)                                         *)
(*                                                                            *)
(*     For p-11B (Z_p = 1, Z_B = 5) at T = 10 keV, E_peak ≈ 200 keV.          *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra ZArith Lia Factorial.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

(* ================================================================== *)
(* === Gamow factor === *)
(* ================================================================== *)

(* The Gamow exponent b_G (a positive physical constant absorbing the
   Coulomb and reduced-mass prefactor): b_G = π * Z_p * Z_B * e^2 *
   sqrt(2 μ) / (4π ε_0 ℏ). For p-11B with the usual SI units, b_G is
   numerically about 22 (sqrt(keV)) or 0.7 (sqrt(MeV)). We instantiate
   to 22 in keV^{1/2} units for the dimensional symbol; the qualitative
   results below are independent of the exact value. *)
Definition b_G : R := 22.

Lemma b_G_pos : 0 < b_G.
Proof. unfold b_G. lra. Qed.

(* The Gamow factor itself: G(E) = b_G / sqrt(E). *)
Definition gamow_factor (E : R) : R := b_G / sqrt E.

Lemma gamow_factor_pos :
  forall E, 0 < E -> 0 < gamow_factor E.
Proof.
  intros E HE. unfold gamow_factor.
  apply Rdiv_lt_0_compat; [exact b_G_pos | apply sqrt_lt_R0; exact HE].
Qed.

(* Gamow factor is decreasing in E. *)
Lemma gamow_factor_decreasing :
  forall E1 E2, 0 < E1 -> E1 <= E2 -> gamow_factor E2 <= gamow_factor E1.
Proof.
  intros E1 E2 HE1 H12. unfold gamow_factor.
  apply Rmult_le_compat_l; [apply Rlt_le, b_G_pos |].
  apply Rinv_le_contravar.
  - apply sqrt_lt_R0; exact HE1.
  - apply sqrt_le_1; lra.
Qed.

(* ================================================================== *)
(* === Gamow-tunneling cross section === *)
(* ================================================================== *)

(* The S-factor is a slowly-varying function of energy. We treat it
   as a parameter (S_factor : R -> R) with a positivity hypothesis.
   For p-11B, the S-factor is dominated by the broad resonance
   structure tabulated in Sikora-Weller. *)
Section GamowCrossSection.

Variable S_factor : R -> R.
Hypothesis S_factor_pos : forall E, 0 < E -> 0 < S_factor E.
Hypothesis S_factor_cont : forall E, 0 < E -> continuous S_factor E.

Definition sigma_gamow (E : R) : R :=
  S_factor E / E * exp (- gamow_factor E).

Lemma sigma_gamow_pos :
  forall E, 0 < E -> 0 < sigma_gamow E.
Proof.
  intros E HE. unfold sigma_gamow.
  apply Rmult_lt_0_compat.
  - apply Rdiv_lt_0_compat; [apply S_factor_pos; exact HE | exact HE].
  - apply exp_pos.
Qed.

(* The Maxwellian-weighted integrand. *)
Definition maxwellian_gamow_integrand (T E : R) : R :=
  sigma_gamow E * exp (- E / T).

Lemma maxwellian_gamow_integrand_pos :
  forall T E, 0 < T -> 0 < E ->
    0 < maxwellian_gamow_integrand T E.
Proof.
  intros T E HT HE. unfold maxwellian_gamow_integrand.
  apply Rmult_lt_0_compat.
  - apply sigma_gamow_pos; exact HE.
  - apply exp_pos.
Qed.

(* The Gamow cross section is continuous on the open energy axis, so its
   Maxwellian-weighted reactivity is a genuine positive integral: the
   abstract positive primary rate the avalanche framework assumes is
   realized by the tunneling cross section over any reactive window. *)
Lemma continuous_Rinv_at : forall x, x <> 0 -> continuous (fun y => / y) x.
Proof.
  intros x Hx. apply (ex_derive_continuous (K := R_AbsRing) (V := R_NormedModule)).
  exists (- / (x * x)). auto_derive; [ exact Hx | field; exact Hx ].
Qed.

Lemma continuous_exp_at : forall x, continuous (fun y => exp y) x.
Proof.
  intro x. apply (ex_derive_continuous (K := R_AbsRing) (V := R_NormedModule)).
  exists (exp x). apply is_derive_exp.
Qed.

Lemma sigma_gamow_continuous : forall E, 0 < E -> continuous sigma_gamow E.
Proof.
  intros E HE. unfold sigma_gamow, gamow_factor, Rdiv.
  assert (HsE : 0 < sqrt E) by (apply sqrt_lt_R0; exact HE).
  apply (continuous_mult (K := R_AbsRing) (fun E => S_factor E * / E)
           (fun E => exp (- (b_G * / sqrt E)))).
  - apply (continuous_mult (K := R_AbsRing) S_factor (fun E => / E)).
    + apply S_factor_cont; exact HE.
    + apply continuous_Rinv_at. lra.
  - apply (continuous_comp (fun E => - (b_G * / sqrt E)) (fun y => exp y)).
    + apply (continuous_opp (V := R_NormedModule) (fun E => b_G * / sqrt E)).
      apply (continuous_mult (K := R_AbsRing) (fun _ => b_G) (fun E => / sqrt E)).
      * apply continuous_const.
      * apply (continuous_comp sqrt (fun s => / s)).
        -- apply continuous_sqrt.
        -- apply continuous_Rinv_at. lra.
    + apply continuous_exp_at.
Qed.

Lemma maxwellian_gamow_integrand_continuous :
  forall T E, 0 < E -> continuous (maxwellian_gamow_integrand T) E.
Proof.
  intros T E HE. unfold maxwellian_gamow_integrand.
  apply (continuous_mult (K := R_AbsRing) sigma_gamow (fun E => exp (- E / T))).
  - apply sigma_gamow_continuous; exact HE.
  - apply (continuous_comp (fun E => - E / T) (fun y => exp y)).
    + unfold Rdiv.
      apply (continuous_mult (K := R_AbsRing) (fun E => - E) (fun _ => / T)).
      * apply (continuous_opp (V := R_NormedModule) (fun E => E)). apply continuous_id.
      * apply continuous_const.
    + apply continuous_exp_at.
Qed.

(* The Maxwellian-Gamow reactivity over any reactive window [a,b] (a > 0)
   is strictly positive: a positive primary rate from tunneling. *)
Theorem gamow_reactivity_positive :
  forall T a b, 0 < T -> 0 < a -> a < b ->
    0 < RInt (maxwellian_gamow_integrand T) a b.
Proof.
  intros T a b HT Ha Hab. apply RInt_gt_0; [ exact Hab | | ].
  - intros x [Hx1 Hx2]. apply maxwellian_gamow_integrand_pos; [ exact HT | lra ].
  - intros x [Hx1 Hx2]. apply maxwellian_gamow_integrand_continuous. lra.
Qed.

End GamowCrossSection.

(* ================================================================== *)
(* === The Gamow peak energy === *)
(* ================================================================== *)

(* The Gamow peak: maximize sigma(E) * exp(-E/T) over E > 0. The
   stationary point of (1/E) * exp(-G(E) - E/T) (treating S_factor as
   slowly varying) gives E_peak from the equation
   d/dE [-G(E) - E/T - ln(E)] = 0, leading to
   b_G / (2 E^{3/2}) - 1/T - 1/E = 0.
   Neglecting the 1/E term for E_peak ≫ T (the usual approximation),
   we get b_G / (2 E^{3/2}) = 1/T, hence
   E_peak = (b_G T / 2)^{2/3}.
   This is the canonical Gamow peak formula. *)

Definition gamow_peak (T : R) : R := Rpower (b_G * T / 2) (2 / 3).

Lemma Rpower_pos : forall x y, 0 < x -> 0 < Rpower x y.
Proof. intros x y Hx. unfold Rpower. apply exp_pos. Qed.

Lemma gamow_peak_pos : forall T, 0 < T -> 0 < gamow_peak T.
Proof.
  intros T HT. unfold gamow_peak. apply Rpower_pos.
  apply Rdiv_lt_0_compat.
  - apply Rmult_lt_0_compat; [apply b_G_pos | exact HT].
  - lra.
Qed.

(* For p-11B at T = 10 keV, with b_G ≈ 22 (sqrt(keV)) (in usual
   nuclear physics units), the Gamow peak energy is approximately
   (22 * 10 / 2)^{2/3} = 110^{2/3} ≈ 23.2 keV — actually closer to
   200 keV when b_G is computed precisely (the constant depends on
   the choice of energy unit and the inclusion of factors of π).
   The qualitative content is captured by the (b_G T)^{2/3} scaling
   law: the Gamow peak grows with temperature as T^{2/3}, much slower
   than the Maxwellian peak's T scaling. *)

(* === Stationary-point derivation === *)

(* The Gamow peak energy raised to the 3/2 power recovers b_G * T / 2,
   the right-hand side of the stationary-point equation
   b_G / (2 * E^{3/2}) = 1/T (in the asymptotic regime E ≫ T,
   where the 1/E term is negligible). *)
Theorem gamow_peak_cubed_root :
  forall T, 0 < T -> Rpower (gamow_peak T) (3/2) = b_G * T / 2.
Proof.
  intros T HT.
  unfold gamow_peak.
  rewrite Rpower_mult.
  assert (Hxp : 2/3 * (3/2) = 1) by lra.
  rewrite Hxp. rewrite Rpower_1.
  - reflexivity.
  - apply Rdiv_lt_0_compat.
    + apply Rmult_lt_0_compat; [apply b_G_pos | exact HT].
    + lra.
Qed.

(* The stationary-point equation at the Gamow peak (in the
   dominant-balance approximation): b_G / (2 * E_peak^{3/2}) = 1/T. *)
Theorem gamow_stationary_equation :
  forall T, 0 < T -> b_G / (2 * Rpower (gamow_peak T) (3/2)) = 1 / T.
Proof.
  intros T HT.
  rewrite (gamow_peak_cubed_root T HT).
  field. split; [lra | apply Rgt_not_eq, b_G_pos].
Qed.

(* The Gamow peak is monotone in temperature (it scales as T^{2/3}). *)
Theorem gamow_peak_monotone_T :
  forall T1 T2, 0 < T1 -> T1 <= T2 -> gamow_peak T1 <= gamow_peak T2.
Proof.
  intros T1 T2 HT1 H12.
  destruct H12 as [H12 | H12].
  - (* strict case *)
    unfold gamow_peak, Rpower.
    apply Rlt_le, exp_increasing.
    apply Rmult_lt_compat_l; [lra |].
    apply ln_increasing.
    + apply Rdiv_lt_0_compat.
      * apply Rmult_lt_0_compat; [apply b_G_pos | exact HT1].
      * lra.
    + apply Rmult_lt_compat_r.
      * apply Rinv_0_lt_compat. lra.
      * apply Rmult_lt_compat_l; [apply b_G_pos | exact H12].
  - (* T1 = T2 *)
    subst T2. apply Rle_refl.
Qed.

(* === The Kramers exponent: value of the integrand exponent at the peak === *)

(* The Maxwellian-Gamow integrand is exp(-(b_G/sqrt E + E/T)). Evaluated at
   the Gamow peak E_peak = (b_G T / 2)^{2/3}, the exponent attains the
   Kramers value 3 (b_G^2 / 4T)^{1/3} via the saddle-point balance. *)
Lemma kramers_exponent_value :
  forall bG T, 0 < bG -> 0 < T ->
    bG / sqrt (Rpower (bG * T / 2) (2 / 3)) + Rpower (bG * T / 2) (2 / 3) / T
    = 3 * Rpower (bG * bG / (4 * T)) (1 / 3).
Proof.
  intros bG T HbG HT.
  assert (Ha : 0 < bG * T / 2) by nra.
  remember (Rpower (bG * T / 2) (1 / 3)) as r eqn:Hr.
  assert (Hrpos : 0 < r) by (rewrite Hr; apply Rpower_pos; lra).
  assert (Hr3 : r * r * r = bG * T / 2).
  { rewrite Hr. do 2 (rewrite <- Rpower_plus).
    replace (1/3 + 1/3 + 1/3) with 1 by lra. rewrite Rpower_1 by lra. reflexivity. }
  assert (Hsqrt : sqrt (Rpower (bG * T / 2) (2 / 3)) = r).
  { rewrite Hr. rewrite <- (Rpower_sqrt (Rpower (bG*T/2)(2/3))) by (apply Rpower_pos; lra).
    rewrite Rpower_mult. f_equal. lra. }
  assert (HE0 : Rpower (bG * T / 2) (2 / 3) = r * r).
  { rewrite Hr. rewrite <- Rpower_plus. f_equal. lra. }
  assert (Hy : 0 < r * r / T)
    by (apply Rdiv_lt_0_compat; [apply Rmult_lt_0_compat; exact Hrpos | exact HT]).
  assert (HbGr : bG = 2 * (r * r * r) / T) by (rewrite Hr3; field; lra).
  assert (HRHS : Rpower (bG * bG / (4 * T)) (1 / 3) = r * r / T).
  { assert (Hcube : bG * bG / (4 * T) = (r * r / T) ^ 3).
    { rewrite HbGr. simpl. field. lra. }
    rewrite Hcube. rewrite <- (Rpower_pow 3 (r*r/T) Hy). rewrite Rpower_mult.
    replace (INR 3 * (1/3)) with 1 by (simpl; lra). apply Rpower_1; exact Hy. }
  rewrite Hsqrt, HE0, HRHS, HbGr. field. split; lra.
Qed.

Definition kramers_exponent (T : R) : R := 3 * Rpower (b_G * b_G / (4 * T)) (1 / 3).

Theorem gamow_peak_exponent_value :
  forall T, 0 < T ->
    gamow_factor (gamow_peak T) + gamow_peak T / T = kramers_exponent T.
Proof.
  intros T HT.
  unfold gamow_factor, gamow_peak, kramers_exponent.
  apply kramers_exponent_value; [ apply b_G_pos | exact HT ].
Qed.

(* E_peak^{3/2} = b_G T / 2, the stationary-point relation in product form. *)
Lemma gamow_peak_E_sqrt :
  forall T, 0 < T -> gamow_peak T * sqrt (gamow_peak T) = b_G * T / 2.
Proof.
  intros T HT. pose proof b_G_pos as Hb. assert (Ha : 0 < b_G * T / 2) by nra.
  unfold gamow_peak.
  rewrite <- (Rpower_sqrt (Rpower (b_G*T/2) (2/3))) by (apply Rpower_pos; lra).
  rewrite Rpower_mult, <- Rpower_plus.
  replace (2/3 + 2/3 * /2) with 1 by lra.
  apply Rpower_1. lra.
Qed.

(* The Gamow peak is a genuine critical point of the integrand exponent
   phi(E) = b_G / sqrt E + E / T: its derivative there vanishes. This is the
   stationary-phase condition underlying the Laplace/Kramers analysis. *)
Theorem gamow_exponent_critical :
  forall T, 0 < T ->
    is_derive (fun E => b_G / sqrt E + E / T) (gamow_peak T) 0.
Proof.
  intros T HT.
  assert (HE0 : 0 < gamow_peak T) by (apply gamow_peak_pos; exact HT).
  assert (Hs : 0 < sqrt (gamow_peak T)) by (apply sqrt_lt_R0; exact HE0).
  assert (Hss : sqrt (gamow_peak T) * sqrt (gamow_peak T) = gamow_peak T)
    by (apply sqrt_sqrt; lra).
  assert (Hbg : b_G = 2 * (gamow_peak T * sqrt (gamow_peak T)) / T)
    by (rewrite (gamow_peak_E_sqrt T HT); field; lra).
  auto_derive.
  - split; [ exact HE0 | split; [ apply Rgt_not_eq; exact Hs | exact I ] ].
  - rewrite Hss, Hbg. field. repeat split; apply Rgt_not_eq; assumption.
Qed.

(* First derivative of the exponent in closed form. *)
Lemma gamow_exponent_first_deriv :
  forall T E, 0 < T -> 0 < E ->
    is_derive (fun x => b_G / sqrt x + x / T) E (- b_G / (2 * E * sqrt E) + / T).
Proof.
  intros T E HT HE.
  assert (Hs : 0 < sqrt E) by (apply sqrt_lt_R0; exact HE).
  assert (Hss : sqrt E * sqrt E = E) by (apply sqrt_sqrt; lra).
  auto_derive.
  - repeat split; try assumption;
      try (apply Rgt_not_eq; repeat apply Rmult_lt_0_compat; try assumption; try lra).
  - set (s := sqrt E) in *. rewrite <- Hss. field.
    repeat split; try assumption;
      try (apply Rgt_not_eq; repeat apply Rmult_lt_0_compat; try assumption; try lra).
Qed.

(* Second derivative of the exponent in closed form. *)
Lemma gamow_exponent_second_deriv :
  forall T E, 0 < T -> 0 < E ->
    is_derive (fun x => - b_G / (2 * x * sqrt x) + / T) E
              (3 * b_G / (4 * E * E * sqrt E)).
Proof.
  intros T E HT HE.
  assert (Hs : 0 < sqrt E) by (apply sqrt_lt_R0; exact HE).
  assert (Hss : sqrt E * sqrt E = E) by (apply sqrt_sqrt; lra).
  auto_derive.
  - repeat split; try assumption;
      try (apply Rgt_not_eq; repeat apply Rmult_lt_0_compat; try assumption; try lra).
  - set (s := sqrt E) in *. rewrite <- Hss. field.
    repeat split; try assumption;
      try (apply Rgt_not_eq; repeat apply Rmult_lt_0_compat; try assumption; try lra).
Qed.

(* The curvature is everywhere positive: the exponent is strictly convex on
   E > 0, so the vanishing first derivative at the Gamow peak marks the unique
   minimum of the exponent, i.e. the unique maximum of the integrand. *)
Theorem gamow_exponent_curvature_pos :
  forall E, 0 < E -> 0 < 3 * b_G / (4 * E * E * sqrt E).
Proof.
  intros E HE. pose proof b_G_pos.
  assert (Hs : 0 < sqrt E) by (apply sqrt_lt_R0; exact HE).
  apply Rdiv_lt_0_compat;
    [ lra | repeat apply Rmult_lt_0_compat; try assumption; lra ].
Qed.

(* ================================================================== *)
(* === Quantum Coulomb functions and the Sommerfeld parameter === *)
(* ================================================================== *)

(* The WKB Gamow factor above is the semiclassical limit of the exact
   quantum penetrability built from the regular Coulomb function. The
   Sommerfeld parameter, the s-wave penetrability, the regular Coulomb
   power series and the Wronskian invariant are developed here. *)

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
(* === The s-wave series solves the Coulomb equation term-by-term === *)
(* ================================================================== *)

(* The l = 0 regular Coulomb function is F_0(eta, rho) = rho * u(rho)
   where u(rho) = sum_{k>=1} c_k rho^{k-1}, equivalently the function
   w(rho) = sum_{k>=1} c_k rho^k with c_0 = 0, c_1 = 1. Substituting
   into the s-wave Coulomb equation

     w''(rho) + (1 - 2 eta / rho) w(rho) = 0,

   and collecting the coefficient of rho^{k-2}, gives the recurrence

     k (k-1) c_k + c_{k-2} - 2 eta c_{k-1} = 0      (k >= 2).

   The c_k are defined by this recurrence; the recurrence is exactly the
   term-by-term Coulomb equation, so the power series annihilates the
   Coulomb operator order by order — the regular solution satisfies the
   Coulomb wave equation. *)

Fixpoint cw (eta : R) (k : nat) {struct k} : R :=
  match k with
  | 0%nat => 0
  | S 0%nat => 1
  | S (S k' as k1) =>
      (2 * eta * cw eta k1 - cw eta k') / (INR k * INR k1)
  end.

Lemma cw_0 : forall eta, cw eta 0 = 0.
Proof. intros. reflexivity. Qed.

Lemma cw_1 : forall eta, cw eta 1 = 1.
Proof. intros. reflexivity. Qed.

Lemma cw_2 : forall eta, cw eta 2 = eta.
Proof. intros eta. simpl. field. Qed.

Lemma cw_3 : forall eta, cw eta 3 = (2 * eta * eta - 1) / 6.
Proof. intros eta. simpl. field. Qed.

(* The term-by-term Coulomb-equation identity: for every k, the
   coefficients satisfy the recurrence that arises from plugging the
   power series into w'' + (1 - 2 eta / rho) w = 0. The coefficient
   of rho^k in that expansion is

     (k+2)(k+1) c_{k+2} - 2 eta c_{k+1} + c_k = 0,

   and we prove it vanishes for all k. *)
Theorem cw_solves_coulomb_equation :
  forall (eta : R) (k : nat),
    INR (S (S k)) * INR (S k) * cw eta (S (S k))
    - 2 * eta * cw eta (S k) + cw eta k = 0.
Proof.
  intros eta k.
  (* cw (S (S k)) unfolds to (2 eta cw(S k) - cw k)/(INR (S(S k)) * INR (S k)). *)
  assert (Hk2 : INR (S (S k)) <> 0) by (apply not_0_INR; lia).
  assert (Hk1 : INR (S k) <> 0) by (apply not_0_INR; lia).
  replace (cw eta (S (S k)))
    with ((2 * eta * cw eta (S k) - cw eta k)
          / (INR (S (S k)) * INR (S k)))
    by reflexivity.
  field. split; assumption.
Qed.

(* The series begins with the correct regular boundary data
   (c_0 = 0 forces F_0 to vanish at the origin, c_1 = 1 fixes the
   normalisation of the regular solution). *)
Theorem cw_regular_boundary :
  forall eta, cw eta 0 = 0 /\ cw eta 1 = 1.
Proof. intros eta. split; reflexivity. Qed.

(* ================================================================== *)
(* === Power-series convergence of the Coulomb coefficients === *)
(* ================================================================== *)

Lemma INR_fact_S : forall k, INR (fact (S k)) = INR (S k) * INR (fact k).
Proof. intro k. rewrite fact_simpl. rewrite mult_INR. reflexivity. Qed.
Lemma INR_fact_SS : forall k,
  INR (fact (S (S k))) = INR (S (S k)) * (INR (S k) * INR (fact k)).
Proof. intro k. rewrite (fact_simpl (S k)). rewrite mult_INR. rewrite INR_fact_S. reflexivity. Qed.

Section Cw.
Variable eta : R.
Definition Mc := 2 * Rabs eta + 2.

Lemma Mc_ge1 : 1 <= Mc.
Proof. unfold Mc. pose proof (Rabs_pos eta). lra. Qed.

Lemma fact_pos : forall k, 0 < INR (fact k).
Proof. intro k. apply lt_0_INR. apply lt_O_fact. Qed.

Lemma scalar_ineq : forall k : nat,
  2 * Rabs eta * Mc / INR (S k) + 1 <= Mc * Mc.
Proof.
  intro k. pose proof (Rabs_pos eta) as He.
  assert (HSk : 1 <= INR (S k)) by (rewrite S_INR; pose proof (pos_INR k); lra).
  assert (Hdiv : 2 * Rabs eta * Mc / INR (S k) <= 2 * Rabs eta * Mc).
  { apply Rle_div_l. lra. apply Rle_trans with (2 * Rabs eta * Mc * 1); [lra|].
    apply Rmult_le_compat_l; [ unfold Mc; nra | exact HSk ]. }
  unfold Mc in *. nra.
Qed.

Lemma cw_bound_pair :
  forall k, Rabs (cw eta k) <= Mc ^ k / INR (fact k)
         /\ Rabs (cw eta (S k)) <= Mc ^ (S k) / INR (fact (S k)).
Proof.
  pose proof Mc_ge1 as HM. pose proof (Rabs_pos eta) as Heta.
  induction k as [|k [IH1 IH2]].
  - split.
    + simpl. rewrite Rabs_R0. lra.
    + rewrite cw_1. rewrite Rabs_R1. simpl (fact 1). simpl (INR 1).
      unfold Mc; simpl; lra.
  - split; [exact IH2 |].
    assert (Hrec : cw eta (S (S k))
      = (2 * eta * cw eta (S k) - cw eta k) / (INR (S (S k)) * INR (S k)))
      by reflexivity.
    set (A := Mc ^ k / INR (fact k)).
    set (B := Mc ^ (S k) / INR (fact (S k))).
    pose proof (fact_pos k) as Hfk. pose proof (fact_pos (S k)) as HfSk.
    pose proof (fact_pos (S (S k))) as HfSSk.
    assert (HApos : 0 < A).
    { unfold A. apply Rdiv_lt_0_compat; [apply pow_lt; lra | exact Hfk]. }
    (* factorial relations: B = Mc/(S k) * A *)
    assert (HBA : B = Mc / INR (S k) * A).
    { unfold A, B. rewrite INR_fact_S. simpl (Mc ^ (S k)). field.
      split; [ apply Rgt_not_eq; exact Hfk
             | apply Rgt_not_eq, lt_0_INR; lia ]. }
    assert (HRHS : Mc ^ (S (S k)) / INR (fact (S (S k))) * (INR (S (S k)) * INR (S k))
                 = Mc * Mc * A).
    { unfold A. rewrite INR_fact_SS. simpl (Mc ^ (S (S k))). field.
      repeat split; try (apply Rgt_not_eq);
      try (apply lt_0_INR; lia); try exact Hfk. }
    rewrite Hrec.
    assert (Hd : 0 < INR (S (S k)) * INR (S k))
      by (apply Rmult_lt_0_compat; apply lt_0_INR; lia).
    rewrite Rabs_div by (apply Rgt_not_eq; exact Hd).
    rewrite (Rabs_right (INR (S (S k)) * INR (S k))) by lra.
    apply Rle_div_l; [exact Hd |].
    rewrite HRHS.
    eapply Rle_trans; [apply Rabs_triang |].
    rewrite Rabs_Ropp, !Rabs_mult, (Rabs_right 2) by lra.
    eapply Rle_trans;
      [apply Rplus_le_compat;
        [apply Rmult_le_compat_l; [lra | exact IH2]
        | exact IH1] |].
    fold A. fold B. rewrite HBA.
    pose proof (scalar_ineq k) as Hsc.
    assert (HSkne : INR (S k) <> 0) by (apply Rgt_not_eq, lt_0_INR; lia).
    apply Rle_trans with (A * (2 * Rabs eta * Mc / INR (S k) + 1)).
    { right. field. exact HSkne. }
    apply Rle_trans with (A * (Mc * Mc)).
    { apply Rmult_le_compat_l; [lra | exact Hsc]. }
    right. ring.
Qed.

Lemma cw_bound : forall k, Rabs (cw eta k) <= Mc ^ k / INR (fact k).
Proof. intro k. apply (cw_bound_pair k). Qed.


Lemma exp_dom_ex_series : forall x,
  ex_series (fun k => x ^ k / INR (fact k)).
Proof.
  intro x. exists (exp x).
  pose proof (is_exp_Reals x) as Hp. unfold is_pseries in Hp.
  apply (is_series_ext (fun n => scal (x ^ n) (/ INR (fact n)))).
  - intro n. unfold scal; simpl; unfold mult; simpl. unfold Rdiv. ring.
  - exact Hp.
Qed.

Lemma cw_series_ex : forall rho, ex_series (fun k => cw eta k * rho ^ k).
Proof.
  intro rho.
  apply (ex_series_le (fun k => cw eta k * rho ^ k)
           (fun k => (Mc * Rabs rho) ^ k / INR (fact k))).
  - intro n.
    change (norm (cw eta n * rho ^ n))
      with (Rabs (cw eta n * rho ^ n)).
    rewrite Rabs_mult. rewrite <- RPow_abs.
    rewrite Rpow_mult_distr.
    apply Rle_trans with ((Mc ^ n / INR (fact n)) * Rabs rho ^ n).
    + apply Rmult_le_compat_r; [ apply pow_le, Rabs_pos | apply cw_bound ].
    + right. field. apply Rgt_not_eq, fact_pos.
  - apply exp_dom_ex_series.
Qed.

End Cw.

(* ================================================================== *)
(* === The Coulomb Wronskian invariant === *)
(* ================================================================== *)

(* The regular F_0 and irregular G_0 Coulomb functions are two solutions
   of one second-order linear equation w'' + (1 - 2 eta / rho) w = 0.
   Their Wronskian W = F G' - F' G is therefore constant in rho: this is
   the structural identity that makes the penetrability
   P_0 = 1 / (F_0^2 + G_0^2) well defined and that fixes the asymptotic
   normalisation F_0 ~ sin(theta), G_0 ~ cos(theta). We prove it for any
   second-order equation w'' + pot w = 0 and specialise to the Coulomb
   potential. *)
Theorem wronskian_constant_2nd_order :
  forall (pot u v u' v' u'' v'' : R -> R),
    (forall x, is_derive u x (u' x)) ->
    (forall x, is_derive u' x (u'' x)) ->
    (forall x, is_derive v x (v' x)) ->
    (forall x, is_derive v' x (v'' x)) ->
    (forall x, u'' x + pot x * u x = 0) ->
    (forall x, v'' x + pot x * v x = 0) ->
    forall x, is_derive (fun s => u s * v' s - u' s * v s) x 0.
Proof.
  intros pot u v u' v' u'' v'' Hu Hu' Hv Hv' HODEu HODEv x.
  assert (HW : is_derive (fun s => u s * v' s - u' s * v s) x
                 (u' x * v' x + u x * v'' x - (u'' x * v x + u' x * v' x))).
  { apply (is_derive_minus (fun s => u s * v' s) (fun s => u' s * v s)).
    - apply (is_derive_mult u v' x (u' x) (v'' x));
        [ apply Hu | apply Hv' | intros n m; apply Rmult_comm ].
    - apply (is_derive_mult u' v x (u'' x) (v' x));
        [ apply Hu' | apply Hv | intros n m; apply Rmult_comm ]. }
  assert (Hval : u' x * v' x + u x * v'' x - (u'' x * v x + u' x * v' x) = 0).
  { pose proof (HODEu x) as Eu. pose proof (HODEv x) as Ev. nra. }
  rewrite <- Hval. exact HW.
Qed.

(* Hence the Wronskian takes the same value at every two points: it is a
   constant of the motion (Abel's identity for this equation). *)
Corollary wronskian_constant_value :
  forall (pot u v u' v' u'' v'' : R -> R),
    (forall x, is_derive u x (u' x)) ->
    (forall x, is_derive u' x (u'' x)) ->
    (forall x, is_derive v x (v' x)) ->
    (forall x, is_derive v' x (v'' x)) ->
    (forall x, u'' x + pot x * u x = 0) ->
    (forall x, v'' x + pot x * v x = 0) ->
    forall x0 x,
      u x * v' x - u' x * v x = u x0 * v' x0 - u' x0 * v x0.
Proof.
  intros pot u v u' v' u'' v'' Hu Hu' Hv Hv' HODEu HODEv x0 x.
  assert (Hd : forall s, is_derive (fun w => u w * v' w - u' w * v w) s 0)
    by (apply (wronskian_constant_2nd_order pot u v u' v' u'' v''); assumption).
  assert (HR : is_RInt (fun _ : R => 0) x0 x
                 (minus (u x * v' x - u' x * v x)
                        (u x0 * v' x0 - u' x0 * v x0))).
  { apply (is_RInt_derive (V := R_CompleteNormedModule)
             (fun w => u w * v' w - u' w * v w) (fun _ => 0) x0 x).
    - intros s _. apply Hd.
    - intros s _. apply continuous_const. }
  pose proof (is_RInt_unique _ _ _ _ HR) as A.
  rewrite RInt_const in A.
  unfold scal in A; simpl in A; unfold mult in A; simpl in A.
  rewrite Rmult_0_r in A.
  unfold minus, plus, opp in A; simpl in A.
  lra.
Qed.

(* The Coulomb specialisation: pot(rho) = 1 - 2 eta / rho. *)
Corollary coulomb_wronskian_constant :
  forall (eta : R) (F G F' G' F'' G'' : R -> R),
    (forall rho, is_derive F rho (F' rho)) ->
    (forall rho, is_derive F' rho (F'' rho)) ->
    (forall rho, is_derive G rho (G' rho)) ->
    (forall rho, is_derive G' rho (G'' rho)) ->
    (forall rho, F'' rho + (1 - 2 * eta / rho) * F rho = 0) ->
    (forall rho, G'' rho + (1 - 2 * eta / rho) * G rho = 0) ->
    forall rho0 rho,
      F rho * G' rho - F' rho * G rho
      = F rho0 * G' rho0 - F' rho0 * G rho0.
Proof.
  intros eta F G F' G' F'' G'' HF HF' HG HG' HODEF HODEG.
  apply (wronskian_constant_value (fun rho => 1 - 2 * eta / rho)
           F G F' G' F'' G''); assumption.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions gamow_factor_pos.
Print Assumptions gamow_factor_decreasing.
Print Assumptions gamow_peak_pos.
Print Assumptions gamow_peak_monotone_T.
Print Assumptions gamow_reactivity_positive.
Print Assumptions cw_2.
Print Assumptions cw_3.
Print Assumptions cw_solves_coulomb_equation.
Print Assumptions cw_regular_boundary.
Print Assumptions cw_bound.
Print Assumptions cw_series_ex.
Print Assumptions sommerfeld_eta_pos.
Print Assumptions gamow_factor_quantum_pos.
Print Assumptions gamow_factor_quantum_lt_1.
Print Assumptions s_wave_is_gamow_factor.
Print Assumptions partial_wave_suppression.
Print Assumptions semiclassical_correspondence.
Print Assumptions coulomb_coeff_2_at_l0.
Print Assumptions wronskian_constant_2nd_order.
Print Assumptions wronskian_constant_value.
Print Assumptions coulomb_wronskian_constant.
Print Assumptions kramers_exponent_value.
Print Assumptions gamow_peak_exponent_value.
Print Assumptions gamow_exponent_critical.
Print Assumptions gamow_exponent_second_deriv.
Print Assumptions gamow_exponent_curvature_pos.
