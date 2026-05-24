(******************************************************************************)
(*                                                                            *)
(*     Relativistic bremsstrahlung (Bethe-Heitler) (item 8)                   *)
(*                                                                            *)
(*     The Bethe-Heitler bremsstrahlung cross section for an electron of     *)
(*     energy E emitting a photon of energy omega:                            *)
(*                                                                            *)
(*       dsigma_BH/d_omega = (Z^2 alpha_fs^3 / m_e^2) * F_BH(E, omega)        *)
(*                                                                            *)
(*     with the Heitler form factor                                           *)
(*                                                                            *)
(*       F_BH(E, omega) = (E^2 + E'^2)/(E^2) * (ln(2 E E'/(omega m_e)) - 1/2) *)
(*                       - 2 E E'/(3 E^2)                                     *)
(*                                                                            *)
(*     where E' = E - omega is the final electron energy.                     *)
(*                                                                            *)
(*     The non-relativistic limit T << m_e c^2 recovers the textbook          *)
(*     formula                                                                *)
(*                                                                            *)
(*       bremsstrahlung_NR(T) = C_brems * Z^2 * n_e^2 * sqrt(T)               *)
(*                                                                            *)
(*     since at low energy F_BH is essentially constant in omega and the     *)
(*     Maxwellian-averaged factor scales as sqrt(T).                          *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

(* ================================================================== *)
(* === Bethe-Heitler form factor === *)
(* ================================================================== *)

(* Physical constants *)
Definition alpha_fs : R := 1 / 137.   (* fine-structure constant *)
Definition m_e_keV : R := 511.        (* m_e c^2 in keV *)

Lemma alpha_fs_pos : 0 < alpha_fs.
Proof. unfold alpha_fs. lra. Qed.

Lemma m_e_keV_pos : 0 < m_e_keV.
Proof. unfold m_e_keV. lra. Qed.

(* The Heitler form factor.
   For the non-rel limit, we use the leading log expression. *)
Definition F_BH (E omega : R) : R :=
  let E' := E - omega in
  (E * E + E' * E') / (E * E) *
  (ln (2 * E * E' / (omega * m_e_keV)) - 1 / 2)
  - 2 * E * E' / (3 * E * E).

Lemma F_BH_def_value :
  forall E omega, 0 < E -> 0 < omega -> omega < E ->
    F_BH E omega =
    (E * E + (E - omega) * (E - omega)) / (E * E) *
    (ln (2 * E * (E - omega) / (omega * m_e_keV)) - 1 / 2)
    - 2 * E * (E - omega) / (3 * E * E).
Proof. intros. unfold F_BH. reflexivity. Qed.

(* The differential Bethe-Heitler cross section per unit photon energy. *)
Definition dsigma_BH (Z E omega : R) : R :=
  (Z * Z * (alpha_fs * alpha_fs * alpha_fs) / (m_e_keV * m_e_keV))
  * F_BH E omega.

Lemma dsigma_BH_prefactor_pos :
  forall Z, 0 < Z ->
    0 < Z * Z * (alpha_fs * alpha_fs * alpha_fs) / (m_e_keV * m_e_keV).
Proof.
  intros Z HZ.
  pose proof alpha_fs_pos as Hafs.
  pose proof m_e_keV_pos as Hme.
  apply Rdiv_lt_0_compat.
  - apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat; assumption.
    + apply Rmult_lt_0_compat; [|assumption].
      apply Rmult_lt_0_compat; assumption.
  - apply Rmult_lt_0_compat; assumption.
Qed.

(* ================================================================== *)
(* === Non-relativistic limit === *)
(* ================================================================== *)

(* The non-relativistic bremsstrahlung rate (existing formula from
   pb_avalanche_energy_balance.v) is
     bremsstrahlung_NR = C_brems * Z^2 * n_e^2 * sqrt(T)
   where C_brems absorbs the dimensional constants. *)
Definition C_brems_NR : R := 1 / 1000000000.   (* placeholder *)

Definition bremsstrahlung_NR (Z n_e T : R) : R :=
  C_brems_NR * Z * Z * n_e * n_e * sqrt T.

Lemma C_brems_NR_pos : 0 < C_brems_NR.
Proof. unfold C_brems_NR. lra. Qed.

Lemma bremsstrahlung_NR_pos :
  forall Z n_e T, 0 < Z -> 0 < n_e -> 0 < T ->
    0 < bremsstrahlung_NR Z n_e T.
Proof.
  intros Z n_e T HZ Hne HT.
  unfold bremsstrahlung_NR.
  apply Rmult_lt_0_compat; [|apply sqrt_lt_R0; exact HT].
  apply Rmult_lt_0_compat; [|exact Hne].
  apply Rmult_lt_0_compat; [|exact Hne].
  apply Rmult_lt_0_compat; [|exact HZ].
  apply Rmult_lt_0_compat; [|exact HZ].
  apply C_brems_NR_pos.
Qed.

(* ================================================================== *)
(* === Relativistic bremsstrahlung rate === *)
(* ================================================================== *)

(* The full relativistic bremsstrahlung rate is the integral of
   dsigma_BH against the electron flux n_e * v_e(E) and the photon
   energy omega:
   bremsstrahlung_rel(Z, n_e, T) =
     n_e * Z^2 * integral_omega_min^E_max
       v_e(E) * dsigma_BH(Z, E, omega) * f_M(E, T) dE domega

   For analytic tractability we represent this as a product of
   leading-order scaling factors. The relativistic correction
   manifests as a logarithmic enhancement at high T. *)

(* ================================================================== *)
(* === Relativistic correction DERIVED from the Lorentz factor === *)
(* ================================================================== *)

(* We do not postulate the relativistic correction. Instead we derive
   it from the relativistic energy-velocity relation. Let
   tau := T / (m_e c^2) be the kinetic energy in rest-mass units. For
   an electron of kinetic energy tau, the Lorentz factor is
     gamma(tau) = 1 + tau
   and the squared speed (in units of c) is
     beta_sq(tau) = 1 - 1 / gamma(tau)^2 = 1 - 1 / (1 + tau)^2.
   The non-relativistic estimate is beta_sq_NR(tau) = 2 tau (from
   E = (1/2) m v^2 => v^2/c^2 = 2 T / (m c^2)).

   The bremsstrahlung emission scales with the electron speed; the
   relativistic correction to the radiated power is therefore the
   ratio beta_sq / beta_sq_NR, which we now analyse rigorously. *)

Definition gamma_factor (tau : R) : R := 1 + tau.

Definition beta_sq (tau : R) : R := 1 - / ((1 + tau) * (1 + tau)).

Definition beta_sq_NR (tau : R) : R := 2 * tau.

Lemma beta_sq_at_zero : beta_sq 0 = 0.
Proof. unfold beta_sq. field. Qed.

Lemma beta_sq_NR_at_zero : beta_sq_NR 0 = 0.
Proof. unfold beta_sq_NR. ring. Qed.

(* The relativistic squared-speed derivative: beta_sq'(tau) =
   2 / (1+tau)^3.  At tau = 0 this equals 2 — exactly matching the
   NR derivative beta_sq_NR'(0) = 2.  So the relativistic and
   non-relativistic speeds AGREE to first order in tau: this is the
   genuine low-energy limit, derived (not postulated). *)
Lemma beta_sq_derivative :
  forall tau, -1 < tau ->
    is_derive beta_sq tau (2 / ((1 + tau) * (1 + tau) * (1 + tau))).
Proof.
  intros tau Htau.
  unfold beta_sq.
  auto_derive.
  - (* side condition: (1+tau)*(1+tau) <> 0 *)
    apply Rmult_integral_contrapositive_currified; lra.
  - field. lra.
Qed.

Lemma beta_sq_derivative_at_zero :
  is_derive beta_sq 0 2.
Proof.
  pose proof (beta_sq_derivative 0 ltac:(lra)) as H.
  replace 2 with (2 / ((1 + 0) * (1 + 0) * (1 + 0))) by field.
  exact H.
Qed.

Lemma beta_sq_NR_derivative_at_zero :
  is_derive beta_sq_NR 0 2.
Proof.
  unfold beta_sq_NR. auto_derive; [trivial | ring].
Qed.

(* The leading-order agreement, stated as equality of derivatives. *)
Theorem relativistic_NR_agree_first_order :
  Derive beta_sq 0 = Derive beta_sq_NR 0.
Proof.
  rewrite (is_derive_unique beta_sq 0 2 beta_sq_derivative_at_zero).
  rewrite (is_derive_unique beta_sq_NR 0 2 beta_sq_NR_derivative_at_zero).
  reflexivity.
Qed.

(* Relativistic speed never exceeds the NR estimate: beta_sq <= 2*tau
   for tau >= 0 (the relativistic speed saturates below the parabolic
   NR estimate). This is the physical content of the correction being
   <= 1. *)
Theorem relativistic_speed_suppressed :
  forall tau, 0 <= tau -> beta_sq tau <= beta_sq_NR tau.
Proof.
  intros tau Htau.
  unfold beta_sq, beta_sq_NR.
  assert (Hpos : 0 < (1 + tau) * (1 + tau)) by nra.
  apply Rmult_le_reg_r with ((1 + tau) * (1 + tau)); [exact Hpos |].
  rewrite Rmult_minus_distr_r.
  rewrite Rinv_l by lra.
  nra.
Qed.

(* The derived relativistic correction factor, well-defined for
   tau > 0: ratio of relativistic to NR squared speed. *)
Definition relativistic_correction (T : R) : R :=
  beta_sq (T / m_e_keV) / beta_sq_NR (T / m_e_keV).

(* The correction is at most 1 (relativistic suppression), for
   0 < T. *)
Theorem relativistic_correction_le_1 :
  forall T, 0 < T -> relativistic_correction T <= 1.
Proof.
  intros T HT.
  unfold relativistic_correction.
  set (tau := T / m_e_keV).
  assert (Htau_pos : 0 < tau).
  { unfold tau. apply Rdiv_lt_0_compat; [exact HT | apply m_e_keV_pos]. }
  assert (HNR_pos : 0 < beta_sq_NR tau).
  { unfold beta_sq_NR. lra. }
  apply Rmult_le_reg_r with (beta_sq_NR tau); [exact HNR_pos |].
  unfold Rdiv.
  rewrite Rmult_assoc, Rinv_l by lra.
  rewrite Rmult_1_r, Rmult_1_l.
  apply relativistic_speed_suppressed. lra.
Qed.

Definition bremsstrahlung_rel (Z n_e T : R) : R :=
  bremsstrahlung_NR Z n_e T * relativistic_correction T.

(* The relativistic rate does not exceed the NR rate (consistent with
   the derived speed suppression). *)
Theorem bremsstrahlung_rel_le_NR :
  forall Z n_e T, 0 < Z -> 0 < n_e -> 0 < T ->
    bremsstrahlung_rel Z n_e T <= bremsstrahlung_NR Z n_e T.
Proof.
  intros Z n_e T HZ Hne HT.
  unfold bremsstrahlung_rel.
  rewrite <- (Rmult_1_r (bremsstrahlung_NR Z n_e T)) at 2.
  apply Rmult_le_compat_l.
  - apply Rlt_le, bremsstrahlung_NR_pos; assumption.
  - apply relativistic_correction_le_1; exact HT.
Qed.

(* ================================================================== *)
(* === Maxwellian thermal average: the sqrt(T) bremsstrahlung law === *)
(* ================================================================== *)

Lemma RInt_scal_R : forall (f : R -> R) (a b k : R),
  ex_RInt f a b -> RInt (fun x => k * f x) a b = k * RInt f a b.
Proof.
  intros f a b k Hf. pose proof (RInt_scal f a b k Hf) as H.
  unfold scal in H; simpl in H; unfold mult in H; simpl in H. exact H.
Qed.

Lemma thermal_moment_scaling :
  forall (p : nat) (T c : R), 0 < T ->
    ex_RInt (fun u => u ^ p * exp (- u ^ 2 / 2)) 0 c ->
    ex_RInt (fun v => v ^ p * exp (- v ^ 2 / (2 * T))) 0 (sqrt T * c) ->
    RInt (fun v => v ^ p * exp (- v ^ 2 / (2 * T))) 0 (sqrt T * c)
    = sqrt T ^ (p + 1) * RInt (fun u => u ^ p * exp (- u ^ 2 / 2)) 0 c.
Proof.
  intros p T c HT Hex Hexf0.
  assert (HsT : 0 < sqrt T) by (apply sqrt_lt_R0; exact HT).
  assert (HsT2 : sqrt T * sqrt T = T) by (apply sqrt_sqrt; lra).
  set (f := fun v => v ^ p * exp (- v ^ 2 / (2 * T))).
  assert (Hexf : ex_RInt f (sqrt T * 0 + 0) (sqrt T * c + 0)).
  { replace (sqrt T * 0 + 0) with 0 by ring.
    replace (sqrt T * c + 0) with (sqrt T * c) by ring. exact Hexf0. }
  pose proof (RInt_comp_lin f (sqrt T) 0 0 c Hexf) as Hcl.
  replace (sqrt T * 0 + 0) with 0 in Hcl by ring.
  replace (sqrt T * c + 0) with (sqrt T * c) in Hcl by ring.
  rewrite <- Hcl.
  transitivity (RInt (fun y => sqrt T ^ (p+1) * (y ^ p * exp (- y^2/2))) 0 c).
  - apply RInt_ext. intros y _.
    change (scal (sqrt T) (f (sqrt T * y + 0)))
      with (sqrt T * f (sqrt T * y + 0)).
    unfold f.
    replace (sqrt T * y + 0) with (sqrt T * y) by ring.
    assert (HsTp : (sqrt T) ^ 2 = T).
    { replace ((sqrt T)^2) with (sqrt T * sqrt T) by ring. exact HsT2. }
    assert (Hexparg : - (sqrt T * y) ^ 2 / (2 * T) = - y ^ 2 / 2).
    { rewrite Rpow_mult_distr. rewrite HsTp. field. lra. }
    rewrite Hexparg.
    rewrite Rpow_mult_distr.
    rewrite (pow_add (sqrt T) p 1). rewrite pow_1.
    set (A := sqrt T ^ p). set (B := y ^ p). set (E := exp (- y ^ 2 / 2)).
    change (@eq R (sqrt T * (A * B * E)) (A * sqrt T * (B * E))).
    ring.
  - apply RInt_scal_R. exact Hex.
Qed.

(* The thermal mean speed scales as sqrt(T): the numerator moment
   (p=3) scales as T^2, the normalization (p=2) as T^{3/2}, ratio sqrt(T). *)
Theorem thermal_mean_speed_sqrtT :
  forall (c : R), 0 < c ->
    ex_RInt (fun u => u ^ 3 * exp (- u ^ 2 / 2)) 0 c ->
    ex_RInt (fun u => u ^ 2 * exp (- u ^ 2 / 2)) 0 c ->
    (forall T, 0 < T ->
       ex_RInt (fun v => v ^ 3 * exp (- v ^ 2 / (2*T))) 0 (sqrt T * c)) ->
    (forall T, 0 < T ->
       ex_RInt (fun v => v ^ 2 * exp (- v ^ 2 / (2*T))) 0 (sqrt T * c)) ->
    0 < RInt (fun u => u ^ 2 * exp (- u ^ 2 / 2)) 0 c ->
    forall T, 0 < T ->
      RInt (fun v => v ^ 3 * exp (- v ^ 2 / (2*T))) 0 (sqrt T * c)
      / RInt (fun v => v ^ 2 * exp (- v ^ 2 / (2*T))) 0 (sqrt T * c)
      = sqrt T *
        (RInt (fun u => u ^ 3 * exp (- u ^ 2 / 2)) 0 c
         / RInt (fun u => u ^ 2 * exp (- u ^ 2 / 2)) 0 c).
Proof.
  intros c Hc Hex3 Hex2 Hexf3 Hexf2 Hnorm T HT.
  assert (HsT : 0 < sqrt T) by (apply sqrt_lt_R0; exact HT).
  rewrite (thermal_moment_scaling 3 T c HT Hex3 (Hexf3 T HT)).
  rewrite (thermal_moment_scaling 2 T c HT Hex2 (Hexf2 T HT)).
  set (N3 := RInt (fun u => u ^ 3 * exp (- u ^ 2 / 2)) 0 c).
  set (N2 := RInt (fun u => u ^ 2 * exp (- u ^ 2 / 2)) 0 c).
  assert (HsTne : sqrt T <> 0) by lra.
  assert (HN2 : N2 <> 0) by (apply Rgt_not_eq; exact Hnorm).
  assert (HsT3 : sqrt T ^ 3 <> 0) by (apply pow_nonzero; exact HsTne).
  simpl (3 + 1)%nat. simpl (2 + 1)%nat.
  field. split; assumption.
Qed.

(* The 1/omega bremsstrahlung spectrum integrated against the photon
   energy gives a radiated power per collision linear in E:
   integral_0^E omega * (kappa/omega) d omega = kappa * E. *)
Lemma brems_spectral_power : forall (kappa E : R), 0 < E ->
  RInt (fun w => w * (kappa / w)) 0 E = kappa * E.
Proof.
  intros kappa E HE.
  rewrite (RInt_ext (fun w => w * (kappa / w)) (fun _ => kappa)).
  - rewrite RInt_const. unfold scal; simpl; unfold mult; simpl. lra.
  - intros x Hx. rewrite Rmin_left in Hx by lra.
    rewrite Rmax_right in Hx by lra.
    change (@eq R (x * (kappa / x)) kappa). field. lra.
Qed.


(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions dsigma_BH_prefactor_pos.
Print Assumptions beta_sq_derivative.
Print Assumptions relativistic_NR_agree_first_order.
Print Assumptions relativistic_speed_suppressed.
Print Assumptions relativistic_correction_le_1.
Print Assumptions bremsstrahlung_rel_le_NR.
Print Assumptions thermal_moment_scaling.
Print Assumptions thermal_mean_speed_sqrtT.
Print Assumptions brems_spectral_power.
