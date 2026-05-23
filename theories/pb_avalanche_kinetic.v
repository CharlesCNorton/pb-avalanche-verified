(******************************************************************************)
(*                                                                            *)
(*     Kinetic model: slowing-down spectrum, Fokker-Planck steady state,      *)
(*     and energy-resolved alpha-induced secondary fusion rate                *)
(*                                                                            *)
(*     This file lifts the abstract alpha-weighted velocity integral of       *)
(*     pb_avalanche.v to an energy-resolved kinetic theory:                   *)
(*                                                                            *)
(*       - f_slowing E := S * tau / E  on  [E_min, E_birth]                   *)
(*           (slowing-down spectrum from steady-state Fokker-Planck)          *)
(*       - alpha density n_alpha = integral of f_slowing on [E_min, E_birth]  *)
(*       - sigma_v_avg = integral(f sigma v) / integral(f)                    *)
(*       - R_secondary_kinetic = n_B * integral(f sigma v)                    *)
(*                                                                            *)
(*     The factorization                                                      *)
(*       R_secondary = n_alpha * n_B * sigma_v_avg                            *)
(*     is direct from the definitions. The steady-state identity              *)
(*       n_alpha = S * tau * ln(E_birth/E_min)                                *)
(*     (logarithmic kinematic factor from the 1/E shape) recovers             *)
(*       R_secondary = 3 * R_primary * tau * n_B * sigma_v_avg                *)
(*     when S = 3 * R_primary and the logarithmic factor is absorbed into     *)
(*     the normalization of sigma_v_avg.                                      *)
(*                                                                            *)
(*     The 1/E spectrum is integrable on [E_min, E_birth] (E_min > 0),        *)
(*     avoiding the singularity at E = 0; the truncation parameter E_min      *)
(*     becomes a physical input representing the thermal cutoff below which   *)
(*     alphas are no longer reactive.                                         *)
(*                                                                            *)
(*     Axiom footprint: results in this file carry, in addition to the three  *)
(*     Stdlib Dedekind-real axioms, the classical-logic axiom                 *)
(*     Classical_Prop.classic (excluded middle). It is pulled in by           *)
(*     Coquelicot's fundamental-theorem-of-calculus machinery                 *)
(*     (RInt_Derive / is_derive_ln) used to evaluate the integral of 1/E.     *)
(*     This is a standard consistent extension of CIC, not a project-local    *)
(*     assumption; no Admitted, no project-local axioms.                      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.

From PBAvalanche Require Import pb_avalanche pb_avalanche_integral.

Open Scope R_scope.

(* ================================================================== *)
(* === Kinetic-model parameter spec === *)
(* ================================================================== *)

Module Type KINETIC_MODEL_PARAMS.

  Parameter E_min : R.

  Axiom E_min_pos : 0 < E_min.
  Axiom E_min_lt_birth : E_min < E_alpha_birth_MeV.

  Parameter sigma_E : R -> R.
  Parameter v_E : R -> R.

  Axiom sigma_E_nonneg :
    forall E, E_min <= E <= E_alpha_birth_MeV -> 0 <= sigma_E E.
  Axiom v_E_nonneg :
    forall E, E_min <= E <= E_alpha_birth_MeV -> 0 <= v_E E.

  Parameter sigma_E_max : R.
  Parameter v_E_max : R.

  Axiom sigma_E_max_pos : 0 < sigma_E_max.
  Axiom v_E_max_pos : 0 < v_E_max.

  Axiom sigma_E_bound :
    forall E, E_min <= E <= E_alpha_birth_MeV -> sigma_E E <= sigma_E_max.
  Axiom v_E_bound :
    forall E, E_min <= E <= E_alpha_birth_MeV -> v_E E <= v_E_max.

  (* Lower bounds, for the two-sided sandwich on the figure of merit. *)
  Parameter sigma_E_min_val : R.
  Parameter v_E_min_val : R.

  Axiom sigma_E_min_nonneg : 0 <= sigma_E_min_val.
  Axiom v_E_min_nonneg : 0 <= v_E_min_val.

  Axiom sigma_E_lower :
    forall E, E_min <= E <= E_alpha_birth_MeV -> sigma_E_min_val <= sigma_E E.
  Axiom v_E_lower :
    forall E, E_min <= E <= E_alpha_birth_MeV -> v_E_min_val <= v_E E.

  Axiom sigma_E_continuous_on :
    forall E, E_min <= E <= E_alpha_birth_MeV -> continuous sigma_E E.
  Axiom v_E_continuous_on :
    forall E, E_min <= E <= E_alpha_birth_MeV -> continuous v_E E.

End KINETIC_MODEL_PARAMS.

(* ================================================================== *)
(* === Kinetic-model framework === *)
(* ================================================================== *)

Module KineticFramework (K : KINETIC_MODEL_PARAMS).
  Import K.

  Lemma E_alpha_birth_kinetic_pos : 0 < E_alpha_birth_MeV.
  Proof. unfold E_alpha_birth_MeV, Q_pB_MeV. lra. Qed.

  Lemma E_min_neq_zero : E_min <> 0.
  Proof. apply Rgt_not_eq. exact E_min_pos. Qed.

  Lemma E_min_le_birth : E_min <= E_alpha_birth_MeV.
  Proof. apply Rlt_le. exact E_min_lt_birth. Qed.

  (* --- The integral of 1/E from E_min to E_birth ---

     The classical anti-derivative result: the natural log is the
     antiderivative of 1/x on positive reals, so RInt of 1/E over
     [E_min, E_birth] equals ln(E_birth) - ln(E_min). *)

  Lemma RInt_inv_E :
    RInt (fun E : R => / E) E_min E_alpha_birth_MeV =
    ln E_alpha_birth_MeV - ln E_min.
  Proof.
    pose proof E_min_pos as HEmin.
    pose proof E_alpha_birth_kinetic_pos as HEbirth.
    pose proof E_min_le_birth as HleE.
    apply is_RInt_unique.
    pose proof (@is_RInt_derive R_CompleteNormedModule
                  ln (fun x : R => / x) E_min E_alpha_birth_MeV) as H.
    apply H.
    - intros x Hx.
      rewrite Rmin_left in Hx by exact HleE.
      rewrite Rmax_right in Hx by exact HleE.
      apply is_derive_ln. lra.
    - intros x Hx.
      rewrite Rmin_left in Hx by exact HleE.
      rewrite Rmax_right in Hx by exact HleE.
      apply continuous_Rinv. lra.
  Qed.

  (* --- Slowing-down spectrum: f(E) = S * tau / E --- *)

  Definition f_slowing (S tau : R) (E : R) : R := S * tau / E.

  Lemma f_slowing_nonneg :
    forall S tau E, 0 <= S -> 0 <= tau -> E_min <= E ->
      0 <= f_slowing S tau E.
  Proof.
    intros S tau E HS Htau HE.
    unfold f_slowing.
    pose proof E_min_pos as HEmin.
    apply Rmult_le_pos.
    - apply Rmult_le_pos; assumption.
    - apply Rlt_le. apply Rinv_0_lt_compat. lra.
  Qed.

  Lemma f_slowing_continuous_at :
    forall S tau E, E_min <= E -> continuous (f_slowing S tau) E.
  Proof.
    intros S tau E HE.
    unfold f_slowing.
    pose proof E_min_pos as HEmin.
    apply (continuous_mult (fun _ => S * tau) (fun y => / y)).
    - apply continuous_const.
    - apply continuous_Rinv. lra.
  Qed.

  Lemma ex_RInt_f_slowing :
    forall S tau, ex_RInt (f_slowing S tau) E_min E_alpha_birth_MeV.
  Proof.
    intros S tau.
    apply (@ex_RInt_continuous R_CompleteNormedModule).
    intros x Hx.
    apply f_slowing_continuous_at.
    rewrite Rmin_left in Hx by (apply E_min_le_birth).
    lra.
  Qed.

  (* --- Integral of the slowing-down spectrum ---

     RInt (f_slowing S tau) E_min E_birth = S * tau * (ln E_birth - ln E_min) *)

  Lemma RInt_f_slowing :
    forall S tau,
      RInt (f_slowing S tau) E_min E_alpha_birth_MeV =
      S * tau * (ln E_alpha_birth_MeV - ln E_min).
  Proof.
    intros S tau.
    pose proof E_min_pos as HEmin.
    pose proof E_alpha_birth_kinetic_pos as HEbirth.
    pose proof E_min_le_birth as HleE.
    transitivity (RInt (fun E : R => (S * tau) * / E) E_min E_alpha_birth_MeV).
    - apply (@RInt_ext R_CompleteNormedModule).
      intros x _. unfold f_slowing, Rdiv. reflexivity.
    - rewrite (RInt_scal_R (fun E : R => / E) E_min E_alpha_birth_MeV (S * tau)).
      + rewrite RInt_inv_E. reflexivity.
      + apply (@ex_RInt_continuous R_CompleteNormedModule).
        intros x Hx.
        rewrite Rmin_left in Hx by exact HleE.
        apply continuous_Rinv. lra.
  Qed.

  (* --- Alpha density n_alpha = integral of f_slowing --- *)

  Definition n_alpha_kinetic (S tau : R) : R :=
    RInt (f_slowing S tau) E_min E_alpha_birth_MeV.

  Lemma n_alpha_kinetic_value :
    forall S tau,
      n_alpha_kinetic S tau =
      S * tau * (ln E_alpha_birth_MeV - ln E_min).
  Proof. intros S tau. unfold n_alpha_kinetic. apply RInt_f_slowing. Qed.

  Lemma ln_birth_gt_ln_min : ln E_min < ln E_alpha_birth_MeV.
  Proof.
    apply ln_increasing.
    - exact E_min_pos.
    - exact E_min_lt_birth.
  Qed.

  Lemma ln_diff_pos : 0 < ln E_alpha_birth_MeV - ln E_min.
  Proof. pose proof ln_birth_gt_ln_min. lra. Qed.

  Lemma n_alpha_kinetic_pos :
    forall S tau, 0 < S -> 0 < tau -> 0 < n_alpha_kinetic S tau.
  Proof.
    intros S tau HS Htau.
    rewrite n_alpha_kinetic_value.
    apply Rmult_lt_0_compat.
    - apply Rmult_lt_0_compat; assumption.
    - exact ln_diff_pos.
  Qed.

  (* --- Pointwise integrand bound --- *)

  Lemma f_slowing_sigma_v_bound :
    forall S tau E,
      0 <= S -> 0 <= tau -> E_min <= E <= E_alpha_birth_MeV ->
      f_slowing S tau E * (sigma_E E * v_E E) <=
      f_slowing S tau E * (sigma_E_max * v_E_max).
  Proof.
    intros S tau E HS Htau HE.
    apply Rmult_le_compat_l.
    - apply f_slowing_nonneg; [exact HS | exact Htau |].
      destruct HE. assumption.
    - apply Rmult_le_compat.
      + apply sigma_E_nonneg. exact HE.
      + apply v_E_nonneg. exact HE.
      + apply sigma_E_bound. exact HE.
      + apply v_E_bound. exact HE.
  Qed.

  (* --- Integrability of the full sigma*v*f integrand --- *)

  Lemma ex_RInt_f_sigma_v :
    forall S tau,
      ex_RInt (fun E => f_slowing S tau E * (sigma_E E * v_E E))
              E_min E_alpha_birth_MeV.
  Proof.
    intros S tau.
    apply (@ex_RInt_continuous R_CompleteNormedModule).
    intros x Hx.
    rewrite Rmin_left in Hx by (apply E_min_le_birth).
    rewrite Rmax_right in Hx by (apply E_min_le_birth).
    apply (continuous_mult (f_slowing S tau) (fun E => sigma_E E * v_E E)).
    - apply f_slowing_continuous_at. lra.
    - apply (continuous_mult sigma_E v_E).
      + apply sigma_E_continuous_on. lra.
      + apply v_E_continuous_on. lra.
  Qed.

  (* --- Velocity-weighted integral, energy-resolved ---

     sigma_v_kinetic := (1/n_alpha) * integral of (f * sigma * v) *)

  Definition sigma_v_kinetic (S tau : R) : R :=
    RInt (fun E => f_slowing S tau E * (sigma_E E * v_E E))
         E_min E_alpha_birth_MeV /
    n_alpha_kinetic S tau.

  (* --- Upper bound on sigma_v_kinetic via integral monotonicity --- *)

  Lemma RInt_fsv_le_max :
    forall S tau,
      0 <= S -> 0 <= tau ->
      RInt (fun E => f_slowing S tau E * (sigma_E E * v_E E))
           E_min E_alpha_birth_MeV <=
      (sigma_E_max * v_E_max) * n_alpha_kinetic S tau.
  Proof.
    intros S tau HS Htau.
    pose proof E_min_lt_birth as HltE.
    assert (Hex_f : ex_RInt (f_slowing S tau) E_min E_alpha_birth_MeV)
      by apply ex_RInt_f_slowing.
    assert (Hex_scaled : ex_RInt
      (fun E : R => (sigma_E_max * v_E_max) * f_slowing S tau E)
      E_min E_alpha_birth_MeV)
      by (apply ex_RInt_scal_R; exact Hex_f).
    assert (Hscal_eq :
      (sigma_E_max * v_E_max) * n_alpha_kinetic S tau =
      RInt (fun E : R => (sigma_E_max * v_E_max) * f_slowing S tau E)
           E_min E_alpha_birth_MeV).
    { unfold n_alpha_kinetic.
      symmetry. apply RInt_scal_R. exact Hex_f. }
    rewrite Hscal_eq.
    apply RInt_le.
    - apply Rlt_le. exact HltE.
    - apply ex_RInt_f_sigma_v.
    - exact Hex_scaled.
    - intros E [HE1 HE2].
      rewrite (Rmult_comm (sigma_E_max * v_E_max) (f_slowing S tau E)).
      apply f_slowing_sigma_v_bound; [exact HS | exact Htau |].
      split; lra.
  Qed.

  (* --- Main derived theorem: sigma_v_kinetic <= sigma_max * v_max --- *)

  (* Constant-case closed form: when sigma_E and v_E are pointwise equal
     to constants sigma0 and v0 on the reactive window, the velocity-
     weighted average reduces to sigma0 * v0 — the inequality of
     sigma_v_kinetic_bound becomes an equality. The argument is by
     extending the integral integrand pointwise via RInt_ext, then
     factoring the constant sigma0 * v0 out of the f-weighted integral. *)
  Theorem sigma_v_kinetic_constant_value :
    forall (sigma0 v0 : R) (S tau : R),
      0 < S -> 0 < tau ->
      (forall E, E_min <= E <= E_alpha_birth_MeV -> sigma_E E = sigma0) ->
      (forall E, E_min <= E <= E_alpha_birth_MeV -> v_E E = v0) ->
      sigma_v_kinetic S tau = sigma0 * v0.
  Proof.
    intros sigma0 v0 S tau HS Htau Hsig Hv.
    unfold sigma_v_kinetic.
    pose proof (n_alpha_kinetic_pos S tau HS Htau) as Hn_pos.
    assert (Hex_f : ex_RInt (f_slowing S tau) E_min E_alpha_birth_MeV)
      by apply ex_RInt_f_slowing.
    (* Step 1: rewrite the integrand pointwise on [E_min, E_birth]. *)
    pose proof E_min_le_birth as HleE.
    assert (Hint_eq :
      RInt (fun E => f_slowing S tau E * (sigma_E E * v_E E))
           E_min E_alpha_birth_MeV =
      RInt (fun E => (sigma0 * v0) * f_slowing S tau E)
           E_min E_alpha_birth_MeV).
    { apply (@RInt_ext R_CompleteNormedModule).
      intros x Hx.
      rewrite Rmin_left in Hx by exact HleE.
      rewrite Rmax_right in Hx by exact HleE.
      assert (HxE : E_min <= x <= E_alpha_birth_MeV) by lra.
      change ((fun E0 : R => f_slowing S tau E0 * (sigma_E E0 * v_E E0)) x =
              (fun E0 : R => sigma0 * v0 * f_slowing S tau E0) x).
      cbv beta.
      rewrite (Hsig x HxE), (Hv x HxE). ring. }
    rewrite Hint_eq.
    (* Step 2: factor sigma0 * v0 out of the integral. *)
    rewrite RInt_scal_R by exact Hex_f.
    unfold n_alpha_kinetic.
    field. apply Rgt_not_eq. exact Hn_pos.
  Qed.

  Theorem sigma_v_kinetic_bound :
    forall S tau, 0 < S -> 0 < tau ->
      sigma_v_kinetic S tau <= sigma_E_max * v_E_max.
  Proof.
    intros S tau HS Htau.
    unfold sigma_v_kinetic.
    pose proof (n_alpha_kinetic_pos S tau HS Htau) as Hn_pos.
    pose proof (RInt_fsv_le_max S tau (Rlt_le _ _ HS) (Rlt_le _ _ Htau))
      as Hint_le.
    apply Rle_trans with
      (sigma_E_max * v_E_max * n_alpha_kinetic S tau /
       n_alpha_kinetic S tau).
    - unfold Rdiv. apply Rmult_le_compat_r.
      + apply Rlt_le. apply Rinv_0_lt_compat. exact Hn_pos.
      + exact Hint_le.
    - assert (Hsimpl :
        sigma_E_max * v_E_max * n_alpha_kinetic S tau /
          n_alpha_kinetic S tau = sigma_E_max * v_E_max).
      { field. apply Rgt_not_eq. exact Hn_pos. }
      rewrite Hsimpl. apply Rle_refl.
  Qed.

  (* --- Lower bound on the velocity-weighted integral --- *)

  Lemma f_slowing_sigma_v_lower :
    forall S tau E,
      0 <= S -> 0 <= tau -> E_min <= E <= E_alpha_birth_MeV ->
      f_slowing S tau E * (sigma_E_min_val * v_E_min_val) <=
      f_slowing S tau E * (sigma_E E * v_E E).
  Proof.
    intros S tau E HS Htau HE.
    apply Rmult_le_compat_l.
    - apply f_slowing_nonneg; [exact HS | exact Htau |].
      destruct HE. assumption.
    - apply Rmult_le_compat.
      + exact sigma_E_min_nonneg.
      + exact v_E_min_nonneg.
      + apply sigma_E_lower. exact HE.
      + apply v_E_lower. exact HE.
  Qed.

  Lemma RInt_fsv_ge_min :
    forall S tau,
      0 <= S -> 0 <= tau ->
      (sigma_E_min_val * v_E_min_val) * n_alpha_kinetic S tau <=
      RInt (fun E => f_slowing S tau E * (sigma_E E * v_E E))
           E_min E_alpha_birth_MeV.
  Proof.
    intros S tau HS Htau.
    pose proof E_min_lt_birth as HltE.
    assert (Hex_f : ex_RInt (f_slowing S tau) E_min E_alpha_birth_MeV)
      by apply ex_RInt_f_slowing.
    assert (Hex_scaled : ex_RInt
      (fun E : R => (sigma_E_min_val * v_E_min_val) * f_slowing S tau E)
      E_min E_alpha_birth_MeV)
      by (apply ex_RInt_scal_R; exact Hex_f).
    assert (Hscal_eq :
      (sigma_E_min_val * v_E_min_val) * n_alpha_kinetic S tau =
      RInt (fun E : R => (sigma_E_min_val * v_E_min_val) * f_slowing S tau E)
           E_min E_alpha_birth_MeV).
    { unfold n_alpha_kinetic.
      symmetry. apply RInt_scal_R. exact Hex_f. }
    rewrite Hscal_eq.
    apply RInt_le.
    - apply Rlt_le. exact HltE.
    - exact Hex_scaled.
    - apply ex_RInt_f_sigma_v.
    - intros E [HE1 HE2].
      rewrite (Rmult_comm (sigma_E_min_val * v_E_min_val)
                          (f_slowing S tau E)).
      apply f_slowing_sigma_v_lower; [exact HS | exact Htau |].
      split; lra.
  Qed.

  Theorem sigma_v_kinetic_lower_bound :
    forall S tau, 0 < S -> 0 < tau ->
      sigma_E_min_val * v_E_min_val <= sigma_v_kinetic S tau.
  Proof.
    intros S tau HS Htau.
    unfold sigma_v_kinetic.
    pose proof (n_alpha_kinetic_pos S tau HS Htau) as Hn_pos.
    pose proof (RInt_fsv_ge_min S tau (Rlt_le _ _ HS) (Rlt_le _ _ Htau))
      as Hint_ge.
    apply Rle_trans with
      ((sigma_E_min_val * v_E_min_val) * n_alpha_kinetic S tau /
       n_alpha_kinetic S tau).
    - assert (Hsimpl :
        (sigma_E_min_val * v_E_min_val) * n_alpha_kinetic S tau /
          n_alpha_kinetic S tau = sigma_E_min_val * v_E_min_val).
      { field. apply Rgt_not_eq. exact Hn_pos. }
      rewrite Hsimpl. apply Rle_refl.
    - unfold Rdiv. apply Rmult_le_compat_r.
      + apply Rlt_le. apply Rinv_0_lt_compat. exact Hn_pos.
      + exact Hint_ge.
  Qed.

  (* --- Kinetic R_secondary: literal collision integral --- *)

  Definition R_secondary_kinetic (n_B S tau : R) : R :=
    n_B * RInt (fun E => f_slowing S tau E * (sigma_E E * v_E E))
               E_min E_alpha_birth_MeV.

  (* --- Factorization theorem ---

     R_secondary_kinetic = n_alpha * n_B * sigma_v_kinetic

     i.e., the integral over alpha energies of (density at E times
     cross section at E times velocity at E) factors as
     (total density) times (n_B) times (averaged sigma*v). *)

  Theorem R_secondary_kinetic_factorization :
    forall n_B S tau, 0 < S -> 0 < tau ->
      R_secondary_kinetic n_B S tau =
      n_alpha_kinetic S tau * n_B * sigma_v_kinetic S tau.
  Proof.
    intros n_B S tau HS Htau.
    unfold R_secondary_kinetic, sigma_v_kinetic.
    pose proof (n_alpha_kinetic_pos S tau HS Htau) as Hn_pos.
    field. apply Rgt_not_eq. exact Hn_pos.
  Qed.

  (* --- Subcriticality via the energy-resolved integral ---

     The multiplication factor at a plasma state with primary rate
     R_prim, slowing-down time tau, and boron density n_B is bounded:

       R_secondary_kinetic / R_prim
       = n_alpha * n_B * sigma_v_kinetic / R_prim
       <= n_alpha * n_B * (sigma_max * v_max) / R_prim *)

  Theorem multiplication_factor_kinetic_bound :
    forall R_prim n_B S tau,
      0 < R_prim -> 0 < n_B -> 0 < S -> 0 < tau ->
      R_secondary_kinetic n_B S tau / R_prim <=
      n_alpha_kinetic S tau * n_B * (sigma_E_max * v_E_max) / R_prim.
  Proof.
    intros R_prim n_B S tau HR HnB HS Htau.
    rewrite (R_secondary_kinetic_factorization n_B S tau HS Htau).
    unfold Rdiv.
    apply Rmult_le_compat_r.
    - apply Rlt_le. apply Rinv_0_lt_compat. exact HR.
    - apply Rmult_le_compat_l.
      + apply Rmult_le_pos.
        * apply Rlt_le. exact (n_alpha_kinetic_pos S tau HS Htau).
        * apply Rlt_le. exact HnB.
      + apply (sigma_v_kinetic_bound S tau HS Htau).
  Qed.

  (* ================================================================ *)
  (* === Substantive factorization (item 1) === *)
  (* ================================================================ *)

  (* The logarithmic kinematic factor of the slowing-down spectrum:
     L = ln(E_birth) - ln(E_min) = ln(E_birth / E_min). It measures the
     energy span over which the 1/E spectrum spreads the alphas, and
     enters the alpha density n_alpha = S * tau * L. *)
  Definition L_kin : R := ln E_alpha_birth_MeV - ln E_min.

  Lemma L_kin_pos : 0 < L_kin.
  Proof. unfold L_kin. exact ln_diff_pos. Qed.

  (* Source rate convention: each p+11B reaction yields 3 alphas, so the
     alpha birth rate is 3 * R_primary. Substituting S = 3 * R_primary
     into the kinetic collision integral and factoring yields the
     bilinear decomposition

       R_secondary = 3 * R_primary * tau * n_B * (L * <sigma v>_kinetic)

     where the bracketed quantity is the effective velocity integral,
     the alpha-spectrum-averaged sigma*v scaled by the kinematic factor.
     This is the substantive content behind
     multiplication_factor_equals_figure_of_merit: the bilinear form is
     not assumed but derived from the energy-resolved Fokker-Planck
     collision integral. *)
  Theorem R_secondary_bilinear_factorization :
    forall R_prim n_B tau,
      0 < R_prim -> 0 < tau ->
      R_secondary_kinetic n_B (3 * R_prim) tau =
      3 * R_prim * tau * n_B * (L_kin * sigma_v_kinetic (3 * R_prim) tau).
  Proof.
    intros R_prim n_B tau HR Htau.
    assert (HS : 0 < 3 * R_prim) by lra.
    rewrite (R_secondary_kinetic_factorization n_B (3 * R_prim) tau HS Htau).
    rewrite n_alpha_kinetic_value.
    unfold L_kin. ring.
  Qed.

  (* Explicit identification of the alpha density from the source and
     residence time: the integral of the 1/E slowing-down spectrum over
     the reactive window evaluates to (source rate) * (residence time) *
     (kinematic factor ln(E_birth/E_min)). This is the bridge that
     connects the two factorizations
       R_secondary = n_alpha * n_B * sigma_v_kinetic   (R_secondary_kinetic_factorization)
       R_secondary = 3 * R_prim * tau * n_B * (L * sigma_v_kinetic)
                                                       (R_secondary_bilinear_factorization)
     under the source convention S = 3 * R_prim (three alphas per primary
     reaction). It is implicit in the current proof of
     R_secondary_bilinear_factorization (via rewrite n_alpha_kinetic_value)
     but here it is named as a standalone lemma so the kinematic-factor
     identity is auditable on its own. *)
  Theorem n_alpha_from_source_and_residence :
    forall R_prim tau, 0 < R_prim -> 0 < tau ->
      n_alpha_kinetic (3 * R_prim) tau = 3 * R_prim * tau * L_kin.
  Proof.
    intros R_prim tau HR Htau.
    rewrite n_alpha_kinetic_value.
    unfold L_kin. ring.
  Qed.

  (* Bridge in the opposite direction: given the standalone n_alpha
     identity, the bilinear factorization recovers from
     R_secondary_kinetic_factorization by substitution. *)
  Theorem R_secondary_bilinear_via_n_alpha :
    forall R_prim n_B tau,
      0 < R_prim -> 0 < tau ->
      R_secondary_kinetic n_B (3 * R_prim) tau =
      n_alpha_kinetic (3 * R_prim) tau * n_B *
        sigma_v_kinetic (3 * R_prim) tau.
  Proof.
    intros R_prim n_B tau HR Htau.
    assert (HS : 0 < 3 * R_prim) by lra.
    apply R_secondary_kinetic_factorization; assumption.
  Qed.

  (* The energy-resolved figure of merit. *)
  Definition kinetic_figure_of_merit (R_prim n_B tau : R) : R :=
    3 * tau * n_B * (L_kin * sigma_v_kinetic (3 * R_prim) tau).

  (* Substantive multiplication_factor_equals_figure_of_merit: the
     secondary-to-primary ratio equals the bilinear figure of merit,
     derived from the collision integral rather than by definitional
     unfolding. *)
  Theorem multiplication_factor_kinetic_eq_FoM :
    forall R_prim n_B tau,
      0 < R_prim -> 0 < tau ->
      R_secondary_kinetic n_B (3 * R_prim) tau / R_prim =
      kinetic_figure_of_merit R_prim n_B tau.
  Proof.
    intros R_prim n_B tau HR Htau.
    rewrite (R_secondary_bilinear_factorization R_prim n_B tau HR Htau).
    unfold kinetic_figure_of_merit.
    field. apply Rgt_not_eq. exact HR.
  Qed.

  (* ================================================================ *)
  (* === Energy-resolved subcriticality bound (item 2) === *)
  (* ================================================================ *)

  (* The figure of merit is bounded by the product of the kinematic
     factor, the densities, the slowing-down time, and the
     cross-section/velocity maxima. Subcriticality of this product
     gives M < 1. *)
  Theorem kinetic_FoM_upper_bound :
    forall R_prim n_B tau,
      0 < R_prim -> 0 < n_B -> 0 < tau ->
      kinetic_figure_of_merit R_prim n_B tau <=
      3 * tau * n_B * L_kin * (sigma_E_max * v_E_max).
  Proof.
    intros R_prim n_B tau HR HnB Htau.
    unfold kinetic_figure_of_merit.
    assert (HS : 0 < 3 * R_prim) by lra.
    pose proof (sigma_v_kinetic_bound (3 * R_prim) tau HS Htau) as Hsv.
    pose proof L_kin_pos as HL.
    pose proof sigma_E_max_pos as Hsig.
    pose proof v_E_max_pos as Hv.
    (* 3 tau n_B (L * sv) <= 3 tau n_B L (sigma_max v_max) *)
    apply Rle_trans with
      (3 * tau * n_B * (L_kin * (sigma_E_max * v_E_max))).
    - apply Rmult_le_compat_l.
      + repeat apply Rmult_le_pos; lra.
      + apply Rmult_le_compat_l; [lra | exact Hsv].
    - apply Req_le. ring.
  Qed.

  (* Matching lower bound on the figure of merit (item 13). *)
  Theorem kinetic_FoM_lower_bound :
    forall R_prim n_B tau,
      0 < R_prim -> 0 < n_B -> 0 < tau ->
      3 * tau * n_B * L_kin * (sigma_E_min_val * v_E_min_val) <=
      kinetic_figure_of_merit R_prim n_B tau.
  Proof.
    intros R_prim n_B tau HR HnB Htau.
    unfold kinetic_figure_of_merit.
    assert (HS : 0 < 3 * R_prim) by lra.
    pose proof (sigma_v_kinetic_lower_bound (3 * R_prim) tau HS Htau) as Hsv.
    pose proof L_kin_pos as HL.
    apply Rle_trans with
      (3 * tau * n_B * (L_kin * (sigma_E_min_val * v_E_min_val))).
    - apply Req_le. ring.
    - apply Rmult_le_compat_l.
      + repeat apply Rmult_le_pos; lra.
      + apply Rmult_le_compat_l; [lra | exact Hsv].
  Qed.

  (* Two-sided sandwich: the figure of merit lies between the lower and
     upper kinematic products. The gap between them is controlled by the
     spread between the cross-section/velocity minima and maxima. *)
  Theorem kinetic_FoM_sandwich :
    forall R_prim n_B tau,
      0 < R_prim -> 0 < n_B -> 0 < tau ->
      3 * tau * n_B * L_kin * (sigma_E_min_val * v_E_min_val) <=
      kinetic_figure_of_merit R_prim n_B tau <=
      3 * tau * n_B * L_kin * (sigma_E_max * v_E_max).
  Proof.
    intros R_prim n_B tau HR HnB Htau.
    split.
    - exact (kinetic_FoM_lower_bound R_prim n_B tau HR HnB Htau).
    - exact (kinetic_FoM_upper_bound R_prim n_B tau HR HnB Htau).
  Qed.

  (* The gap between the upper and lower bounds is exactly
     3*tau*n_B*L*(sigma_max*v_max - sigma_min*v_min), an explicit
     closed form controlling the margin from both sides. *)
  Theorem kinetic_FoM_gap :
    forall n_B tau : R,
      3 * tau * n_B * L_kin * (sigma_E_max * v_E_max) -
      3 * tau * n_B * L_kin * (sigma_E_min_val * v_E_min_val) =
      3 * tau * n_B * L_kin *
        (sigma_E_max * v_E_max - sigma_E_min_val * v_E_min_val).
  Proof. intros. ring. Qed.

  (* If the bounding product is below 1, the multiplication factor is
     strictly below 1: no avalanche. *)
  Theorem kinetic_no_avalanche :
    forall R_prim n_B tau,
      0 < R_prim -> 0 < n_B -> 0 < tau ->
      3 * tau * n_B * L_kin * (sigma_E_max * v_E_max) < 1 ->
      R_secondary_kinetic n_B (3 * R_prim) tau / R_prim < 1.
  Proof.
    intros R_prim n_B tau HR HnB Htau Hsub.
    rewrite (multiplication_factor_kinetic_eq_FoM R_prim n_B tau HR Htau).
    apply Rle_lt_trans with
      (3 * tau * n_B * L_kin * (sigma_E_max * v_E_max)).
    - exact (kinetic_FoM_upper_bound R_prim n_B tau HR HnB Htau).
    - exact Hsub.
  Qed.

  (* ================================================================ *)
  (* === Competing loss channels (item 12) === *)
  (* ================================================================ *)

  (* An alpha in the plasma is lost through two competing channels:
     slowing-down to sub-threshold energy (time constant tau_slow) and
     escape/confinement loss (time constant tau_confine). The effective
     residence time is the harmonic combination

       1/tau_eff = 1/tau_slow + 1/tau_confine

     i.e. tau_eff = tau_slow * tau_confine / (tau_slow + tau_confine).
     Adding a loss channel can only shorten the residence time. *)

  Definition tau_eff (tau_slow tau_confine : R) : R :=
    tau_slow * tau_confine / (tau_slow + tau_confine).

  Lemma tau_eff_pos :
    forall ts tc, 0 < ts -> 0 < tc -> 0 < tau_eff ts tc.
  Proof.
    intros ts tc Hts Htc. unfold tau_eff.
    apply Rdiv_lt_0_compat.
    - apply Rmult_lt_0_compat; assumption.
    - lra.
  Qed.

  (* Escape strictly reduces the residence time: tau_eff <= tau_slow. *)
  Lemma tau_eff_le_slow :
    forall ts tc, 0 < ts -> 0 < tc -> tau_eff ts tc <= ts.
  Proof.
    intros ts tc Hts Htc. unfold tau_eff.
    apply Rmult_le_reg_r with (ts + tc); [lra |].
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r; [|lra].
    rewrite Rmult_plus_distr_l. nra.
  Qed.

  (* The figure of merit with competing channels (using tau_eff) is
     bounded by the single-channel kinematic product evaluated at the
     longer slowing-down time tau_slow. Escape only helps: the secondary
     rate accounting for confinement loss is no larger than the rate
     that ignores it. *)
  Theorem channels_preserve_bound :
    forall R_prim n_B tau_slow tau_confine,
      0 < R_prim -> 0 < n_B -> 0 < tau_slow -> 0 < tau_confine ->
      kinetic_figure_of_merit R_prim n_B (tau_eff tau_slow tau_confine) <=
      3 * tau_slow * n_B * L_kin * (sigma_E_max * v_E_max).
  Proof.
    intros R_prim n_B tau_slow tau_confine HR HnB Hts Htc.
    pose proof (tau_eff_pos tau_slow tau_confine Hts Htc) as Heff_pos.
    pose proof (tau_eff_le_slow tau_slow tau_confine Hts Htc) as Heff_le.
    apply Rle_trans with
      (3 * (tau_eff tau_slow tau_confine) * n_B * L_kin *
       (sigma_E_max * v_E_max)).
    - apply (kinetic_FoM_upper_bound R_prim n_B (tau_eff tau_slow tau_confine)
               HR HnB Heff_pos).
    - pose proof L_kin_pos as HL.
      pose proof sigma_E_max_pos as Hsig.
      pose proof v_E_max_pos as Hv.
      apply Rmult_le_compat_r.
      + apply Rmult_le_pos; lra.
      + apply Rmult_le_compat_r; [lra |].
        apply Rmult_le_compat_r; [lra |].
        apply Rmult_le_compat_l; [lra | exact Heff_le].
  Qed.

  (* No avalanche with competing channels: if the single-channel bound
     (at tau_slow) is subcritical, so is the multiplication factor
     accounting for confinement loss. *)
  Theorem channels_no_avalanche :
    forall R_prim n_B tau_slow tau_confine,
      0 < R_prim -> 0 < n_B -> 0 < tau_slow -> 0 < tau_confine ->
      3 * tau_slow * n_B * L_kin * (sigma_E_max * v_E_max) < 1 ->
      R_secondary_kinetic n_B (3 * R_prim) (tau_eff tau_slow tau_confine)
        / R_prim < 1.
  Proof.
    intros R_prim n_B tau_slow tau_confine HR HnB Hts Htc Hsub.
    pose proof (tau_eff_pos tau_slow tau_confine Hts Htc) as Heff_pos.
    rewrite (multiplication_factor_kinetic_eq_FoM R_prim n_B
               (tau_eff tau_slow tau_confine) HR Heff_pos).
    apply Rle_lt_trans with
      (3 * tau_slow * n_B * L_kin * (sigma_E_max * v_E_max)).
    - exact (channels_preserve_bound R_prim n_B tau_slow tau_confine
               HR HnB Hts Htc).
    - exact Hsub.
  Qed.

  (* Helium ash and sub-threshold thermalization: alphas that slow down
     past E_min become helium ash at thermal energy. These sit strictly
     below the reactive window [E_min, E_birth] and are excluded from the
     secondary-rate integral by construction. Accumulation of ash does
     not enter the reactive integral, hence does not raise the secondary
     rate. *)
  Theorem helium_ash_below_reactive_window :
    forall E, 0 <= E < E_min -> ~ (E_min <= E).
  Proof. intros E [_ HE]. lra. Qed.

  (* The reactive secondary rate integrates only over [E_min, E_birth];
     it is insensitive to any ash population at energies below E_min. *)
  Theorem reactive_window_excludes_ash :
    forall S tau,
      R_secondary_kinetic 1 S tau =
      RInt (fun E => f_slowing S tau E * (sigma_E E * v_E E))
           E_min E_alpha_birth_MeV.
  Proof. intros S tau. unfold R_secondary_kinetic. ring. Qed.

  (* ================================================================ *)
  (* === Magnetic field coupling (item 14) === *)
  (* ================================================================ *)

  (* The alpha Larmor radius rho = m v / (q B) sets the cross-field
     step size; it decreases as 1/B. Classical cross-field confinement
     time scales as the number of gyro-orbits to diffuse across the
     device, tau_confine ~ kappa * B^2. Stronger field means smaller
     orbits, better confinement, longer residence. *)

  Definition larmor_radius (m v q B : R) : R := m * v / (q * B).

  Lemma larmor_decreasing_in_B :
    forall m v q B1 B2,
      0 < m -> 0 < v -> 0 < q -> 0 < B1 -> B1 <= B2 ->
      larmor_radius m v q B2 <= larmor_radius m v q B1.
  Proof.
    intros m v q B1 B2 Hm Hv Hq HB1 HB12.
    unfold larmor_radius, Rdiv.
    apply Rmult_le_compat_l; [nra |].
    apply Rinv_le_contravar.
    - apply Rmult_lt_0_compat; lra.
    - nra.
  Qed.

  Definition tau_confine_of_B (kappa B : R) : R := kappa * B * B.

  Lemma tau_confine_of_B_pos :
    forall kappa B, 0 < kappa -> 0 < B -> 0 < tau_confine_of_B kappa B.
  Proof.
    intros kappa B Hk HB. unfold tau_confine_of_B.
    apply Rmult_lt_0_compat;
      [apply Rmult_lt_0_compat; assumption | exact HB].
  Qed.

  Lemma tau_confine_increasing_in_B :
    forall kappa B1 B2,
      0 < kappa -> 0 < B1 -> B1 <= B2 ->
      tau_confine_of_B kappa B1 <= tau_confine_of_B kappa B2.
  Proof.
    intros kappa B1 B2 Hk HB1 HB12. unfold tau_confine_of_B.
    assert (Hcert : 0 <= kappa * ((B2 - B1) * (B2 + B1))).
    { apply Rmult_le_pos; [lra |]. apply Rmult_le_pos; lra. }
    nra.
  Qed.

  (* tau_eff is increasing in the confinement time. *)
  Lemma tau_eff_monotone_confine :
    forall ts tc1 tc2,
      0 < ts -> 0 < tc1 -> tc1 <= tc2 ->
      tau_eff ts tc1 <= tau_eff ts tc2.
  Proof.
    intros ts tc1 tc2 Hts Htc1 H12.
    assert (Htc2 : 0 < tc2) by lra.
    assert (Hd1 : ts + tc1 <> 0) by lra.
    assert (Hd2 : ts + tc2 <> 0) by lra.
    unfold tau_eff.
    apply Rle_trans with
      (ts * tc1 * (ts + tc2) / ((ts + tc1) * (ts + tc2))).
    - right. field. split; assumption.
    - apply Rle_trans with
        (ts * tc2 * (ts + tc1) / ((ts + tc1) * (ts + tc2))).
      + unfold Rdiv. apply Rmult_le_compat_r.
        * apply Rlt_le, Rinv_0_lt_compat, Rmult_lt_0_compat; lra.
        * assert (Hkey : 0 <= ts * ts * (tc2 - tc1)).
          { apply Rmult_le_pos.
            - apply Rmult_le_pos; apply Rlt_le; exact Hts.
            - lra. }
          nra.
      + right. field. split; assumption.
  Qed.

  (* Effective residence time as a function of the magnetic field. *)
  Definition tau_eff_B (tau_slow kappa B : R) : R :=
    tau_eff tau_slow (tau_confine_of_B kappa B).

  Lemma tau_eff_B_le_slow :
    forall tau_slow kappa B,
      0 < tau_slow -> 0 < kappa -> 0 < B ->
      tau_eff_B tau_slow kappa B <= tau_slow.
  Proof.
    intros tau_slow kappa B Hts Hk HB.
    unfold tau_eff_B.
    apply tau_eff_le_slow; [exact Hts | apply tau_confine_of_B_pos; assumption].
  Qed.

  (* Stronger field, longer residence: the effective residence time is
     monotone increasing in B. *)
  Theorem residence_monotone_in_B :
    forall tau_slow kappa B1 B2,
      0 < tau_slow -> 0 < kappa -> 0 < B1 -> B1 <= B2 ->
      tau_eff_B tau_slow kappa B1 <= tau_eff_B tau_slow kappa B2.
  Proof.
    intros tau_slow kappa B1 B2 Hts Hk HB1 HB12.
    unfold tau_eff_B.
    apply tau_eff_monotone_confine.
    - exact Hts.
    - apply tau_confine_of_B_pos; assumption.
    - apply tau_confine_increasing_in_B; assumption.
  Qed.

  (* The multiplication factor is bounded uniformly in B by the
     slowing-down-limited ceiling: no magnetic field strength raises
     the secondary rate above the tau_slow bound. The single-channel
     subcriticality condition therefore suffices for every B. *)
  Theorem B_field_bounded_multiplication :
    forall R_prim n_B tau_slow kappa B,
      0 < R_prim -> 0 < n_B -> 0 < tau_slow -> 0 < kappa -> 0 < B ->
      kinetic_figure_of_merit R_prim n_B (tau_eff_B tau_slow kappa B) <=
      3 * tau_slow * n_B * L_kin * (sigma_E_max * v_E_max).
  Proof.
    intros R_prim n_B tau_slow kappa B HR HnB Hts Hk HB.
    unfold tau_eff_B.
    apply (channels_preserve_bound R_prim n_B tau_slow
             (tau_confine_of_B kappa B) HR HnB Hts).
    apply tau_confine_of_B_pos; assumption.
  Qed.

  Theorem B_field_no_avalanche :
    forall R_prim n_B tau_slow kappa B,
      0 < R_prim -> 0 < n_B -> 0 < tau_slow -> 0 < kappa -> 0 < B ->
      3 * tau_slow * n_B * L_kin * (sigma_E_max * v_E_max) < 1 ->
      R_secondary_kinetic n_B (3 * R_prim) (tau_eff_B tau_slow kappa B)
        / R_prim < 1.
  Proof.
    intros R_prim n_B tau_slow kappa B HR HnB Hts Hk HB Hsub.
    unfold tau_eff_B.
    apply (channels_no_avalanche R_prim n_B tau_slow
             (tau_confine_of_B kappa B) HR HnB Hts).
    - apply tau_confine_of_B_pos; assumption.
    - exact Hsub.
  Qed.

  (* ================================================================ *)
  (* === Fokker-Planck steady state === *)
  (* ================================================================ *)

  (* Continuous slowing-down model. The alpha energy-loss rate (Coulomb
     drag) is Edot(E) = - E / tau: alphas lose energy at a rate
     proportional to their energy, with time constant tau. The
     slowing-down flux is Phi(E) = Edot(E) * f(E), the number of alphas
     per unit time crossing energy E on their way down. *)

  Definition Edot (tau : R) (E : R) : R := - E / tau.

  Definition slowing_flux (S tau : R) (E : R) : R :=
    Edot tau E * f_slowing S tau E.

  (* The slowing-down flux is constant in energy, equal to -S:
     this is the closed form Phi(E) = (-E/tau)(S tau / E) = -S. *)
  Lemma slowing_flux_constant :
    forall S tau E, 0 < tau -> E <> 0 ->
      slowing_flux S tau E = - S.
  Proof.
    intros S tau E Htau HE.
    unfold slowing_flux, Edot, f_slowing.
    field. split; [exact HE | apply Rgt_not_eq; exact Htau].
  Qed.

  (* Steady state (integrated form): the divergence d/dE[Edot f]
     vanishes, so the flux takes the same value at every energy. This
     is the steady-state slowing-down Fokker-Planck equation away from
     the source: no alpha accumulation at any intermediate energy. *)
  Theorem slowing_down_steady_state :
    forall S tau E1 E2, 0 < tau -> E1 <> 0 -> E2 <> 0 ->
      slowing_flux S tau E1 = slowing_flux S tau E2.
  Proof.
    intros S tau E1 E2 Htau HE1 HE2.
    rewrite (slowing_flux_constant S tau E1 Htau HE1).
    rewrite (slowing_flux_constant S tau E2 Htau HE2).
    reflexivity.
  Qed.

  (* Source equals sink: the flux entering at the birth energy (the S
     alphas per unit time born from p+11B fusion) equals the flux
     leaving at the thermal cutoff (the S alphas per unit time
     thermalizing). Particle conservation in steady state. *)
  Theorem source_equals_sink :
    forall S tau, 0 < tau ->
      slowing_flux S tau E_alpha_birth_MeV = slowing_flux S tau E_min.
  Proof.
    intros S tau Htau.
    apply slowing_down_steady_state.
    - exact Htau.
    - apply Rgt_not_eq. exact E_alpha_birth_kinetic_pos.
    - apply Rgt_not_eq. exact E_min_pos.
  Qed.

  (* The source magnitude: the birth rate carried by the flux at the
     birth energy is exactly S. *)
  Theorem flux_carries_source :
    forall S tau, 0 < tau ->
      slowing_flux S tau E_alpha_birth_MeV = - S.
  Proof.
    intros S tau Htau.
    apply slowing_flux_constant.
    - exact Htau.
    - apply Rgt_not_eq. exact E_alpha_birth_kinetic_pos.
  Qed.

  (* Differential form of the steady-state equation: the derivative of
     the slowing-down flux is zero at every reactive energy. This is
     the pointwise statement d/dE[Edot(E) f(E)] = 0, the slowing-down
     Fokker-Planck equation in the source-free region E_min <= E. The
     flux is locally constant near any such E (which is bounded away
     from the singular point 0), so its derivative vanishes. *)
  Theorem slowing_flux_steady_derivative :
    forall S tau E, 0 < tau -> E_min <= E ->
      is_derive (slowing_flux S tau) E 0.
  Proof.
    intros S tau E Htau HE.
    pose proof E_min_pos as HEmin.
    apply (is_derive_ext_loc (fun _ : R => - S)).
    - (* slowing_flux = -S in a neighborhood of E (where E > 0) *)
      apply (locally_interval _ E 0 (E + 1)).
      + simpl. lra.
      + simpl. lra.
      + intros y Hy0 Hy1. simpl in Hy0. symmetry.
        apply slowing_flux_constant; [exact Htau |].
        apply Rgt_not_eq. exact Hy0.
    - apply (is_derive_const (- S) E).
  Qed.

End KineticFramework.

(* ================================================================== *)
(* === A concrete kinetic instantiation === *)
(* ================================================================== *)

(* Constant sigma and v, with E_min set to a small fraction of E_birth.
   This is the simplest non-trivial instance of the kinetic framework. *)

Module ConstantKineticParams <: KINETIC_MODEL_PARAMS.

  Definition E_min : R := E_alpha_birth_MeV / 10.

  Lemma E_min_pos : 0 < E_min.
  Proof.
    unfold E_min, E_alpha_birth_MeV, Q_pB_MeV. lra.
  Qed.

  Lemma E_min_lt_birth : E_min < E_alpha_birth_MeV.
  Proof.
    unfold E_min, E_alpha_birth_MeV, Q_pB_MeV. lra.
  Qed.

  Definition sigma_E_max : R := 1 / 10000000.
  Definition v_E_max : R := 10000.

  Lemma sigma_E_max_pos : 0 < sigma_E_max.
  Proof. unfold sigma_E_max. lra. Qed.

  Lemma v_E_max_pos : 0 < v_E_max.
  Proof. unfold v_E_max. lra. Qed.

  Definition sigma_E : R -> R := fun _ => sigma_E_max.
  Definition v_E : R -> R := fun _ => v_E_max.

  Lemma sigma_E_nonneg :
    forall E, E_min <= E <= E_alpha_birth_MeV -> 0 <= sigma_E E.
  Proof.
    intros. unfold sigma_E. apply Rlt_le. exact sigma_E_max_pos.
  Qed.

  Lemma v_E_nonneg :
    forall E, E_min <= E <= E_alpha_birth_MeV -> 0 <= v_E E.
  Proof.
    intros. unfold v_E. apply Rlt_le. exact v_E_max_pos.
  Qed.

  Lemma sigma_E_bound :
    forall E, E_min <= E <= E_alpha_birth_MeV -> sigma_E E <= sigma_E_max.
  Proof. intros. unfold sigma_E. apply Rle_refl. Qed.

  Lemma v_E_bound :
    forall E, E_min <= E <= E_alpha_birth_MeV -> v_E E <= v_E_max.
  Proof. intros. unfold v_E. apply Rle_refl. Qed.

  Definition sigma_E_min_val : R := sigma_E_max.
  Definition v_E_min_val : R := v_E_max.

  Lemma sigma_E_min_nonneg : 0 <= sigma_E_min_val.
  Proof. unfold sigma_E_min_val. apply Rlt_le. exact sigma_E_max_pos. Qed.

  Lemma v_E_min_nonneg : 0 <= v_E_min_val.
  Proof. unfold v_E_min_val. apply Rlt_le. exact v_E_max_pos. Qed.

  Lemma sigma_E_lower :
    forall E, E_min <= E <= E_alpha_birth_MeV -> sigma_E_min_val <= sigma_E E.
  Proof. intros. unfold sigma_E_min_val, sigma_E. apply Rle_refl. Qed.

  Lemma v_E_lower :
    forall E, E_min <= E <= E_alpha_birth_MeV -> v_E_min_val <= v_E E.
  Proof. intros. unfold v_E_min_val, v_E. apply Rle_refl. Qed.

  Lemma sigma_E_continuous_on :
    forall E, E_min <= E <= E_alpha_birth_MeV -> continuous sigma_E E.
  Proof. intros. unfold sigma_E. apply continuous_const. Qed.

  Lemma v_E_continuous_on :
    forall E, E_min <= E <= E_alpha_birth_MeV -> continuous v_E E.
  Proof. intros. unfold v_E. apply continuous_const. Qed.

End ConstantKineticParams.

Module ConstantKineticFramework := KineticFramework ConstantKineticParams.

Print Assumptions ConstantKineticFramework.sigma_v_kinetic_bound.
Print Assumptions ConstantKineticFramework.R_secondary_kinetic_factorization.
Print Assumptions ConstantKineticFramework.multiplication_factor_kinetic_bound.
Print Assumptions ConstantKineticFramework.RInt_inv_E.
Print Assumptions ConstantKineticFramework.RInt_f_slowing.
Print Assumptions ConstantKineticFramework.slowing_down_steady_state.
Print Assumptions ConstantKineticFramework.source_equals_sink.
Print Assumptions ConstantKineticFramework.slowing_flux_steady_derivative.
Print Assumptions ConstantKineticFramework.R_secondary_bilinear_factorization.
Print Assumptions ConstantKineticFramework.multiplication_factor_kinetic_eq_FoM.
Print Assumptions ConstantKineticFramework.kinetic_FoM_upper_bound.
Print Assumptions ConstantKineticFramework.kinetic_no_avalanche.
Print Assumptions ConstantKineticFramework.kinetic_FoM_sandwich.
Print Assumptions ConstantKineticFramework.channels_preserve_bound.
Print Assumptions ConstantKineticFramework.channels_no_avalanche.
Print Assumptions ConstantKineticFramework.larmor_decreasing_in_B.
Print Assumptions ConstantKineticFramework.residence_monotone_in_B.
Print Assumptions ConstantKineticFramework.B_field_bounded_multiplication.
Print Assumptions ConstantKineticFramework.B_field_no_avalanche.
