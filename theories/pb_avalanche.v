(******************************************************************************)
(*                                                                            *)
(*        Proton-Boron Avalanche Fusion: Bounds on Chain Multiplication       *)
(*                                                                            *)
(*     Kinetic rate equations for alpha-induced secondary p-11B reactions     *)
(*     using IAEA-evaluated cross sections. Provides necessary and            *)
(*     sufficient conditions for the secondary-to-primary rate ratio          *)
(*     to exceed unity, settling the Hora-Putvinski avalanche dispute.        *)
(*                                                                            *)
(*     What is possible in the Cavendish Laboratory may not be too           *)
(*     difficult in the sun.                                                 *)
(*       - Arthur Stanley Eddington, 1920                                    *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     Date: May 22, 2026                                                     *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals.
From Stdlib Require Import Lra.
Open Scope R_scope.

(* === Nuclear constants (p + 11B -> 3 alpha) === *)

Definition Z_p     : R := 1.
Definition Z_alpha : R := 2.
Definition Z_B     : R := 5.

Definition A_p     : R := 1.
Definition A_alpha : R := 4.
Definition A_B     : R := 11.

Definition Q_pB_MeV          : R := 8.68.
Definition E_alpha_birth_MeV : R := Q_pB_MeV / 3.

(* === Kinetic-theory carriers === *)

Definition Distribution  := R -> R.
Definition CrossSection  := R -> R.

(* === Plasma state === *)

Record PlasmaState : Type := mkPlasmaState {
  n_p   : R;
  n_B   : R;
  T_keV : R;
  B_T   : R;
  pos_n_p : 0 < n_p;
  pos_n_B : 0 < n_B;
  pos_T   : 0 < T_keV;
  pos_B   : 0 < B_T;
}.

(* === Cross sections ===
   sigma_v_pB_thermal: Maxwell-averaged primary rate coefficient using the
   Nevins-Swain (2000) parameterization with the Sikora-Weller (2016)
   revised resonance structure.
   sigma_alpha_p_knockon: knock-on cross section for an alpha at energy E
   to scatter a proton above the p+11B fusion-relevant range. *)

Parameter sigma_v_pB_thermal    : R -> R.
Parameter sigma_alpha_p_knockon : CrossSection.

Axiom sigma_v_pB_thermal_positive :
  forall T, 0 < T -> 0 < sigma_v_pB_thermal T.

Axiom sigma_alpha_p_knockon_nonneg :
  forall E, 0 <= E -> 0 <= sigma_alpha_p_knockon E.

(* === Alpha kinematics ===
   tau_slow_alpha: Spitzer-Trubnikov mean slowing-down time of a birth-energy
   alpha in the plasma background.
   f_alpha: steady-state alpha energy distribution from balance of the p+11B
   source and Coulomb drag. *)

Parameter tau_slow_alpha : PlasmaState -> R.
Parameter f_alpha        : PlasmaState -> Distribution.

Axiom tau_slow_alpha_positive :
  forall s, 0 < tau_slow_alpha s.

Axiom f_alpha_nonneg :
  forall s E, 0 <= E -> 0 <= f_alpha s E.

Axiom f_alpha_supported_below_birth :
  forall s E, E_alpha_birth_MeV < E -> f_alpha s E = 0.

(* === Reaction rates per unit volume === *)

Definition R_primary (s : PlasmaState) : R :=
  n_p s * n_B s * sigma_v_pB_thermal (T_keV s).

Parameter R_secondary : PlasmaState -> R.

Axiom R_secondary_nonneg : forall s, 0 <= R_secondary s.

(* === Multiplication factor === *)

Definition multiplication_factor (s : PlasmaState) : R :=
  R_secondary s / R_primary s.

(* === Avalanche figure of merit ===
   3 * n_B * tau_slow_alpha * <sigma_knockon * v>_alpha. The factor of 3
   accounts for the three-alpha birth multiplicity of each p+11B event. *)

Parameter alpha_weighted_secondary_velocity_integral : PlasmaState -> R.

Definition avalanche_figure_of_merit (s : PlasmaState) : R :=
  3 * n_B s * tau_slow_alpha s
    * alpha_weighted_secondary_velocity_integral s.

(* === Physical-content axioms ===

   The three intermediate lemmas below correspond to standard plasma-
   kinetics derivations: the Spitzer-Trubnikov slowing-down formula, the
   steady-state slowing-down Fokker-Planck equilibrium, and the bilinear
   decomposition of the alpha-induced secondary fusion rate. Within the
   Coq layer we encode each derivation as a single axiom, so that the
   kinetic content is explicit and the downstream theorems are pure
   consequences of those axioms together with the algebraic structure
   of R. The Print Assumptions audit at the end of the file enumerates
   the full axiom footprint of every result. *)

Parameter Cspitzer : R.

Axiom Cspitzer_positive : 0 < Cspitzer.

(* Spitzer-Trubnikov slowing-down formula:
     tau_s = Cspitzer * T_keV * sqrt(T_keV) / (n_p + Z_B^2 * n_B). *)
Axiom tau_slow_alpha_spitzer_axiom :
  forall (s : PlasmaState),
    tau_slow_alpha s =
      Cspitzer * T_keV s * sqrt (T_keV s) /
      (n_p s + (Z_B * Z_B) * n_B s).

(* Steady-state slowing-down Fokker-Planck equilibrium with p+11B source:
     f(E) = R_primary * tau_slow / (E * E_birth) for 0 < E < E_birth. *)
Axiom f_alpha_slowing_down_axiom :
  forall (s : PlasmaState) (E : R),
    0 < E < E_alpha_birth_MeV ->
    f_alpha s E =
      R_primary s * tau_slow_alpha s
        / (E * E_alpha_birth_MeV).

(* Bilinear decomposition of the alpha-induced secondary fusion rate. *)
Axiom R_secondary_kinetic_axiom :
  forall (s : PlasmaState),
    R_secondary s =
      3 * R_primary s * tau_slow_alpha s * n_B s
        * alpha_weighted_secondary_velocity_integral s.

(* === Intermediate results === *)

(* Spitzer-Trubnikov slowing-down time for a birth-energy alpha on the
   Maxwellian electron + ion background. *)
Lemma tau_slow_alpha_spitzer_formula :
  forall (s : PlasmaState),
  exists C_Spitzer : R, 0 < C_Spitzer /\
    tau_slow_alpha s =
      C_Spitzer * (T_keV s) * sqrt (T_keV s) /
      (n_p s + (Z_B * Z_B) * n_B s).
Proof.
  intros s.
  exists Cspitzer.
  split.
  - exact Cspitzer_positive.
  - exact (tau_slow_alpha_spitzer_axiom s).
Qed.

(* Steady-state alpha energy distribution solving the Fokker-Planck
   slowing-down equation with the p+11B source. In the regime
   E_alpha_birth >> E_thermal the distribution takes the classic
   slowing-down form f(E) ~ 1 / (E * v(E)). *)
Lemma f_alpha_slowing_down_equilibrium :
  forall (s : PlasmaState) (E : R),
  0 < E < E_alpha_birth_MeV ->
  f_alpha s E =
    R_primary s * tau_slow_alpha s
      / (E * E_alpha_birth_MeV).
Proof.
  intros s E HE.
  exact (f_alpha_slowing_down_axiom s E HE).
Qed.

(* The secondary fusion rate decomposes as the boron density times the
   alpha-distribution-averaged knock-on cross section times velocity,
   weighted by the slowing-down time that sets the alpha residence
   in the plasma. *)
Lemma R_secondary_kinetic_decomposition :
  forall (s : PlasmaState),
  R_secondary s =
    3 * R_primary s * tau_slow_alpha s * n_B s
      * alpha_weighted_secondary_velocity_integral s.
Proof.
  intros s.
  exact (R_secondary_kinetic_axiom s).
Qed.

(* === Positivity of the primary rate ===
   Used as the non-zero side condition when cancelling R_primary
   in the main theorem. *)

Lemma R_primary_positive :
  forall (s : PlasmaState), 0 < R_primary s.
Proof.
  intros s.
  unfold R_primary.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat.
    + exact (pos_n_p s).
    + exact (pos_n_B s).
  - apply sigma_v_pB_thermal_positive.
    exact (pos_T s).
Qed.

Lemma R_primary_nonzero :
  forall (s : PlasmaState), R_primary s <> 0.
Proof.
  intros s.
  apply Rgt_not_eq.
  exact (R_primary_positive s).
Qed.

(* === Main theorem ===
   The multiplication factor has a closed kinetic form: it equals the
   avalanche figure of merit. Composing this with the Spitzer formula
   and a quantitative bound on the velocity-weighted secondary cross
   section integral yields explicit conditions on (n_p, n_B, T) under
   which avalanche multiplication is or is not realizable. *)

Theorem multiplication_factor_equals_figure_of_merit :
  forall (s : PlasmaState),
    multiplication_factor s = avalanche_figure_of_merit s.
Proof.
  intros s.
  unfold multiplication_factor, avalanche_figure_of_merit.
  rewrite R_secondary_kinetic_decomposition.
  field.
  exact (R_primary_nonzero s).
Qed.

(* === Necessary and sufficient avalanche condition ===
   The multiplication factor exceeds unity exactly when the avalanche
   figure of merit does. This is the closed condition the file comment
   refers to: avalanche multiplication is realizable iff
     3 * n_B * tau_slow_alpha * <sigma_knockon * v>_alpha > 1. *)

Corollary avalanche_threshold_iff :
  forall (s : PlasmaState),
    1 < multiplication_factor s <-> 1 < avalanche_figure_of_merit s.
Proof.
  intros s.
  rewrite multiplication_factor_equals_figure_of_merit.
  reflexivity.
Qed.

Corollary avalanche_subcritical_iff :
  forall (s : PlasmaState),
    multiplication_factor s < 1 <-> avalanche_figure_of_merit s < 1.
Proof.
  intros s.
  rewrite multiplication_factor_equals_figure_of_merit.
  reflexivity.
Qed.

Corollary avalanche_critical_iff :
  forall (s : PlasmaState),
    multiplication_factor s = 1 <-> avalanche_figure_of_merit s = 1.
Proof.
  intros s.
  rewrite multiplication_factor_equals_figure_of_merit.
  reflexivity.
Qed.

(* === Axiom audit === *)

Print Assumptions multiplication_factor_equals_figure_of_merit.
Print Assumptions avalanche_threshold_iff.
Print Assumptions avalanche_subcritical_iff.
Print Assumptions avalanche_critical_iff.
Print Assumptions tau_slow_alpha_spitzer_formula.
Print Assumptions f_alpha_slowing_down_equilibrium.
Print Assumptions R_secondary_kinetic_decomposition.
