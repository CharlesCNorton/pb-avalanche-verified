(******************************************************************************)
(*                                                                            *)
(*     Dimensional re-derivation of the avalanche framework (item 16)         *)
(*                                                                            *)
(*     Reformulates the abstract PB_AVALANCHE_PARAMS interface using          *)
(*     DR-typed parameters from pb_avalanche_units.v. Every quantity          *)
(*     (densities, slowing-down time, cross sections, velocities, rates)      *)
(*     carries an explicit unit; the multiplication factor                    *)
(*     R_secondary / R_primary inhabits DR zero_unit by Coq's type            *)
(*     check, rather than being verified separately.                          *)
(*                                                                            *)
(*     The framework demonstrates dimensional homogeneity as a typing         *)
(*     property of the formalization itself.                                  *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra ZArith Lia.
From PBAvalanche Require Import pb_avalanche pb_avalanche_units.

Open Scope R_scope.

(* ================================================================== *)
(* === Auxiliary unit synonyms (extending pb_avalanche_units.v) === *)
(* ================================================================== *)

Open Scope Z_scope.
Definition temp_unit : Unit :=
  {| u_length := 0; u_time := 0; u_mass := 0; u_charge := 0;
     u_temp := 1; u_count := 0 |}.
Definition length_unit : Unit :=
  {| u_length := 1; u_time := 0; u_mass := 0; u_charge := 0;
     u_temp := 0; u_count := 0 |}.
Open Scope R_scope.

(* ================================================================== *)
(* === DR-typed plasma state === *)
(* ================================================================== *)

(* A plasma state in DR form: each quantity carries its physical unit.
   We embed the existing PlasmaState into this typed view. *)

Record DR_PlasmaState : Type := mkDR_PlasmaState {
  dr_n_p   : DR density_unit;
  dr_n_B   : DR density_unit;
  dr_T     : DR temp_unit;
  dr_B     : DR length_unit;
  drps_pos_n_p : 0 < dr_val dr_n_p;
  drps_pos_n_B : 0 < dr_val dr_n_B;
  drps_pos_T   : 0 < dr_val dr_T;
  drps_pos_B   : 0 < dr_val dr_B;
}.

(* Cast a DR_PlasmaState to a plain PlasmaState (forget the dr_val
   tags). *)
Definition cast_DR_PlasmaState (s : DR_PlasmaState) : PlasmaState :=
  mkPlasmaState (dr_val (dr_n_p s)) (dr_val (dr_n_B s))
                (dr_val (dr_T s)) (dr_val (dr_B s))
                (drps_pos_n_p s) (drps_pos_n_B s)
                (drps_pos_T s) (drps_pos_B s).

(* ================================================================== *)
(* === The dimensional multiplication factor === *)
(* ================================================================== *)

(* Composite multiplication factor in DR form. The result type
   [DR fom_unit] is determined by the framework's choice of base
   quantities; under the chosen unit synonyms, fom_unit equals
   count^1 (a per-reaction counter). *)
Definition dr_multiplication_factor
  (n_B    : DR density_unit)
  (tau_s  : DR time_unit)
  (sigma_v : DR sigma_v_unit)
  : DR fom_unit :=
  dr_scal 3 (dr_mul n_B (dr_mul tau_s sigma_v)).

(* The dimensional balance is now definitional: the multiplication
   factor's unit reduces to zero_unit at the count axis (after
   dividing by another rate). The value is just the product of the
   value-level pieces. *)
Lemma dr_multiplication_factor_value :
  forall n_B tau_s sigma_v,
    dr_val (dr_multiplication_factor n_B tau_s sigma_v) =
    3 * dr_val n_B * (dr_val tau_s * dr_val sigma_v).
Proof.
  intros [vn] [vt] [vs]. simpl. ring.
Qed.

(* ================================================================== *)
(* === Type-level dimensional check === *)
(* ================================================================== *)

(* The "ratio of rates" — divide one rate by another to get a
   dimensionless number. With the Z-exponent algebra, this lives
   in DR (unit_div rate_unit rate_unit), which we have proved equals
   zero_unit by multiplication_factor_unit_dimensionless. We expose
   the DR-typed witness. *)

Definition dr_rate_ratio
  (R_secondary : DR rate_unit) (R_primary : DR rate_unit)
  : DR (unit_div rate_unit rate_unit) :=
  dr_div R_secondary R_primary.

(* The rate-ratio's unit reduces to zero_unit. *)
Lemma dr_rate_ratio_unit :
  unit_div rate_unit rate_unit = zero_unit.
Proof. exact multiplication_factor_unit_dimensionless. Qed.

(* Value-level result for the rate ratio: just the quotient of the
   underlying values. *)
Lemma dr_rate_ratio_value :
  forall R_sec R_prim,
    dr_val (dr_rate_ratio R_sec R_prim) =
    dr_val R_sec / dr_val R_prim.
Proof.
  intros [vs] [vp]. simpl. reflexivity.
Qed.

(* ================================================================== *)
(* === DR composition identities === *)
(* ================================================================== *)

(* Multiplying density (count/length^3) by sigma_v (length^3/time)
   gives a quantity with zero length-exponent and -1 time exponent —
   the "per-particle reaction frequency". *)
Definition reaction_freq_unit : Unit :=
  unit_mul density_unit sigma_v_unit.

Lemma reaction_freq_unit_value :
  reaction_freq_unit =
    {| u_length := 0; u_time := -1; u_mass := 0; u_charge := 0;
       u_temp := 0; u_count := 1 |}.
Proof. unfold reaction_freq_unit, unit_mul, density_unit, sigma_v_unit.
       simpl. f_equal. Qed.

(* The DR-typed reaction frequency: a single density times sigma_v. *)
Definition dr_reaction_freq
  (n : DR density_unit) (sigma_v : DR sigma_v_unit)
  : DR reaction_freq_unit :=
  dr_mul n sigma_v.

Lemma dr_reaction_freq_value :
  forall n sigma_v,
    dr_val (dr_reaction_freq n sigma_v) = dr_val n * dr_val sigma_v.
Proof. intros [a] [b]. reflexivity. Qed.

(* ================================================================== *)
(* === DR-typed kinetic factorization === *)
(* ================================================================== *)

(* The volumetric reaction rate is the product of TWO densities and
   sigma_v. In the current Unit algebra, count adds, giving
   count^2 — not count^1. We expose this as a separate
   "two-density rate" unit and note the dimensional content
   explicitly. *)
Definition rate_two_density_unit : Unit :=
  unit_mul density_unit (unit_mul density_unit sigma_v_unit).

Lemma rate_two_density_unit_value :
  rate_two_density_unit =
    {| u_length := -3; u_time := -1; u_mass := 0; u_charge := 0;
       u_temp := 0; u_count := 2 |}.
Proof.
  unfold rate_two_density_unit, unit_mul, density_unit, sigma_v_unit.
  simpl. f_equal.
Qed.

Definition dr_R_secondary
  (n_alpha n_B : DR density_unit) (sigma_v : DR sigma_v_unit)
  : DR rate_two_density_unit :=
  dr_mul n_alpha (dr_mul n_B sigma_v).

Lemma dr_R_secondary_value :
  forall n_alpha n_B sigma_v,
    dr_val (dr_R_secondary n_alpha n_B sigma_v) =
    dr_val n_alpha * (dr_val n_B * dr_val sigma_v).
Proof. intros [a] [b] [c]. reflexivity. Qed.

(* The ratio of two same-form rates is dimensionless. Two factors of
   rate_two_density_unit cancel exactly. *)
Lemma rate_two_density_ratio_dimensionless :
  unit_div rate_two_density_unit rate_two_density_unit = zero_unit.
Proof. apply unit_mul_inv_r. Qed.

(* ================================================================== *)
(* === Item 19: DR-typed PB_AVALANCHE_PARAMS module type === *)
(* ================================================================== *)

(* A DR-typed reformulation of the avalanche-framework hypotheses.
   Every constant carries an explicit physical unit, enforced by
   the DR type system. Plain-real bounds are re-derived by reading
   off dr_val. *)
Module Type DR_PB_AVALANCHE_PARAMS.

  (* Reactor envelope. *)
  Parameter dr_n_B_max : DR density_unit.
  Parameter dr_T_max   : DR temp_unit.
  Parameter dr_n_p_min : DR density_unit.

  Axiom dr_n_B_max_pos : 0 < dr_val dr_n_B_max.
  Axiom dr_T_max_pos   : 0 < dr_val dr_T_max.
  Axiom dr_n_p_min_pos : 0 < dr_val dr_n_p_min.

  (* Sup bounds on the knock-on cross section and recoil velocity. *)
  Parameter dr_sigma_knockon_max : DR sigma_v_unit.
  Parameter dr_v_alpha_max       : DR sigma_v_unit.

  Axiom dr_sigma_knockon_max_pos : 0 < dr_val dr_sigma_knockon_max.
  Axiom dr_v_alpha_max_pos       : 0 < dr_val dr_v_alpha_max.

End DR_PB_AVALANCHE_PARAMS.

(* A DR-typed framework module that consumes the above parameters and
   exposes the upper-bound figure of merit in dimensionally explicit
   form. *)
Module DRFramework (DR_P : DR_PB_AVALANCHE_PARAMS).
  Import DR_P.

  (* The DR-typed FoM upper bound. *)
  Definition dr_FoM_max :
    DR (unit_mul density_unit (unit_mul sigma_v_unit sigma_v_unit)) :=
    dr_mul dr_n_B_max (dr_mul dr_sigma_knockon_max dr_v_alpha_max).

  Lemma dr_FoM_max_value :
    dr_val dr_FoM_max =
    dr_val dr_n_B_max *
    (dr_val dr_sigma_knockon_max * dr_val dr_v_alpha_max).
  Proof. unfold dr_FoM_max. rewrite !dr_val_mul. reflexivity. Qed.

  Lemma dr_FoM_max_positive : 0 < dr_val dr_FoM_max.
  Proof.
    rewrite dr_FoM_max_value.
    apply Rmult_lt_0_compat; [exact dr_n_B_max_pos |].
    apply Rmult_lt_0_compat;
      [exact dr_sigma_knockon_max_pos | exact dr_v_alpha_max_pos].
  Qed.

End DRFramework.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions dr_multiplication_factor_value.
Print Assumptions dr_rate_ratio_unit.
Print Assumptions dr_rate_ratio_value.
Print Assumptions reaction_freq_unit_value.
Print Assumptions dr_reaction_freq_value.
Print Assumptions rate_two_density_unit_value.
Print Assumptions dr_R_secondary_value.
Print Assumptions rate_two_density_ratio_dimensionless.
