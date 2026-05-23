(******************************************************************************)
(*                                                                            *)
(*     Pervasive axiom audit (item 2 of the next-generation program)          *)
(*                                                                            *)
(*     Runs `Print Assumptions` against every exported Theorem, Lemma,        *)
(*     Corollary, Fact, and module-projected identity that constitutes the    *)
(*     content of the development. The expected footprint for every entry     *)
(*     is the three Stdlib Dedekind axioms                                    *)
(*                                                                            *)
(*       ClassicalDedekindReals.sig_forall_dec                                *)
(*       ClassicalDedekindReals.sig_not_dec                                   *)
(*       FunctionalExtensionality.functional_extensionality_dep               *)
(*                                                                            *)
(*     plus, for theorems that ultimately route through Coquelicot's          *)
(*     fundamental-theorem-of-calculus machinery, `Classical_Prop.classic`.   *)
(*                                                                            *)
(*     If any regression introduces a new axiom or a non-Qed proof, this      *)
(*     file's compilation will either fail or its `Print Assumptions`         *)
(*     output will surface the deviation. The file therefore acts as a        *)
(*     compile-time regression guard against axiomatic creep.                 *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From PBAvalanche Require Import
  pb_avalanche
  pb_avalanche_integral
  pb_avalanche_kinetic
  pb_avalanche_envelope
  pb_avalanche_thermal
  pb_avalanche_spitzer
  pb_avalanche_iaea
  pb_avalanche_units
  pb_avalanche_final.

(* ================================================================== *)
(* === pb_avalanche.v — abstract framework + classical instances === *)
(* ================================================================== *)

Print Assumptions ConcreteSettlement.multiplication_factor_equals_figure_of_merit.
Print Assumptions ConcreteSettlement.avalanche_threshold_iff.
Print Assumptions ConcreteSettlement.avalanche_subcritical_iff.
Print Assumptions ConcreteSettlement.avalanche_critical_iff.
Print Assumptions ConcreteSettlement.tau_slow_alpha_spitzer_formula.
Print Assumptions ConcreteSettlement.f_alpha_slowing_down_equilibrium.
Print Assumptions ConcreteSettlement.R_secondary_kinetic_decomposition.
Print Assumptions ConcreteSettlement.tau_slow_alpha_reactor_bound.
Print Assumptions ConcreteSettlement.reactor_FoM_upper_bound.
Print Assumptions ConcreteSettlement.reactor_no_avalanche.
Print Assumptions ConcreteSettlement.reactor_no_multiplication.
Print Assumptions ConcreteSettlement.hora_putvinski_settlement.
Print Assumptions ConcreteSettlement.reactor_avalanche_impossible.
Print Assumptions ConcreteSettlement.reactor_no_marginal.
Print Assumptions ConcreteSettlement.reactor_FoM_no_marginal.
Print Assumptions ConcreteSettlement.reactor_FoM_avalanche_impossible.
Print Assumptions ConcreteSettlement.multiplication_factor_pointwise_bound.
Print Assumptions ConcreteSettlement.reactor_safety_margin_positive.
Print Assumptions ConcreteSettlement.reactor_safety_margin_bound.

Print Assumptions PhysicalSettlement.hora_putvinski_settlement.
Print Assumptions PhysicalSettlement.reactor_no_multiplication.
Print Assumptions PhysicalSettlement.reactor_no_avalanche.

Print Assumptions SaturatedSettlement.hora_putvinski_settlement.
Print Assumptions SaturatedSettlement.reactor_no_multiplication.

Print Assumptions LinearCrossSectionSettlement.hora_putvinski_settlement.
Print Assumptions LinearCrossSectionSettlement.reactor_no_multiplication.

Print Assumptions concrete_FoM_max_reactor_value.
Print Assumptions concrete_multiplication_factor_bound.
Print Assumptions concrete_safety_margin.
Print Assumptions witness_no_avalanche.
Print Assumptions witness_multiplication_factor_bound.
Print Assumptions physical_witness_no_avalanche.
Print Assumptions physical_FoM_max_value.
Print Assumptions physical_multiplication_factor_bound.
Print Assumptions physical_safety_margin.

(* ================================================================== *)
(* === pb_avalanche_integral.v — Coquelicot-derived bound + 2 more === *)
(* ================================================================== *)

Print Assumptions alpha_velocity_average_bound.
Print Assumptions alpha_velocity_average_nonneg.
Print Assumptions RInt_fsv_le.

Print Assumptions IntegralSettlement.hora_putvinski_settlement.
Print Assumptions IntegralSettlement.reactor_no_multiplication.
Print Assumptions IntegralParams.alpha_weighted_integral_value.
Print Assumptions IntegralParams.alpha_weighted_integral_uniform_bound.

Print Assumptions LinearIntegralSettlement.hora_putvinski_settlement.
Print Assumptions LinearIntegralSettlement.reactor_no_multiplication.
Print Assumptions LinearIntegralParams.alpha_weighted_integral_value.
Print Assumptions LinearIntegralParams.alpha_weighted_integral_uniform_bound.

Print Assumptions RInt_id_0_b.
Print Assumptions linear_integrand_RInt.
Print Assumptions all_settlements_subcritical.
Print Assumptions all_six_settlements_subcritical.

(* ================================================================== *)
(* === pb_avalanche_kinetic.v — energy-resolved kinetic framework === *)
(* ================================================================== *)

Print Assumptions ConstantKineticFramework.RInt_inv_E.
Print Assumptions ConstantKineticFramework.RInt_f_slowing.
Print Assumptions ConstantKineticFramework.n_alpha_kinetic_value.
Print Assumptions ConstantKineticFramework.sigma_v_kinetic_bound.
Print Assumptions ConstantKineticFramework.sigma_v_kinetic_constant_value.
Print Assumptions ConstantKineticFramework.sigma_v_kinetic_lower_bound.
Print Assumptions ConstantKineticFramework.R_secondary_kinetic_factorization.
Print Assumptions ConstantKineticFramework.multiplication_factor_kinetic_bound.
Print Assumptions ConstantKineticFramework.R_secondary_bilinear_factorization.
Print Assumptions ConstantKineticFramework.n_alpha_from_source_and_residence.
Print Assumptions ConstantKineticFramework.R_secondary_bilinear_via_n_alpha.
Print Assumptions ConstantKineticFramework.multiplication_factor_kinetic_eq_FoM.
Print Assumptions ConstantKineticFramework.kinetic_FoM_upper_bound.
Print Assumptions ConstantKineticFramework.kinetic_FoM_lower_bound.
Print Assumptions ConstantKineticFramework.kinetic_FoM_sandwich.
Print Assumptions ConstantKineticFramework.kinetic_FoM_gap.
Print Assumptions ConstantKineticFramework.kinetic_no_avalanche.
Print Assumptions ConstantKineticFramework.channels_preserve_bound.
Print Assumptions ConstantKineticFramework.channels_no_avalanche.
Print Assumptions ConstantKineticFramework.helium_ash_below_reactive_window.
Print Assumptions ConstantKineticFramework.reactive_window_excludes_ash.
Print Assumptions ConstantKineticFramework.larmor_decreasing_in_B.
Print Assumptions ConstantKineticFramework.tau_confine_increasing_in_B.
Print Assumptions ConstantKineticFramework.residence_monotone_in_B.
Print Assumptions ConstantKineticFramework.B_field_bounded_multiplication.
Print Assumptions ConstantKineticFramework.B_field_no_avalanche.
Print Assumptions ConstantKineticFramework.slowing_flux_constant.
Print Assumptions ConstantKineticFramework.slowing_down_steady_state.
Print Assumptions ConstantKineticFramework.source_equals_sink.
Print Assumptions ConstantKineticFramework.flux_carries_source.
Print Assumptions ConstantKineticFramework.slowing_flux_steady_derivative.

(* ================================================================== *)
(* === pb_avalanche_envelope.v — admissibility + Hora regime === *)
(* ================================================================== *)

Print Assumptions ln2_lt_1.
Print Assumptions PK_L_eq_ln2.
Print Assumptions PK_L_lt_1.
Print Assumptions PK_L_pos.
Print Assumptions PK_sigma_v_value.
Print Assumptions admissible_product_subcritical.
Print Assumptions envelope_subcritical.
Print Assumptions hora_admissible.
Print Assumptions hora_regime_no_avalanche.

(* ================================================================== *)
(* === pb_avalanche_thermal.v — Maxwellian-averaged reactivity === *)
(* ================================================================== *)

Print Assumptions is_derive_id_times_const.
Print Assumptions is_derive_neg_id_over_T.
Print Assumptions is_derive_exp_neg_id_over_T.
Print Assumptions is_derive_neg_T_exp.
Print Assumptions continuous_exp_thermal.
Print Assumptions RInt_exp_thermal.
Print Assumptions exp_thermal_pos.

(* ================================================================== *)
(* === pb_avalanche_spitzer.v — Spitzer-Trubnikov + Coulomb log === *)
(* ================================================================== *)

Print Assumptions coulomb_log_pos.
Print Assumptions coulomb_log_monotone_bmax.
Print Assumptions admissible_coulomb_log_pos.
Print Assumptions tau_spitzer_pos.
Print Assumptions tau_spitzer_scaling_T.
Print Assumptions tau_spitzer_scaling_n.
Print Assumptions tau_spitzer_scaling_ln_lambda.
Print Assumptions tau_spitzer_lower_bound.
Print Assumptions tau_spitzer_upper_bound.
Print Assumptions tau_spitzer_sandwich.
Print Assumptions tau_spitzer_composite_scaling.
Print Assumptions coulomb_Edot_neg.
Print Assumptions coulomb_Edot_linear.
Print Assumptions coulomb_Edot_scal.
Print Assumptions slowing_flux_value.
Print Assumptions slowing_steady_state.
Print Assumptions source_balances_sink.
Print Assumptions tau_spitzer_eq_abstract.
Print Assumptions n_eff_ion_scatter_pos.

(* ================================================================== *)
(* === pb_avalanche_iaea.v — IAEA interpolation + error bound === *)
(* ================================================================== *)

Print Assumptions interp_segment_left.
Print Assumptions interp_segment_right.
Print Assumptions interp_segment_continuous.
Print Assumptions ex_RInt_interp_segment.
Print Assumptions RInt_interp_segment.
Print Assumptions interp_linear_first_segment.
Print Assumptions interp_linear_tail.
Print Assumptions head_E_le_last_E.
Print Assumptions continuous_piecewise_at.
Print Assumptions interp_linear_continuous_on.
Print Assumptions ex_RInt_interp_linear.
Print Assumptions RInt_interp_linear_split.
Print Assumptions RInt_interp_linear_eq_trap.
Print Assumptions interp_error_bound.
Print Assumptions iaea_pB_sample_sorted.
Print Assumptions iaea_pB_sample_trap_value.
Print Assumptions iaea_pB_sample_integral.

(* ================================================================== *)
(* === pb_avalanche_units.v — dimensional types === *)
(* ================================================================== *)

Print Assumptions unit_mul_zero_l.
Print Assumptions unit_mul_zero_r.
Print Assumptions unit_mul_comm.
Print Assumptions unit_mul_assoc.
Print Assumptions unit_mul_inv_r.
Print Assumptions unit_mul_inv_l.
Print Assumptions unit_inv_inv.
Print Assumptions unit_pow_zero.
Print Assumptions unit_pow_one.
Print Assumptions unit_pow_add.
Print Assumptions dr_lift_unlift.
Print Assumptions dr_unlift_lift.
Print Assumptions dr_val_add.
Print Assumptions dr_val_mul.
Print Assumptions dr_val_inv.
Print Assumptions dr_val_div.
Print Assumptions dr_val_opp.
Print Assumptions dr_val_scal.
Print Assumptions dr_eq_intro.
Print Assumptions dr_add_comm.
Print Assumptions dr_add_assoc.
Print Assumptions fom_unit_value.
Print Assumptions fom_unit_length_zero.
Print Assumptions fom_unit_time_zero.
Print Assumptions fom_unit_mass_zero.
Print Assumptions fom_unit_charge_zero.
Print Assumptions fom_unit_temp_zero.
Print Assumptions multiplication_factor_unit_dimensionless.
Print Assumptions rate_over_rate_zero.
Print Assumptions velocity_times_time_is_length.
Print Assumptions cross_section_velocity_is_sigma_v.

(* ================================================================== *)
(* === pb_avalanche_final.v — aggregate settlement === *)
(* ================================================================== *)

Print Assumptions pb_avalanche_kinetic_criterion.
Print Assumptions pb_avalanche_envelope_subcriticality.
Print Assumptions pb_avalanche_hora_rebuttal.
Print Assumptions pb_avalanche_slowing_steady_state.
Print Assumptions pb_avalanche_thermal_exp_integral.
Print Assumptions pb_avalanche_spitzer_scaling.
Print Assumptions pb_avalanche_spitzer_envelope.
Print Assumptions pb_avalanche_IAEA_error_bound.
Print Assumptions pb_avalanche_dimensional_balance.
Print Assumptions pb_avalanche_settlement.
