(******************************************************************************)
(*                                                                            *)
(*     Constructive subset audit (item 30)                                    *)
(*                                                                            *)
(*     Identifies the maximal subset of the development that closes by Qed    *)
(*     without invoking Classical_Prop.classic. The classical axiom is        *)
(*     pulled in only via Coquelicot's fundamental-theorem-of-calculus        *)
(*     machinery (RInt_Derive); theorems that do not route through FTC are    *)
(*     fully constructive (modulo the three Stdlib Dedekind-real axioms).    *)
(*                                                                            *)
(*     A full elimination of Classical_Prop.classic requires replacing       *)
(*     Coquelicot's classical integration layer with a constructive one      *)
(*     (e.g., MathComp analysis, or a hand-rolled is_RInt_intuit framework).  *)
(*     That is documented as a follow-up beyond this audit.                   *)
(*                                                                            *)
(*     Below we collect the constructive-core theorems whose axiom            *)
(*     footprint is exactly the three Stdlib Dedekind-real axioms             *)
(*     (sig_forall_dec, sig_not_dec, functional_extensionality_dep). Each     *)
(*     Print Assumptions check witnesses the absence of classic.             *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals.
From PBAvalanche Require Import
  pb_avalanche
  pb_avalanche_units
  pb_avalanche_units_q
  pb_avalanche_dr_framework
  pb_avalanche_nuclear
  pb_avalanche_eddington
  pb_avalanche_ash
  pb_avalanche_energy_balance.

Open Scope R_scope.

(* ================================================================== *)
(* === Constructive-core theorems === *)
(* ================================================================== *)

(* The abstract framework's Hora-Putvinski settlement is constructive
   in every concrete instantiation that does not use Coquelicot's
   integral derivation. *)

Print Assumptions ConcreteSettlement.hora_putvinski_settlement.
Print Assumptions ConcreteSettlement.reactor_no_multiplication.
Print Assumptions ConcreteSettlement.reactor_no_marginal.
Print Assumptions ConcreteSettlement.reactor_safety_margin_positive.

Print Assumptions PhysicalSettlement.hora_putvinski_settlement.
Print Assumptions PhysicalSettlement.reactor_no_multiplication.

Print Assumptions SaturatedSettlement.hora_putvinski_settlement.
Print Assumptions LinearCrossSectionSettlement.hora_putvinski_settlement.

Print Assumptions SolarSettlement.hora_putvinski_settlement.
Print Assumptions solar_no_avalanche.
Print Assumptions solar_safety_margin.

(* Algebraic/dimensional content is constructive. *)
Print Assumptions unit_mul_inv_r.
Print Assumptions unit_pow_add.
Print Assumptions multiplication_factor_unit_dimensionless.
Print Assumptions unit_mul_q_inv_r.
Print Assumptions sqrt_unit_squared.
Print Assumptions sqrt_T_unit_squared_is_T.

(* The Coulomb-strength ordering for nuclear reactant pairs:
   constructive. *)
Print Assumptions coulomb_barrier_ordering.
Print Assumptions Q_value_ordering.

(* Ash self-quenching and energy-balance constraints: constructive. *)
Print Assumptions tau_slow_alpha_ash_decreasing.
Print Assumptions M_ash_decreasing.
Print Assumptions energy_balance_density_constraint.

(* DR-typed dimensional balance: constructive. *)
Print Assumptions dr_rate_ratio_unit.
Print Assumptions rate_two_density_ratio_dimensionless.
Print Assumptions reaction_freq_unit_value.

(* Witness states: the rescaled-units concrete witness, the physical
   witness, the corner witness, and the solar instance all close
   constructively (no classical reasoning needed for these
   first-order arithmetic statements). *)
Print Assumptions witness_no_avalanche.
Print Assumptions physical_witness_no_avalanche.
Print Assumptions saturated_corner_witness_M_value.
Print Assumptions saturated_FoM_max_loose.

(* ================================================================== *)
(* === Final wrap-up theorem: the constructive Hora-Putvinski =====   *)
(* ================================================================== *)

(* A bundled compound statement of the constructive-core content of
   the avalanche settlement: each conjunct is one of the framework's
   classical-free conclusions, all assembled into a single closing
   theorem. The classical axiom is NOT invoked in any branch — only
   the three Stdlib Dedekind-real axioms appear in the assumption
   footprint, as the audit checks below confirm. *)

Theorem hora_putvinski_constructive :
  (* (A) Concrete-rescaled settlement *)
  (forall s, ConcreteSettlement.reactor_regime s ->
             ConcreteSettlement.multiplication_factor s < 1) /\
  (* (B) Physical-scale settlement *)
  (forall s, PhysicalSettlement.reactor_regime s ->
             PhysicalSettlement.multiplication_factor s < 1) /\
  (* (C) Saturated-integral settlement *)
  (forall s, SaturatedSettlement.reactor_regime s ->
             SaturatedSettlement.multiplication_factor s < 1) /\
  (* (D) Linear-cross-section settlement *)
  (forall s, LinearCrossSectionSettlement.reactor_regime s ->
             LinearCrossSectionSettlement.multiplication_factor s < 1) /\
  (* (E) Solar (Eddington) settlement *)
  (forall s, SolarSettlement.reactor_regime s ->
             SolarSettlement.multiplication_factor s < 1) /\
  (* (F) Dimensional balance: M ratio is dimensionless *)
  (unit_div rate_unit rate_unit = zero_unit) /\
  (* (G) Sharp dichotomy: M != 1 on the regime *)
  (forall s, ConcreteSettlement.reactor_regime s ->
             ConcreteSettlement.multiplication_factor s <> 1).
Proof.
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))).
  - exact ConcreteSettlement.reactor_no_multiplication.
  - exact PhysicalSettlement.reactor_no_multiplication.
  - exact SaturatedSettlement.reactor_no_multiplication.
  - exact LinearCrossSectionSettlement.reactor_no_multiplication.
  - exact SolarSettlement.reactor_no_multiplication.
  - exact multiplication_factor_unit_dimensionless.
  - exact ConcreteSettlement.reactor_no_marginal.
Qed.

Print Assumptions hora_putvinski_constructive.
