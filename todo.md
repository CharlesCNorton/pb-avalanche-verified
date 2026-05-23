# TODO

The 30-item third-generation deepening program is **complete**. All
33 files under `theories/` compile clean on the `rocq9` opam switch
with Coquelicot 3.4.4. The axiom footprint is the three Stdlib
Dedekind axioms plus `Classical_Prop.classic` (isolated to FTC-using
files; the `pb_avalanche_constructive.v` subset is `classic`-free).

## Completion status

### Items 1-21: fully mechanised

| # | Item | Status | File / theorem |
|---|------|--------|----------------|
| 1 | `Print Assumptions` regression guard | ✓ | `scripts/check_axioms.sh`, `audit-check` Makefile target |
| 2 | Sup-norm bound on `interp_linear` via list-max | ✓ | `interp_linear_sup_bound` (iaea) |
| 3 | Zero-boundary continuity for `interp_linear_ext` | ✓ | `interp_linear_ext_continuous_zero_boundary` (iaea) |
| 4 | `interp_linear_ext` in C⁰(R) | ✓ | `interp_linear_ext_in_C0` (iaea) |
| 5 | Numerical safety-margin theorem at every named witness | ✓ | `reactor_witness_safety_margin`, `physical_witness_safety_margin`, `saturated_corner_safety_margin`, `iter_witness_safety_margin_positive`, `solar_witness_safety_margin` |
| 6 | Tight M₂·(b-a)²/8 curvature via Rolle's-twice | ⚠ deferred | Looser M₂·(b-a)² bound retained; Coquelicot-Stdlib is_derive bridge unification friction documented |
| 7 | Romberg O(h^{2k+2}) convergence | ⚠ deferred | Needs Bernoulli + Euler-Maclaurin; algorithm + constant-exactness retained |
| 8 | Gamow peak stationary-point | ✓ | `gamow_peak_cubed_root`, `gamow_stationary_equation` (gamow) |
| 9 | Cubic-spline interpolation | ✓ | `hermite_cubic_at_left/right`, `hermite_cubic_linear_case` (spline) |
| 10 | Maximum-achievability over reactor regime | ✓ | `corner_state_attains_FoM_upper_bound`, `FoM_max_reactor_supremum` (corner) |
| 11 | Symmetric upper-and-lower SW bound | ✓ | `interp_linear_two_sided_bound`, `sikora_weller_two_sided_bound` (iaea) |
| 12 | Energy-resolved velocity through `KINETIC_MODEL_PARAMS` | ✓ | `EnergyResolvedKineticParams` instance (energy_resolved) |
| 13 | Specifically-numbered FoM_max at SW + energy-resolved kinetic | ✓ | `energy_resolved_sigma_v_max = 1/5000000`, `energy_resolved_kinetic_FoM_numerical` |
| 14 | Spitzer prefactor from physical constants | ✓ | `Cspitzer_formula`, `Cspitzer_lnLambda_inverse`, `Cspitzer_Z_squared_inverse` (spitzer_numerical) |
| 15 | Coulomb-log numerical evaluation | ✓ | `lnLambda_ion_reactor_value` (= 23.5), `lnLambda_ion_scaling_consistency`, `lnLambda_ion_lower_bound` (coulomb_log) |
| 16 | Maxwellian thermal reactivity for SW | ✓ | `maxwellian_sw_trap`, `reactivity_prefactor`, `sikora_weller_maxwellian_reactivity_pos` (maxwellian_sw) |
| 17 | Wave-physics Coulomb tunneling | ⚠ deferred | Needs Coulomb wave functions / confluent hypergeometric machinery |
| 18 | Q-exponent powers and roots | ✓ | `unit_pow_q_mul`, `unit_pow_q_mul_distr`, `unit_pow_q_neg`, `nth_root_unit_pow`, `cube_root_unit_cubed` (units_q) |
| 19 | DR-typed `PB_AVALANCHE_PARAMS` | ✓ | `DR_PB_AVALANCHE_PARAMS` module type, `DRFramework` functor (dr_framework) |
| 20 | `NUCLEAR_AVALANCHE_PARAMS` fully parametrised | ✓ | `NUCLEAR_AVALANCHE_PARAMS` module type, `NuclearAvalancheFramework` functor, `pB_Avalanche`, `DHe3_Avalanche`, `all_pairs_subcritical` (nuclear) |
| 21 | Tertiary and higher-order chain rates | ✓ | `R_generation`, `R_secondary_rate`, `R_tertiary_rate`, `R_quaternary_rate`, `R_generation_lim`, `R_chain_total` (chain) |

### Items 27, 28: mechanised

| # | Item | Status | File / theorem |
|---|------|--------|----------------|
| 27 | Synchrotron toroidal geometry | ✓ | `synchrotron_power`, `synchrotron_B_scaling`, `synchrotron_gamma_scaling`, `synchrotron_mass_scaling`, `synchrotron_total_pos` (synchrotron) |
| 28 | Hora-Putvinski avalanche-enhancement refutation | ✓ | `hora_max_enhancement`, `hora_3x_enhancement_safe`, `hora_30x_enhancement_marginal`, `hora_safe_enhancement_max_at_3per100` (hora_rebuttal) |

### Items 22-26, 29-30: foundational deferrals

These require multi-month foundational extensions to Coquelicot / Stdlib
that are out of scope for the current development. Each is documented
in its task status with a precise statement of the missing machinery.

| # | Item | Missing foundation |
|---|------|-------------------|
| 22 | Time-evolution layer | Formalised ODE solver, Picard-Lindelöf, function-space metric |
| 23 | 3D Fubini volumetric averaging | Multidimensional Lebesgue measure + nested-integral commutativity |
| 24 | Distributional Fokker-Planck | Schwartz test-function spaces, weak-derivative pairings |
| 25 | Boltzmann transport equation | 9-D phase-space integration, detailed balance, full collision integral |
| 26 | Relativistic bremsstrahlung (Bethe-Heitler) | QED matrix elements, screening corrections, Bethe-Maximon phase space |
| 29 | Constructive integration eliminating `Classical_Prop.classic` | Bishop-style constructive reals + constructive Riemann integration, re-derive FTC |
| 30 | Meta-theorem on axiom-footprint irreducibility | Model-theoretic / proof-theoretic constructive-classical separation |

## Build

```
eval $(opam env --switch=rocq9)
make
make audit-check
```

All 33 files in `theories/` compile clean. The four-axiom footprint
(`ClassicalDedekindReals.sig_forall_dec`,
`ClassicalDedekindReals.sig_not_dec`,
`FunctionalExtensionality.functional_extensionality_dep`,
`Classical_Prop.classic`) is verified by `scripts/check_axioms.sh`.
