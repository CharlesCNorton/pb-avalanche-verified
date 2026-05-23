# TODO

**All 30 items of the next-generation deepening program are complete.**

Total content: 25 files under `theories/`, all compile clean on the
`rocq9` opam switch (Coquelicot 3.4.4). Combined axiom footprint over
the whole development is the three Stdlib Dedekind-real axioms plus
`Classical_Prop.classic` (the latter pulled in by Coquelicot's
fundamental-theorem-of-calculus machinery, isolated to the
integration-derivation files). The constructive-core subset
(`pb_avalanche_constructive.v`) closes by Qed without
`Classical_Prop.classic`.

## Completed

- **Item 1** — `auto_derive` replaced with explicit `is_derive_mult /
  comp / const / id / exp / inv` chains in `pb_avalanche_thermal.v`
  and `pb_avalanche_iaea.v`.
- **Item 2** — `pb_avalanche_audit.v` enumerates `Print Assumptions`
  for every named theorem in the development.
- **Item 3** — `n_alpha_from_source_and_residence` and
  `R_secondary_bilinear_via_n_alpha` name the kinematic identity
  bridging the two factorizations.
- **Item 4** — `sigma_v_kinetic_constant_value` closed-form for
  constant sigma_E, v_E.
- **Item 5** — `reactor_no_marginal` / `reactor_FoM_no_marginal`
  prove `M ≠ 1` on the regime.
- **Item 6** — `interp_linear_continuous_on` global continuity via
  trichotomy + `continuous_piecewise_at` join lemma.
- **Item 7** — `interp_linear_ext` (zero-extended interpolant),
  `interp_linear_ext_below/above/inside`,
  `RInt_interp_linear_ext_eq_trap`.
- **Item 8** — `iter_witness_no_avalanche` threads B = 5 T through
  `tau_eff_B`, with `iter_witness_monotone_in_B`.
- **Item 9** — `interp_segment_curvature_error`: per-segment bound
  `M_2 * (b-a)^2` via three `MVT_gen` applications. The tight
  `M_2 * (b-a)^2 / 8` constant via Rolle's-twice is a future
  refinement.
- **Item 10** — `pb_avalanche_romberg.v`: `trap_pow2`,
  `romberg_table`, `romberg`; `romberg_const`, `romberg_RInt_const`,
  `romberg_single`. The full `O(h^{2k+2})` convergence rate is a
  future refinement.
- **Item 11** — `RInt_exp_thermal_half_line` shows the integral over
  `[0, +∞)` equals T via `is_lim_seq` of the closed form `T(1 - e^{-b/T})`.
- **Item 12** — `tau_s_E_dep`, `Edot_E_dep_closed_form`,
  `f_slowing_E_dep_scaling`, `slowing_flux_E_dep_constant` give the
  energy-dependent slowing-down model with `tau_s(E) ∝ sqrt E`.
- **Item 13** — `saturated_corner_witness` exhibits the tightest
  achievable `M = 3/2600`, `saturated_FoM_max_loose` documents the
  framework bound's 26× looseness.
- **Item 14** — `sikora_weller_pB_table` (20 points), proved sorted
  with integral identity. `sikora_weller_M_inf`, `sikora_weller_M_2`
  expose the Breit-Wigner bounds.
- **Item 15** — `pb_avalanche_units_q.v` with Q-exponent `UnitQ`
  type, group laws, `sqrt_unit_squared`, `inject_Z_unit` embedding
  the Z-exponent units.
- **Item 16** — `pb_avalanche_dr_framework.v` with
  `dr_multiplication_factor`, `dr_rate_ratio_unit` (proves the M
  ratio is dimensionless by type), `reaction_freq_unit`,
  `rate_two_density_unit`.
- **Item 17** — `pb_avalanche_spitzer_constants.v`: physical
  constants (`mass_unit_q`, `length_unit_q`, `eps_0_unit_q`,
  `k_B_unit_q`, `hbar_unit_q`) and `tau_signature_components`.
- **Item 18** — `lambda_Debye`, `b_min_quantum`, `b_min_classical`,
  `coulomb_log_derived`, with the envelope theorem
  `coulomb_log_derived_envelope` proving `ln Λ ∈ [10, 25]` under
  exp-bracketed numerical bounds.
- **Item 19** — `pb_avalanche_gamow.v`: `gamow_factor`,
  `sigma_gamow`, `maxwellian_gamow_integrand`,
  `gamow_peak_monotone_T` with `T^{2/3}` scaling.
- **Item 20** — `pb_avalanche_fokker_planck.v`: `FP_op` (drift +
  diffusion), `FP_drift`, `FP_drift_slowing`, `FP_op_slowing_no_diffusion`.
- **Item 21** — `pb_avalanche_sw_kinetic.v`: `SikoraWellerKineticParams`
  instance with `sigma_E_max := sikora_weller_M_inf`,
  `SW_K_FoM_upper_bound`.
- **Item 22** — `thermal_R_prim` (= n_p · n_B · sv_avg),
  `thermal_kinetic_no_avalanche`, `thermal_kinetic_iter_no_avalanche`
  in `pb_avalanche_envelope.v`.
- **Item 23** — `pb_avalanche_ash.v`: `PlasmaStateAsh` with `n_ash`,
  `n_eff_with_ash`, `tau_slow_alpha_ash_decreasing`,
  `M_ash_decreasing` (self-quenching).
- **Item 24** — `pb_avalanche_chain.v`: `M_chain_total = / (1 - M)`
  via `Series_geom`, `chain_total_at_concrete = 100/97`,
  `chain_diverges_at_one` divergence for M ≥ 1.
- **Item 25** — `pb_avalanche_spatial.v`: `PlasmaProfile`,
  `M_volumetric`, `M_volumetric_pointwise_bound`,
  `M_volumetric_uniform`.
- **Item 26** — `pb_avalanche_energy_balance.v`: `bremsstrahlung`,
  `synchrotron`, `energy_balance_admissible`,
  `energy_balance_density_constraint`.
- **Item 27** — `pb_avalanche_laser.v`: `laser_witness_n_B`,
  `laser_witness_above_unity` (3·ln 2 > 1) exhibits a state with
  composite product above unity, `laser_witness_outside_magnetic_envelope`.
- **Item 28** — `pb_avalanche_nuclear.v`: `NUCLEAR_REACTANTS`
  module type, instantiated for p-11B, D-³He, D-D;
  `coulomb_barrier_ordering` and `Q_value_ordering`.
- **Item 29** — `pb_avalanche_eddington.v`: `SolarParams` (n_p = 10²⁵,
  T = 100 keV, sigma = 10⁻⁴⁹), `solar_no_avalanche`,
  `solar_safety_margin`.
- **Item 30** — `pb_avalanche_constructive.v`: `hora_putvinski_constructive`
  bundles the classical-free subset (Concrete, Physical, Saturated,
  LinearCrossSection, Solar settlements + dimensional balance + sharp
  dichotomy) and verifies via `Print Assumptions` that this subset
  closes without `Classical_Prop.classic`. The full constructive
  re-derivation of Coquelicot's FTC machinery — to eliminate classic
  from the integral-derivation files — is documented as a deeper
  follow-up.

## Build

```
eval $(opam env --switch=rocq9)
make
```

All 25 files in `theories/` compile clean:

- `pb_avalanche.v` (abstract framework + 4 instantiations + saturated
  corner witness + sharp dichotomy)
- `pb_avalanche_integral.v` (Coquelicot-derived bound + 2 more
  instantiations)
- `pb_avalanche_kinetic.v` (energy-resolved kinetic framework + tau_E_dep)
- `pb_avalanche_envelope.v` (admissible envelope + Hora rebuttal +
  ITER witness + thermal-kinetic connection)
- `pb_avalanche_thermal.v` (Maxwellian reactivity + half-line integral)
- `pb_avalanche_spitzer.v` (Spitzer-Trubnikov + Coulomb-log envelope)
- `pb_avalanche_iaea.v` (interp_linear + curvature error + Sikora-Weller)
- `pb_avalanche_units.v` (Z-exponent dimensional types)
- `pb_avalanche_final.v` (aggregate settlement)
- `pb_avalanche_audit.v` (per-theorem `Print Assumptions`)
- `pb_avalanche_units_q.v` (Q-exponent dimensional types)
- `pb_avalanche_dr_framework.v` (DR-typed multiplication factor)
- `pb_avalanche_spitzer_constants.v` (physical constants + signature)
- `pb_avalanche_gamow.v` (Gamow cross section + peak scaling)
- `pb_avalanche_fokker_planck.v` (FP operator + drift case)
- `pb_avalanche_sw_kinetic.v` (Sikora-Weller kinetic instance)
- `pb_avalanche_ash.v` (helium-ash self-quenching)
- `pb_avalanche_chain.v` (geometric chain sum)
- `pb_avalanche_romberg.v` (Richardson extrapolation)
- `pb_avalanche_spatial.v` (radial volumetric integration)
- `pb_avalanche_energy_balance.v` (bremsstrahlung + synchrotron)
- `pb_avalanche_laser.v` (laser regime explicit out-of-scope)
- `pb_avalanche_nuclear.v` (D-³He, D-D generalization)
- `pb_avalanche_eddington.v` (solar instantiation)
- `pb_avalanche_constructive.v` (classical-free subset)
