# TODO

Status of the 15-item deepening program. **All items now complete.**

Each "done" entry is proved in Coq, compiled clean on the `rocq9` opam
switch (Coquelicot 3.4.4), and audited with `Print Assumptions`. The
combined axiom footprint over the whole development is exactly the
three Stdlib Dedekind-real axioms

    ClassicalDedekindReals.sig_forall_dec
    ClassicalDedekindReals.sig_not_dec
    FunctionalExtensionality.functional_extensionality_dep

plus `Classical_Prop.classic` (excluded middle, pulled in by
Coquelicot's fundamental-theorem-of-calculus machinery). No
`Admitted`, no `admit`, no project-local axioms.

## Done

- **Item 1** — `R_secondary` derived from the Fokker-Planck collision
  integral; `R_secondary_bilinear_factorization` and the substantive
  `multiplication_factor_kinetic_eq_FoM` in `pb_avalanche_kinetic.v`.
- **Item 2** — `kinetic_FoM_upper_bound` and `kinetic_no_avalanche`:
  the bound `3·n_B·tau·L·sigma·v < 1` implies `M < 1`.
- **Item 3** — IAEA-evaluated p-11B cross sections in
  `pb_avalanche_iaea.v`: a discrete `(E_i, sigma_i)` table type,
  piecewise-linear interpolant `interp_linear`, the trapezoidal sum
  `trap_integral`, the integral equivalence
  `RInt_interp_linear_eq_trap`, and the explicit interpolation error
  bound `interp_error_bound` proved via `abs_RInt_le`, `ex_RInt_norm`,
  and `RInt_minus`.
- **Item 4** — Maxwellian-averaged reactivity in
  `pb_avalanche_thermal.v`. Thermal normalization integral
  `RInt_exp_thermal` via FTC with antiderivative `-T·exp(-E/T)`, plus
  `reactivity_nonneg`, `reactivity_bound`, `R_primary_thermal_*`. The
  `continuous_exp_thermal` typeclass mismatch was resolved by routing
  `exp(-x/T)` through the algebraic rewrite `x * (- / T)` (the helper
  lemma `exp_thermal_rewrite`).
- **Item 5** — Spitzer-Trubnikov slowing-down time and the Coulomb
  logarithm in `pb_avalanche_spitzer.v`: `tau_spitzer`,
  `tau_spitzer_scaling_T` (the `T^(3/2)` law), `tau_spitzer_scaling_n`,
  `tau_spitzer_sandwich` carrying explicit `ln_Lambda_min = 10` and
  `ln_Lambda_max = 25` envelope bounds, the Coulomb energy-loss
  equation `coulomb_Edot`, and the steady-state slowing flux identity
  `slowing_flux_value`.
- **Item 6** — dimensional types in `pb_avalanche_units.v`:
  `Unit` record over six base SI exponents, the unit algebra
  (`unit_mul_zero_l/r`, `unit_mul_assoc`, `unit_mul_inv_r`,
  `unit_pow_add`), the dimensional-real type `DR u`, lift/unlift,
  typed arithmetic operations, and a dimensional check that the
  multiplication factor reduces to `zero_unit`
  (`multiplication_factor_unit_dimensionless`).
- **Item 7** — the admissible parameter envelope
  (`admissible`, `admissible_product_subcritical`, `envelope_subcritical`)
  in `pb_avalanche_envelope.v`.
- **Item 8** — the Hora regime (`hora_admissible`,
  `hora_regime_no_avalanche`) in `pb_avalanche_envelope.v`: Putvinski's
  rebuttal formalized.
- **Item 9** — the 1/E slowing-down spectrum carried through,
  integrable on `[E_min, E_birth]`; `RInt_inv_E`, `RInt_f_slowing`,
  `sigma_v_kinetic`, `sigma_v_kinetic_bound`.
- **Item 10** — `f_slowing` proved the steady-state Fokker-Planck
  solution: `slowing_flux_constant`, `slowing_down_steady_state`,
  `source_equals_sink`, `slowing_flux_steady_derivative`.
- **Item 11** — energy-resolved `integral(f sigma v)`;
  `R_secondary_kinetic` and its factorization.
- **Item 12** — competing channels: `tau_eff` (harmonic combination),
  `channels_preserve_bound`, `channels_no_avalanche`, helium-ash and
  sub-threshold exclusion from the reactive window.
- **Item 13** — matching lower bound: `sigma_v_kinetic_lower_bound`,
  `kinetic_FoM_lower_bound`, `kinetic_FoM_sandwich`, `kinetic_FoM_gap`.
- **Item 14** — `B_T` coupling: `larmor_radius` decreasing in B,
  `tau_confine_of_B` increasing, `residence_monotone_in_B`,
  `B_field_bounded_multiplication`, `B_field_no_avalanche`.
- **Item 15** — aggregate final theorem `pb_avalanche_settlement` in
  `pb_avalanche_final.v`: a single closing statement composing the
  bilinear factorization (item 1), the subcriticality criterion (item
  2), the two-sided FoM sandwich (item 13), the admissible envelope
  (item 7), the Hora rebuttal (item 8), the steady-state flux identity
  (item 10), the Spitzer scaling (item 5), the IAEA error bound (item
  3), the dimensional balance (item 6), and the six-instance
  uniform subcriticality (items 7-14 across all `PB_AVALANCHE_PARAMS`
  instantiations).

## Build

```
eval $(opam env --switch=rocq9)
make
```

All nine files in `theories/` compile cleanly:

- `pb_avalanche.v`
- `pb_avalanche_integral.v`
- `pb_avalanche_kinetic.v`
- `pb_avalanche_envelope.v`
- `pb_avalanche_thermal.v`
- `pb_avalanche_spitzer.v`
- `pb_avalanche_iaea.v`
- `pb_avalanche_units.v`
- `pb_avalanche_final.v`
