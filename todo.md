# TODO

Status of the 15-item deepening program. Items are the original work
list; "done" means proved in Coq, compiled on the Ragnarok rocq9 switch
(Coquelicot 3.4.4), with the axiom footprint limited to the three Stdlib
Dedekind-real axioms plus `Classical_Prop.classic` (excluded middle,
from Coquelicot's fundamental-theorem-of-calculus machinery). No
`Admitted`, no project-local axioms.

## Done

- **Item 1** — `R_secondary` derived from the Fokker-Planck collision
  integral; `R_secondary_bilinear_factorization` and the substantive
  `multiplication_factor_kinetic_eq_FoM` in `pb_avalanche_kinetic.v`.
- **Item 2** — `kinetic_FoM_upper_bound` and `kinetic_no_avalanche`:
  the bound `3·n_B·tau·L·sigma·v < 1` implies `M < 1`.
- **Item 9** — 1/E slowing-down spectrum carried through, integrable on
  `[E_min, E_birth]`; `RInt_inv_E`, `RInt_f_slowing`, `sigma_v_kinetic`,
  `sigma_v_kinetic_bound`.
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
- **Items 7, 8** — admissible envelope (`admissible`,
  `envelope_subcritical`) and the Hora regime (`hora_admissible`,
  `hora_regime_no_avalanche`) in `pb_avalanche_envelope.v`.

## Remaining

- **Item 4 (partial, WIP in `pb_avalanche_thermal.v`, not yet in the
  build)** — Maxwellian-averaged reactivity. Done: the thermal
  normalization integral `RInt_exp_thermal`
  (`integral_0^b exp(-E/T) dE = T(1 - exp(-b/T))`, via FTC with
  antiderivative `-T exp(-E/T)`) and `is_derive_neg_T_exp`. Open: the
  Coquelicot continuity combinator obligations in
  `continuous_exp_thermal` (resolving `continuous_opp` /
  `continuous_id` instances), and the downstream `reactivity_bound` /
  `R_primary_thermal_*` lemmas. Re-add the file to `_CoqProject` once
  green.

- **Item 3** — IAEA-evaluated p-11B cross sections: a discrete
  `(E_i, sigma_i)` table, piecewise-linear interpolation, the
  trapezoidal integral of the interpolant, and the integral error
  carried as an explicit bounded term
  `|RInt sigma_true - RInt sigma_interp| <= eps * (b - a)` via
  `abs_RInt_le` and `RInt_minus`.

- **Item 5** — Spitzer-Trubnikov `tau ~ T^{3/2}/n` from the Coulomb
  collision operator, recovering the scaling and the Coulomb logarithm
  `ln Lambda` as an explicit bounded term.

- **Item 6** — dimensional types: a unit-indexed real type with the
  typechecker enforcing dimensional homogeneity, so every expression
  carries units and they must balance.

- **Item 15** — aggregate the header claims: a final theorem chain
  proving the necessary-and-sufficient conditions, the IAEA-evaluated
  cross-section bound, and the Hora-Putvinski settlement, by composing
  items 1-14.

## Build note

Compiled on Ragnarok (`rocq9` opam switch, Coquelicot 3.4.4) because the
SAURON-side WSL toolchain wedged. Sync working tree to
`ragnarok:~/pb-avalanche-verified/` and run
`eval $(opam env --switch=rocq9) && make -f Makefile.coq`.
