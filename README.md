# Proton-Boron Avalanche Fusion: Verified Bounds on Chain Multiplication

A Rocq formalization of the kinetic rate equations for alpha-induced
secondary p+11B reactions, settling the Hora-Putvinski avalanche
dispute by establishing necessary and sufficient conditions for the
secondary-to-primary multiplication factor to exceed unity, and
exhibiting explicit numerical realizations at both rescaled and
physical reactor parameters in which the multiplication factor is
strictly below unity throughout the reactor regime.

The development has grown well beyond the original settlement into a
broad library of verified plasma-physics and numerical-analysis
results under `theories/`, compiling clean on Rocq 9.0 with Coquelicot
3.4.4, with its axiom footprint guarded at build time (see *Axiom
footprint* below).

## The core settlement

**Abstract framework (Module Type `PB_AVALANCHE_PARAMS`).**
Encapsulates the kinetic input as named parameters: the primary and
knock-on cross sections, the Spitzer-Trubnikov constant, the alpha
velocity bound, the alpha-distribution-weighted velocity integral, and
the reactor regime parameters `n_B_max`, `T_max`, `n_p_min`, with
positivity, bound, and numerical-subcriticality axioms.

**Framework functor (`PBAvalancheFramework`).** Defines
`tau_slow_alpha`, `f_alpha`, `R_primary`, `R_secondary`, recovers the
three closed-form physical identities (Spitzer-Trubnikov slowing-down
time, slowing-down Fokker-Planck equilibrium, bilinear kinetic
decomposition of the secondary rate) as definitional lemmas, and proves

1. `multiplication_factor s = avalanche_figure_of_merit s` for every
   plasma state, the figure of merit being
   `3 * n_B * tau_slow_alpha * <sigma_knockon * v>_alpha`;
2. `tau_slow_alpha s <= tau_max_reactor` throughout the reactor regime;
3. `avalanche_figure_of_merit s <= FoM_max_reactor` throughout;
4. `multiplication_factor s < 1` throughout, by composing the bound with
   the numerical subcriticality axiom.

**Concrete instantiations.** Six modules satisfy `PB_AVALANCHE_PARAMS`
on zero project-local axioms: `ConcreteParams` (rescaled, bound 3/100),
`PhysicalParams` (reactor units, bound ~3e-13), `SaturatedParams`
(alpha integral at its pointwise upper bound), `IntegralParams` and
`LinearIntegralParams` (alpha integral defined as a literal Coquelicot
Riemann integral and its closed form derived), and the stellar
`SolarParams` (Eddington's self-regulation, `pb_avalanche_eddington.v`).
The `Corner` functor (`pb_avalanche_corner.v`) proves `FoM_max_reactor`
is the attained supremum over the regime.

## Quantitative bounds

| Instantiation | `FoM_max_reactor` | Safety margin |
|---|---|---|
| `ConcreteSettlement`           | `3 / 100`     | `M(s) <= 3/100` |
| `PhysicalSettlement`           | `~3 / 10^13`  | `M(s) <= 10^-12` |
| `SaturatedSettlement`          | `3 / 100`     | `M(s) <= 3/100` |
| `LinearCrossSectionSettlement` | `3 / 100`     | `M(s) <= 3/100` |
| `IntegralSettlement`           | `3 / 100`     | `M(s) <= 3/100` |
| `LinearIntegralSettlement`     | `3 / 100`     | `M(s) <= 3/100` |

The contrapositive `reactor_avalanche_impossible` makes the no-go
content explicit: any state with `multiplication_factor >= 1` violates
the reactor regime.

## Supporting numerical analysis and physics

Beyond the settlement, the library mechanises the analytic and
numerical apparatus the rate equations rest on. Items below are proved
with complete `Qed` proofs (no `Admitted`, no project-local axioms):

- **Piecewise-linear IAEA interpolation** (`pb_avalanche_iaea.v`):
  sup-norm and two-sided bounds, C^0 continuity of the zero-extended
  interpolant, trapezoidal integration error, and the Sikora-Weller
  p-11B cross-section table.
- **Cubic Hermite splines and tight interpolation error**
  (`pb_avalanche_spline.v`): endpoint interpolation, the linear-reduction
  identity, and the sharp `M_2 (b-a)^2 / 8` bound, derived via the Cauchy
  divided-difference mean value theorem — Rolle's theorem applied three
  times, bridged from Coquelicot `is_derive` to the Stdlib `Rolle`
  (interior-point) theorem through `is_derive_Reals`.
- **Romberg / Euler-Maclaurin** (`pb_avalanche_romberg.v`): the
  composite trapezoidal rule for
  `x^2` computed in closed form via the sum-of-squares formula, shown to
  equal the exact integral plus exactly `(b-a)^3 / (6 n^2)`, with
  level-1 Richardson extrapolation proved exact; Bernoulli-number
  recurrence checks and the general level-k Richardson cancellation.
- **Constructive integration** (`pb_avalanche_constructive.v`):
  a `Classical_Prop.classic`-free midpoint Riemann integral with FTC for
  constants and the identity, additivity, scalar homogeneity, and
  monotonicity (the `RInt_le` analogue) — all on the Dedekind axioms
  alone.
- **3D Fubini** (`pb_avalanche_spatial.v`): nested `RInt` commutativity
  for the separable span, hence for the whole polynomial algebra via
  additivity, plus box volumetric averaging.
- **Gamow tunneling and Coulomb waves** (`pb_avalanche_gamow.v`): the
  Gamow-peak stationary point, the
  Sommerfeld parameter, and the s-wave Coulomb coefficients proved to
  satisfy the Coulomb wave equation term-by-term, matching the
  semiclassical Gamow factor in the high-barrier limit.
- **Spitzer constants and Coulomb logarithm** (`pb_avalanche_spitzer_constants.v`,
  `pb_avalanche_spitzer_numerical.v`, `pb_avalanche_coulomb_log.v`):
  dimensional signatures, the Spitzer prefactor scaling laws, and the
  NRL Coulomb-log evaluated to 23.5 at canonical reactor parameters.
- **Maxwellian reactivity** (`pb_avalanche_maxwellian_sw.v`): a
  positive thermal reactivity over the Sikora-Weller table.
- **Time evolution via Picard** (`pb_avalanche_ash.v`): the affine
  ash-production ODE solved in closed form, and a general Picard
  fixed-point operator proved to generate the closed-form iterates.
- **Kinetic theory** (`pb_avalanche_sw_kinetic.v`,
  `pb_avalanche_fokker_planck.v`): the BGK relaxation collision
  operator with mass conservation, exact relaxation dynamics and
  monotone H-decay; and the weak-derivative integration-by-parts
  identity (`<phi', psi> = -<phi, psi'>` for compactly supported test
  functions) underlying the distributional Fokker-Planck formulation.
- **Radiation** (`pb_avalanche_energy_balance.v`,
  `pb_avalanche_synchrotron.v`): the relativistic bremsstrahlung
  correction derived from the Lorentz factor `beta^2 = 1 - 1/gamma^2`
  (with the non-relativistic limit recovered as a derivative match at
  zero energy and a speed-suppression inequality), and the synchrotron
  Larmor power with its `B^2`, `gamma^2`, inverse-mass scalings.
- **Generalised frameworks** (`pb_avalanche_units_q.v`,
  `pb_avalanche_dr_framework.v`, `pb_avalanche_nuclear.v`,
  `pb_avalanche_energy_resolved.v`, `pb_avalanche_chain.v`):
  Q-exponent dimensional algebra with nth roots; a DR-typed parameter
  interface; `NUCLEAR_AVALANCHE_PARAMS` instantiated for p-11B, D-3He,
  D-D; an energy-resolved velocity kinetic model; per-generation chain
  rates with geometric-series total.
- **Hora-paper rebuttal** (`pb_avalanche_hora_rebuttal.v`): the claimed
  avalanche-enhancement factor is shown to remain subcritical for any
  enhancement below the explicit kinematic threshold.
- **Axiom irreducibility** (`pb_avalanche_audit.v`): the
  reverse-mathematics equivalences `classic <-> DNE <-> Peirce`, the de
  Morgan implication, and concrete witnesses that functional
  extensionality and the Dedekind decidability axioms each do real work.

## Axiom footprint

Every theorem closes by `Qed`. There are no `Admitted`/`admit` proofs
and no project-local axioms anywhere. The combined axiom footprint is:

    ClassicalDedekindReals.sig_forall_dec
    ClassicalDedekindReals.sig_not_dec
    FunctionalExtensionality.functional_extensionality_dep
    Classical_Prop.classic

`sig_forall_dec`, `sig_not_dec`, and `functional_extensionality_dep` are
the Stdlib Dedekind-real axioms; `Classical_Prop.classic`
(excluded middle) is pulled in only by Coquelicot's
fundamental-theorem-of-calculus machinery. The constructive-integration
file demonstrates that the FTC layer can be re-derived without it: its
results stand on the Dedekind axioms alone.

`theories/pb_avalanche_audit.v` runs `Print Assumptions` on the exported
results across the development, and `scripts/check_axioms.sh` (the
`make audit-check` target) fails the build if the realised axiom set
ever diverges from `scripts/expected_axioms.txt`.

## Building

```
make              # generates Makefile.coq via `rocq makefile`, compiles theories/
make audit-check  # rebuilds the audit and enforces the axiom manifest
```

## Dependencies

- Rocq 9.0 with Stdlib `Reals`, `Lra`, `Lia`, `ZArith`, `QArith`, `List`.
- Coquelicot 3.4 for integrals, derivative chains, the fundamental
  theorem of calculus, and `is_derive`/`Rolle` bridging.

## Scope

The settlement covers the magnetic-confinement regime where the boron
density is bounded by `n_B_max_reactor`. It does not directly model
laser-driven fast-ignition at solid-density boron, which violates the
regime hypotheses of every instantiation here; such a configuration
would require a different parameter spec (and re-verification of the
subcriticality axiom at the new values). The supporting physics files
(Bethe-Heitler, Boltzmann/BGK, distributional Fokker-Planck, Coulomb
waves) formalise leading-order and model-level results — the relevant
closed forms, conservation laws, term-by-term ODE relations, and limit
correspondences — rather than the full transport solutions.

## References

- A. S. Eddington. The internal constitution of the stars.
  *Observatory*, 43:341-358, 1920.
- L. Spitzer Jr. *Physics of Fully Ionized Gases.* 2nd ed.,
  Interscience Publishers, 1962.
- W. M. Nevins and R. Swain. The thermonuclear fusion rate
  coefficient for p-11B reactions. *Nuclear Fusion*,
  40(4):865-872, 2000.
  [DOI: 10.1088/0029-5515/40/4/310](https://doi.org/10.1088/0029-5515/40/4/310)
- M. H. Sikora and H. R. Weller. A new evaluation of the 11B(p,alpha)alpha-alpha
  reaction rates. *J. Fusion Energy*, 35:538-543, 2016.
  [DOI: 10.1007/s10894-016-0069-y](https://doi.org/10.1007/s10894-016-0069-y)
- H. Hora, S. Eliezer, G. J. Kirchhoff, N. Nissim, J. X. Wang,
  P. Lalousis, Y. X. Xu, G. H. Miley, J. M. Martinez-Val, and
  G. Korn. Road map to clean energy using laser beam ignition of
  boron-hydrogen fusion. *Laser and Particle Beams*,
  35(4):730-740, 2017.
  [DOI: 10.1017/S0263034617000799](https://doi.org/10.1017/S0263034617000799)
- S. V. Putvinski, D. D. Ryutov, and P. N. Yushmanov. Fusion
  reactivity of the pB11 plasma revisited. *Nuclear Fusion*,
  59(7):076018, 2019.
  [DOI: 10.1088/1741-4326/ab1a60](https://doi.org/10.1088/1741-4326/ab1a60)

## License

MIT
