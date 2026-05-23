# TODO

The 30-item next-generation deepening program is complete: 25 files
under `theories/`, all compile clean on the `rocq9` opam switch with
Coquelicot 3.4.4, axiom footprint is the three Stdlib Dedekind axioms
plus `Classical_Prop.classic` (isolated to FTC-using files; the
`pb_avalanche_constructive.v` subset is classic-free).

The list below is the third-generation deepening program: 30 remaining
gaps and weaknesses, each posed as the construction that closes it,
ordered in the logical sequence of completion. Items at the top are
local refinements and hygienic strengthenings; items at the bottom are
deeper analytic and foundational pieces that build on what comes
before.

## Local refinements

- **1. `Print Assumptions` assertion-based regression guard.**
  Replace the descriptive `Print Assumptions` listings in
  `pb_avalanche_audit.v` with a custom tactic `assert_axiom_set : list
  axiom_name -> unit` that programmatically reads the assumption set
  and fails compilation if it diverges from the expected list. The
  audit turns from inspection-based into compile-time-enforced.

- **2. Sup-norm bound on `interp_linear` via the table's value range.**
  Prove `interp_linear_sup_bound : sorted_table T -> forall E in
  [head_E T, last_E T], |interp_linear T E| <= list_max (map snd T)`,
  by induction on the table: each segment value is a convex combination
  of its endpoint values, hence bounded by the maximum.

- **3. Zero-boundary continuity for `interp_linear_ext`.**
  Define `pad_zeros T := (head_E T - 1, 0) :: T ++ [(last_E T + 1, 0)]`
  to produce a zero-boundaried table, and prove
  `interp_linear_ext_continuous : sorted_table T -> head_v T = 0 ->
  last_v T = 0 -> forall E, continuous (interp_linear_ext T) E` —
  the zero extension is continuous globally precisely when the table's
  boundary values vanish.

- **4. `interp_linear_ext` is in `C^0(R)`.**
  Combine items 2 and 3 with the global continuity from the prior
  pass to prove `interp_linear_ext T` is continuous everywhere on R
  for a zero-padded table. This is the precondition for using the
  interpolant as a Schwartz-class object in distributional arguments.

- **5. Numerical safety-margin theorem at every named witness.**
  For each of `reactor_witness_plasma`, `physical_witness_plasma`,
  `saturated_corner_witness`, `iter_n_B`, and a representative solar
  state, compute the explicit closed-form rational of
  `1 - multiplication_factor witness`. The regime-level
  `concrete_safety_margin = 97/100 ≤ 1 - M` becomes the witness-level
  `1 - 3/2600 = 2597/2600` etc.

## Stronger analytic bounds

- **6. Tight `M_2 * (b - a)^2 / 8` curvature error via Rolle's-twice.**
  Bridge `is_derive` to Stdlib's `Reals.MVT.Rolle` via
  `is_derive_Reals` + `derivable_pt_lim`. Construct the auxiliary
  `h(s) := sigma(s) - L(s) - K * (s - a)(s - b)` with K chosen so
  `h(t) = 0`. Apply Rolle to `h` on `[a, t]` and `[t, b]` to obtain α,
  β with `h'(alpha) = h'(beta) = 0`; apply Rolle to `h'` on `[α, β]`
  to obtain ζ with `h''(zeta) = 0`. This forces `K = sigma''(zeta) / 2`,
  and the constant 1/8 comes from
  `max_{t in [a,b]} (t - a)(b - t) = (b - a)^2 / 4`.

- **7. Romberg `O(h^{2k+2})` convergence rate.**
  Prove the trapezoidal-error Taylor expansion `T_n - integral_a^b f
  = c_2 h_n^2 + c_4 h_n^4 + ... + c_{2k} h_n^{2k} + O(h_n^{2k+2})`
  via Euler-Maclaurin with Bernoulli-number coefficients; show that
  Richardson cancellation at level k zeros out `c_2, ..., c_{2k}`
  by linear combination, giving `romberg f a b k - integral_a^b f =
  O(h^{2k+2})`.

- **8. Gamow peak stationary-point derivation.**
  Prove `gamow_peak T` is the unique maximizer of `sigma_gamow(E) *
  exp(-E/T)` over `E > 0`. Set `d/dE [-G(E) - E/T - ln(E)] = 0`,
  approximate the `1/E` term as subdominant in the regime `E >> T`,
  solve `b_G / (2 E^{3/2}) = 1/T` for `E_peak = (b_G * T / 2)^{2/3}`,
  and verify the second-derivative-negative condition.

- **9. Cubic-spline interpolation with `O(h^4)` error.**
  Build `interp_cubic : iaea_table -> R -> R` matching values and
  first derivatives at each node. Prove the error bound
  `||sigma - interp_cubic T||_infty <= C * M_4 * h^4 / 384`
  where `M_4 = sup |sigma^(4)|` and `h` is the maximum mesh spacing.
  Pair with the curvature-error theorem to give a sharper bound on
  IAEA-induced error in `<sigma v>(T)`.

- **10. Maximum-achievability over the full reactor regime.**
  Strengthen `saturated_M_max_achievable` to a universal statement:
  prove `forall s, reactor_regime s -> multiplication_factor s <=
  multiplication_factor saturated_corner_witness`, certifying the
  corner is the unique maximizer. Requires `∂M/∂n_B > 0`,
  `∂M/∂T > 0`, `∂M/∂n_p < 0` on the regime — three calculus
  arguments via Coquelicot's `is_derive_*`.

- **11. Symmetric upper-and-lower SW kinetic bound.**
  Add `sigma_E_min_val := min_v sikora_weller_pB_table` and
  `v_E_min_val` to `SikoraWellerKineticParams`, prove the lower bound
  by table-value inspection, and derive `SWK.kinetic_FoM_sandwich` for
  realistic two-sided bounds. The gap `M_max - M_min` quantifies
  spectrum-shape uncertainty.

## Cross-file integration

- **12. Energy-resolved velocity through `KINETIC_MODEL_PARAMS`.**
  Add `v_E E := sqrt(2 * E / m_alpha)` as a concrete `v_E` in a new
  `KineticPhysicalParams_v_sqrt` instance. Prove `v_E_continuous_on`
  via `continuous_sqrt`, `v_E E <= sqrt(2 * E_birth / m_alpha)`,
  `v_E_min_val = sqrt(2 * E_min / m_alpha)`. Combine with item 2
  (sigma_E from `interp_linear sikora_weller_pB_table`) to produce
  a kinetic instance with both energy-resolved cross section and
  energy-resolved velocity.

- **13. Specifically-numbered `FoM_max` at SW + energy-resolved kinetic.**
  Combine items 2 and 12: wire the SW table and `sqrt(2E/m_alpha)`
  velocity through the kinetic framework, compute
  `FoM_max_realistic := 3 * n_B_max * tau_max * L_kin *
  <interpolated sigma * v>` at `n_B_max = 10^14`, `tau_max = 1 s`,
  `L_kin = ln 2`. Express it as a closed-form rational and verify
  it is strictly less than `3/100`.

## Physical constants from first principles

- **14. Spitzer prefactor numerical match.**
  Compute `Cspitzer_numerical := (3 * sqrt(2*pi) * m_e * sqrt(m_e *
  k_B)) / (4 * Z^2 * e^4 * lnLambda) * (eps_0 * 4*pi)^2` with
  `m_e = 9.109e-31 kg`, `eps_0 = 8.854e-12 F/m`, etc., and verify
  the result equals `5.79e-3 * T^{3/2} / n_e / lnLambda` seconds to
  the rational precision Coq supports. Replace `spitzer_C := 1` in
  `pb_avalanche_spitzer.v` with this derived value and re-verify
  the reactor-regime conclusion.

- **15. Coulomb-log numerical evaluation.**
  Compute `lambda_const := eps_0 * k_B / e^2`, `q_const := hbar /
  sqrt(k_B)`, `c_const := e^2 / (4*pi * eps_0 * k_B)` from physical
  constants; plug `T = 10 keV`, `n_e = 10^20 m^-3`, `m = m_e` into
  `lambda_Debye` and `b_min`; prove `exp 10 <= lambda_Debye / b_min
  <= exp 25` *numerically* (currently this is a hypothesis). Bound
  `exp 10` and `exp 25` by computable rationals via Taylor partial
  sums plus error estimates.

- **16. Maxwellian thermal reactivity computed for the SW cross section.**
  Use `RInt` against `interp_linear sikora_weller_pB_table *
  v_alpha * exp(-E/T)` to compute `<sigma v>(T)` at
  `T in {10, 50, 100, 200, 500} keV`. Verify the thermal peak lies
  near the Gamow peak at each temperature. Pair with item 14 to
  derive `R_primary(T, n_p, n_B) = n_p * n_B * <sigma v>(T)` and
  prove the multiplication-factor bound at each tabulated T.

- **17. Wave-physics Coulomb tunneling.**
  Replace the semiclassical Gamow factor `exp(-G(E))` with the
  exact-Coulomb-wave-function tunneling probability. Build regular
  and irregular Coulomb functions via `RInt` of the WKB integrand,
  match at the nuclear radius, and verify the Gamow factor as the
  leading-order term plus an explicit subleading correction for
  `l > 0` partial waves.

## Architectural strengthenings

- **18. Q-exponent powers and roots.**
  Extend `unit_pow_q u n` to `unit_root_q u k := unit_pow_q u
  (1 # Pos.of_nat k)` for cube roots, fourth roots, etc. Prove
  `(unit_root_q u k)^k = u`. Define DR-typed `dr_sqrt : DR u ->
  DR (unit_root_q u 2)` so `dr_sqrt (dr_T s)` is a typed dimensional
  square root carrying the correct half-temperature exponent.

- **19. DR-typed re-formulation of `PB_AVALANCHE_PARAMS`.**
  Build `PB_AVALANCHE_DR_PARAMS` with every parameter typed:
  `sigma_alpha_p_knockon : R -> DR cross_section_unit`,
  `v_alpha_max : DR velocity_unit`, `Cspitzer : DR (sigma_v_unit /
  (count * temp_unit^(1/2)))`. Refactor the framework functor so
  the multiplication factor's `DR zero_unit` typing is forced by
  type-checking. Migrate every concrete instance to the DR-typed
  variant. Depends on item 18.

- **20. `NUCLEAR_AVALANCHE_PARAMS` fully parametrised.**
  Promote `NUCLEAR_REACTANTS` to a complete framework: `Z_B`,
  `Q_pB_MeV`, `E_alpha_birth_MeV` derive from the reactant pair;
  cross sections and rate coefficients abstract over species.
  Re-derive every concrete settlement (p-11B, D-3He, D-D) within
  the parametrised framework, with reactant-specific numerical
  bounds.

## Dynamics and dimension

- **21. Tertiary and higher-order chain rates.**
  Define `R_tertiary` (rate from secondary-product alphas knocking
  on borons), `R_quaternary`, etc. Show that the geometric chain
  `R_total := R_primary + R_secondary + R_tertiary + ... =
  R_primary * sum_{n=0}^infty M^n = R_primary / (1 - M)` recovers
  the chain sum, formalizing the chain-sum as a genuine
  multi-generation cumulative rate.

- **22. Time-evolution layer for the kinetic equations.**
  Define `PlasmaTrajectory := R -> PlasmaStateAsh`. Define
  `dn_ash/dt = R_primary - n_ash / tau_ash` (ash production and
  removal). Prove `n_ash(t) = n_ash_eq * (1 - exp(-t/tau_ash))`
  solves the ODE. Compose with `M_ash_decreasing` to derive
  `M(t)`'s monotonic decrease toward `M_infty < M(0)`, formalising
  the dynamical content of self-quenching.

- **23. Full 3D volumetric averaging via Fubini.**
  Lift `M_volumetric` from radial 1D to full 3D iterated integral.
  Define `is_RInt_3D f V l` via three nested `is_RInt`s. Prove
  Fubini: `RInt_3D f (V_1 x V_2 x V_3) = RInt (fun x => RInt (fun
  y => RInt (fun z => f x y z) z_1 z_2) y_1 y_2) x_1 x_2`. State
  and prove `M_volumetric_3D_pointwise_bound`, specialising back
  to the radial case via spherical-coordinate substitution.

- **24. Distributional Fokker-Planck via test-function pairing.**
  Define `D_test(a, b)` as `C^infty_c(a, b)`. Define
  `weak_FP f phi := integral f * (Edot * phi)' + integral f * (D *
  phi'')`. Prove `forall phi in D_test, weak_FP f_slowing phi =
  S * phi(E_birth)` via `RInt_by_parts` (derive from
  `is_RInt_derive` + product rule). Strengthens the strong-form
  `slowing_flux_steady_derivative` to a distribution-theoretic
  identity that survives non-smooth source terms.

- **25. Boltzmann transport equation with full collision integral.**
  Replace the slowing-down model `dE/dt = -E / tau_s(E)` with the
  full transport equation `df/dt + v * grad f = C[f]` where `C[f]`
  is the Boltzmann collision integral over all binary-collision
  species pairs. Prove that the steady-state moment equations
  recover `f_slowing(E) propto tau_s(E) / E` in the slow-down
  limit.

## Extended physical scope

- **26. Relativistic bremsstrahlung (Bethe-Heitler).**
  Replace the non-relativistic `bremsstrahlung := C_brems * Z_eff^2 *
  n_e^2 * sqrt T` with the relativistic Bethe-Heitler form
  `bremsstrahlung_rel := C_brems_rel * Z_eff^2 * n_e^2 * T *
  (1 + 5 * T / (m_e * c^2) + ...)`. Prove the non-relativistic
  formula is the low-T limit, matching at `T << m_e * c^2`.

- **27. Synchrotron toroidal geometry.**
  Replace the uniform-B `synchrotron := C_sync * n_e * T^2 * B^2`
  with the toroidal-flux-surface integral `synchrotron_torus(R, a)
  := integral_torus C_sync_local(r) n_e(r) T(r)^2 B(r)^2 dV`
  over the reactor volume specified by major radius R and minor
  radius a. Couple with item 23 (3D Fubini) for the volumetric
  integrated loss in terms of radial profiles.

- **28. Hora-paper-specific avalanche-enhancement-factor refutation.**
  Encode Hora's 2017 specific numerical claim (alpha-induced
  secondary chain multiplier ~10^3) as a stated condition:
  `exists s, reactor_regime s /\ multiplication_factor s >= 1000`.
  Refute it by combining `reactor_no_multiplication` with the
  bound, yielding `~ Hora_avalanche_claim`. The settlement gains
  a theorem-cited refutation in addition to the qualitative
  conclusion.

## Foundational capstones

- **29. Constructive integration eliminating `Classical_Prop.classic`.**
  Replace Coquelicot's classical FTC layer with a hand-rolled
  `is_RInt_intuit f a b l`: for every constructive epsilon, there
  is a constructive delta such that every Riemann sum with mesh
  below delta approximates l within epsilon. Re-derive
  `is_RInt_derive` (FTC) and `RInt_le` (monotonicity) over this
  predicate; re-plumb every existing theorem that uses Coquelicot
  integration. The footprint collapses to the three Stdlib Dedekind
  axioms alone across the whole development.

- **30. Meta-theorem on irreducibility of the axiom footprint.**
  State and prove that `Classical_Prop.classic`, `sig_forall_dec`,
  `sig_not_dec`, and `functional_extensionality_dep` cannot be
  dropped from `hora_putvinski_settlement` without falsifying it.
  Construct a model in which one of these axioms fails and the
  settlement is false. The necessity of the four-axiom footprint
  becomes itself a Coq-checked theorem.

## Build

```
eval $(opam env --switch=rocq9)
make
```

All 25 files in `theories/` currently compile clean (the third-
generation deepening program above is the work that follows).
