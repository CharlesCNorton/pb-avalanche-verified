# TODO

The 15-item deepening program is complete (settlement compiles with
no `Admitted` or project-local axioms; the closing theorem
`pb_avalanche_settlement` in `theories/pb_avalanche_final.v` carries
only the three Stdlib Dedekind axioms plus `Classical_Prop.classic`).

The list below is the next-generation deepening program: 30 remaining
gaps and weaknesses, each posed as the construction that closes it,
ordered in the logical sequence of completion. Earlier items are
prerequisites or hygiene; later items are architectural redesigns,
physics-from-first-principles derivations, and scope generalizations.

## Hygiene and local refinements

- **1. Replace `auto_derive` with explicit derivative chains.**
  Unfold `is_derive_neg_T_exp` (thermal file) and `id_squared_derive`
  / `F_quadratic_derive` (integral file) into explicit chains of
  `is_derive_mult`, `is_derive_comp`, `is_derive_const`,
  `is_derive_exp`, `is_derive_inv`, `is_derive_id`. Tactical
  blackbox becomes auditable line-by-line.

- **2. Pervasive `Print Assumptions` audit.** Add a dedicated
  `pb_avalanche_audit.v` that runs `Print Assumptions` against every
  Theorem exported by every framework module. Any regression in the
  axiom footprint then surfaces at `make` time rather than requiring
  manual inspection.

- **3. Eta-expand the kinetic factorization with an explicit `n_alpha`
  identity.** Introduce
  `n_alpha_from_source_and_residence :
     n_alpha_kinetic (3 * R_prim) tau = 3 * R_prim * tau * L_kin`,
  with `L_kin = ln(E_birth / E_min)` named as the kinematic factor,
  so the bridge between `R_secondary = 3 R_prim tau n_B (L * sigma_v)`
  and `R_secondary = n_alpha n_B sigma_v` is a named lemma rather than
  an implicit identification.

- **4. Constant-case closed-form for `sigma_v_kinetic`.** Prove
  `forall S tau,
     K.sigma_E = const sigma_E_max ->
     K.v_E    = const v_E_max ->
     PK.sigma_v_kinetic S tau = sigma_E_max * v_E_max`,
  removing the inequality-only treatment in the constant
  instantiation.

- **5. Avalanche threshold as a sharp dichotomy: `M ≠ 1` on the
  regime.** Strengthen `reactor_no_multiplication` to
  `forall s, reactor_regime s -> multiplication_factor s <> 1` (and
  the contrapositive: the marginal case `M = 1` is *excluded* by the
  regime, not merely bounded above by it).

- **6. Continuity of `interp_linear` as a single global statement.**
  Refactor the per-segment continuity in `pb_avalanche_iaea.v` into
  one theorem `interp_linear_continuous_on :
   sorted_table T -> forall E, head_E T <= E <= last_E T ->
     continuous (interp_linear T) E`, so it can be reused as input
  to other `ex_RInt_continuous` closures.

- **7. Zero-extension of `interp_linear` outside the table interval.**
  Redefine `interp_linear T E` to be `0` for `E < head_E T` and
  `E > last_E T` (rather than the current constant-extrapolation
  behavior, which is physically wrong above the resonance). Prove
  the integral identity is unchanged on the table interval, and
  that the extended interpolant remains continuous at the endpoints
  (require boundary values `v_0 = v_last = 0`).

- **8. Thread the magnetic field through to the witness state's
  `B_T`.** The current `reactor_witness_plasma.B_T = 1` is unused in
  the bound. Make `tau_slow_alpha` in the witness genuinely depend on
  `B_T s` via `tau_eff_B (tau_slow_alpha s) kappa (B_T s)` from the
  kinetic file's residence-time machinery, and re-prove
  `witness_no_avalanche` with `B = 5 Tesla` (ITER class).

## Stronger derived bounds

- **9. Curvature-bounded interpolation error.** Strengthen
  `interp_error_bound` from a uniform `eps` hypothesis to the derived
  bound `||sigma - interp_linear T||_infty <= M_2 * h^2 / 8` where
  `M_2 := sup_E |sigma''(E)|` and `h := max_i (E_{i+1} - E_i)`. Needs
  `Derive_2 sigma` continuity plus combinatorics over the table's
  intervals.

- **10. Adaptive Romberg integration.** Implement
  `romberg : (R -> R) -> R -> R -> nat -> R` via the
  Richardson-extrapolation tableau, prove convergence
  `lim_{k -> infty} romberg f a b k = RInt f a b` for `f` of class
  `C^{2k}` at rate `O(h^{2k})`, and use it against the IAEA cross
  section to produce a tighter numerical bound than the trapezoidal
  rule.

- **11. Improper-integral reactivity over `[0, infty)`.** Extend
  `pb_avalanche_thermal.v` from finite `[E_lo, E_hi]` to the half-line
  via Coquelicot's `is_RInt_gen` framework. Prove
  `RInt_gen (fun E => exp (-E/T)) 0 +infty = T`, prove
  dominated-convergence integrability of `sigma(E) * v(E) * exp(-E/T)`
  for an IAEA-bounded `sigma`, and lift `reactivity_bound` to the full
  half-line.

- **12. Energy-dependent Coulomb slowing-down time.** Replace the
  constant `Edot E := -E / tau` in `pb_avalanche_kinetic.v` with
  `Edot E := -E / tau_s(E)` carrying the proper Coulomb-velocity
  dependence `tau_s(E) ∝ E / v(E)^3 ∝ E^{-1/2}`. Re-derive the
  steady-state slowing-down spectrum (picks up an `E^{1/2}` factor:
  `f(E) ∝ S * E^{-3/2}`), and re-prove the kinetic FoM sandwich.

- **13. Asymptotic completeness of `reactor_FoM_upper_bound`.** State
  and prove the converse: for any `eps > 0` there exists a plasma
  state in the reactor regime with
  `M >= FoM_max_reactor - eps`. Constructive witness: `n_B =
  n_B_max_reactor`, `T = T_max_reactor`, `n_p = n_p_min_reactor`,
  alpha-spectrum saturating its upper bound. This certifies tightness
  rather than just one-sided estimate.

- **14. Sikora-Weller p-11B cross-section instantiation.** Encode the
  full Sikora-Weller (2016) `p-11B(α₀ + α₁ + α₂)` tabulation as a
  ~50-point `iaea_table`. Prove monotonicity of the resonance
  structure, derive `M_2 := sup |sigma''|` from the Breit-Wigner
  shape, and use it via the curvature-bounded `interp_error_bound`
  (item 9) to get an explicit numerical interpolation error.

## Architectural foundations

- **15. Rational-exponent `Unit` type.** Generalize `Unit` from
  `Z`-exponents to `Q`-exponents so `sqrt(T)` in Spitzer carries the
  legitimate exponent `u_temp = 1/2`. Prove the unit algebra is a
  `Q`-vector space, redo the algebraic-group lemmas
  (`unit_mul_zero_l/r`, `unit_mul_assoc`, `unit_mul_inv_r`,
  `unit_pow_add`), and propagate through `tau_spitzer` so its dr-type
  carries the proper rational-exponent signature.

- **16. DR-typed re-derivation of the framework.** Rebuild
  `PB_AVALANCHE_PARAMS` and `PBAvalancheFramework` so that `n_p`,
  `n_B`, `tau_slow_alpha`, `sigma_alpha_p_knockon`, `v_alpha_max`,
  `R_secondary` are `DR u`-typed for the unit `u` from item 15.
  `multiplication_factor` then inhabits `DR zero_unit` *by type-check
  alone* — the dimensional-balance theorem becomes definitional. All
  six concrete instantiations port to typed values.

## Physics from first principles

- **17. Spitzer prefactor from physical constants.** Build `m_e`,
  `m_alpha`, `Z_e`, `e_charge`, `eps_0`, `k_B`, `hbar` as DR-typed
  constants in their proper units. Derive
  `Cspitzer = (3 * sqrt(2π) * m_e * sqrt(m_e)) /
              (4 * Z_e² * e_charge⁴ * eps_0² * pi * lnLambda) *
              k_B^{3/2}`
  with the dr-type checked against the slowing-down-time signature, so
  `tau_spitzer` has the right units by construction rather than the
  current `spitzer_C := 1` convention.

- **18. Derived Coulomb-log envelope.** Define
  `lambda_Debye T n_e := sqrt(eps_0 * k_B * T / (n_e * e_charge²))`,
  `b_min_classical T := Z_e² * e_charge² / (4πε₀ * k_B * T)`,
  `b_min_quantum T m := hbar / sqrt(m * k_B * T)`, and
  `b_min := max b_min_classical b_min_quantum`. Prove that on the
  reactor regime
  `T ∈ [10, 300] keV`, `n_e ∈ [10¹³, 10¹⁵] cm⁻³`, the derived
  `ln(lambda_Debye / b_min)` falls in `[ln_Lambda_min, ln_Lambda_max]
  = [10, 25]` — *deriving* the envelope rather than asserting it.

- **19. Gamow penetration cross section.** Derive the primary
  cross section's energy dependence
  `sigma(E) = S(E) / E * exp(-2π * Z_p * Z_B * e² /
                              (4πε₀ * hbar * v_rel(E)))`
  from the WKB Coulomb-tunneling approximation. Prove the
  low-energy form `sigma(E) ~ exp(-C / sqrt E)`, differentiate the
  Maxwellian-weighted integrand to locate the Gamow peak, and verify
  it agrees with the experimental `T_peak ≈ 200 keV` for p-11B.

- **20. Distributional Fokker-Planck steady state.** Define the
  Fokker-Planck operator
  `FP[f] E := d/dE (Edot(E) * f(E)) - d²/dE² (D(E) * f(E))`
  with energy-dependent diffusion coefficient `D`, and the source
  `S * delta_{E_birth}` via Coquelicot's pairing of locally
  integrable functions with smooth test functions. Prove `f_slowing`
  solves the steady-state weak equation `∀φ ∈ C_c^∞,
  ∫ f * FP*[φ] = S * φ(E_birth)` — strengthening the current
  divergence-free `slowing_flux_steady_derivative`.

## Cross-file integration

- **21. Wire the IAEA cross section into the kinetic framework.**
  Instantiate `KINETIC_MODEL_PARAMS` with
  `sigma_E := interp_linear sikora_weller_table` (item 14) and
  `v_E E := sqrt(2 * E / m_alpha)` (item 19 / classical kinematics).
  Prove the continuity hypotheses via item 6 and `continuous_sqrt`,
  and derive the kinetic figure-of-merit sandwich for these
  realistic inputs.

- **22. Maxwellian-thermal connection to kinetic.** Prove that the
  abstract `R_prim` in `PK.kinetic_no_avalanche` equals
  `n_p * n_B * reactivity (sigma * v) T_keV` where `reactivity` is the
  half-line average from item 11. Instantiate the kinetic framework
  with this thermal primary rate to produce
  `thermal_kinetic_no_avalanche : T_keV ∈ [10, 300] keV -> M < 1`.

- **23. Helium-ash transport with `Z_eff` raising.** Add `n_ash` to
  `PlasmaState`. Redo `tau_slow_alpha` with denominator
  `n_p + Z_B² * n_B + Z_alpha² * n_ash`. Prove that `M` *decreases*
  with ash buildup — a formal self-quenching mechanism. Re-instantiate
  the witness states with explicit `n_ash` profiles.

## New dimensional axes

- **24. Time-integrated geometric chain.** Define the all-generations
  multiplication `M_total := lim_{N -> infty} Σ_{n=0}^{N} M^n`. Prove
  convergence for `M < 1` to `1 / (1 - M)` via Coquelicot's
  `Series_geom`, prove divergence for `M >= 1`, and restate the
  settlement as: *the total long-time integrated secondary-fusion
  contribution is bounded by* `R_primary / (1 - FoM_max_reactor)`
  — an absolute, time-integrated bound rather than the current
  instantaneous ratio.

- **25. Spatial reactor profile via volumetric integration.** Promote
  `PlasmaState` to `PlasmaProfile := R^3 -> PlasmaState` over a
  reactor volume `V ⊂ R^3`. Define
  `M_volumetric := ∫_V R_secondary(r) dV / ∫_V R_primary(r) dV`
  via iterated `RInt` (Fubini). Prove that pointwise `M(r) < 1`
  implies `M_volumetric < 1`, and produce volume-averaged versions of
  every witness theorem.

- **26. Energy-balance admissibility.** Define
  `bremsstrahlung T n_p n_B := C_brems * (n_p + Z_B² * n_B)² * sqrt T`
  and
  `synchrotron T n_e B := C_sync * n_e * T² * B²`. Add
  `energy_balance_admissible (s : PlasmaState) :=
     R_primary s * Q_pB >= bremsstrahlung s + synchrotron s`.
  Prove that the intersection of `reactor_regime` with energy balance
  gives a *sharper* numerical bound on `FoM_max_reactor` — quantitatively,
  that the temperature must lie below 250 keV for breakeven, tightening
  the avalanche bound.

## Scope generalization and validation

- **27. Laser-driven (Hora 2017) regime explicitly out-of-scope.**
  Define `laser_driven_regime` with `n_B ∈ [10²¹, 10²³] cm⁻³` and
  `tau ∈ [10⁻¹², 10⁻⁶] s`. Prove that `reactor_subcritical_axiom`
  of `PhysicalParams` *does not hold* at those parameters by
  exhibiting a witness state that violates the inequality. Identify
  the precise composite-product threshold at which the conclusion
  becomes inconclusive, documenting it as "the Hora claim is a genuine
  open question above this threshold."

- **28. `NUCLEAR_AVALANCHE_PARAMS` generalization.** Refactor
  `PB_AVALANCHE_PARAMS` so the reactant pair `(Z₁, A₁, Z₂, A₂)` and
  Q-value `Q_MeV` are abstract parameters. Instantiate for p-11B
  (current), D-³He (`Z₁=1, A₁=2, Z₂=2, A₂=3, Q=18.35`), and D-D
  (`Q ≈ 3.27`). Prove the same subcriticality conclusion for each,
  identifying the reactant-specific critical density-temperature
  product.

- **29. Eddington stellar instantiation.** Instantiate the
  generalized framework (item 28) against solar-core p-p parameters
  (`T = 1.5 keV`, `n_p = 10²⁵ cm⁻³`, cross section orders of magnitude
  below p-11B). Prove `M ≪ 1` for the Sun. Encode as
  `theorem solar_no_avalanche` — a formal version of Eddington's
  intuition that thermonuclear chains in stars are self-regulating.

## Capstone

- **30. Constructive elimination of `Classical_Prop.classic`.**
  Replace Coquelicot's classical FTC machinery (`is_RInt_derive`,
  `RInt_Derive`) with a constructive integration layer — either
  MathComp's reals analysis or a hand-rolled `is_RInt_intuit` built
  from uniform-continuity plus classical-free Riemann sums via
  `pos_div_2`. The axiom footprint then collapses to the three Stdlib
  Dedekind axioms alone, validating the entire development under
  intuitionistic logic.

## Build

```
eval $(opam env --switch=rocq9)
make
```

All nine files in `theories/` currently compile clean:

- `pb_avalanche.v`
- `pb_avalanche_integral.v`
- `pb_avalanche_kinetic.v`
- `pb_avalanche_envelope.v`
- `pb_avalanche_thermal.v`
- `pb_avalanche_spitzer.v`
- `pb_avalanche_iaea.v`
- `pb_avalanche_units.v`
- `pb_avalanche_final.v`
