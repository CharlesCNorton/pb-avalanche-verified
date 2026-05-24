# TODO

All eleven items have genuine complete-`Qed` content. 43 files in
`theories/` compile clean on the `rocq9` switch with Coquelicot 3.4.4;
the four-axiom footprint is guarded by `scripts/check_axioms.sh`.

| # | Item | Status | File |
|---|------|--------|------|
| 1 | Sharp /8 bound wired into IAEA | done | `interp_segment_curvature_error_sharp` (curvature_tight) |
| 2 | CI workflow | done | `.github/workflows/ci.yml` |
| 3 | Trapezoidal panel error | general C^2, tight /12 constant via divided-difference MVT | `trapezoidal_panel_error` (curvature_tight) |
| 4 | Coulomb series | convergence for all rho via coefficient bound + exp comparison | `cw_bound`, `cw_series_ex` (coulomb_waves) |
| 5 | Picard | closed-form solution is the Picard fixed point; iterates collapse at n=1,2 | `n_ash_solution_fixed_point` (picard) |
| 6 | Fubini | additivity + closure under sums (additive span of products) | `iter_rint_xyz_plus`, `fubini_sum` (fubini_3d) |
| 7 | Distributional FP | weak drift pairing = strong operator against the test function | `weak_FP_drift_is_strong` (distributional_fp) |
| 8 | Collision integral | mass/momentum/energy conservation from gain-loss balance | `collision_conserves_{mass,momentum,energy}` (boltzmann) |
| 9 | Bremsstrahlung | sqrt(T) law from Maxwellian moment scaling; spectral integral | `thermal_mean_speed_sqrtT`, `brems_spectral_power` (bethe_heitler) |
| 10 | Constructive integration | uniqueness of the classic-free constructive integral | `is_RInt_intuit_unique` (constructive_integration) |
| 11 | Axiom characterisation | sig_forall_dec <-> LPO (informative Set-level form distinguished) | `sig_forall_dec_implies_LPO` (axiom_irreducibility) |

## Remaining full-generality extensions

Each item above proves the substantive core; these are the further
constructions that take them to full generality:

- **3.** Bernoulli-Peano higher-order terms for the full `O(h^{2k+2})`
  at arbitrary `k` (the order-2 case for arbitrary `C^2` is done).
- **4.** Asymptotic matching `F_0(eta, rho) ~ sin(rho - eta ln(2 rho) +
  sigma_0)` and the irregular solution `G_0` (convergence is done).
- **5.** Banach fixed-point convergence of the iterates at all `n` in
  the uniform metric (the fixed-point property and low-order iterates
  are done).
- **6.** Arbitrary continuous integrands via Stone-Weierstrass density
  (the additive span of separable products is done).
- **7.** The exact delta-measure source `S * phi(E_birth)` for the
  singular slowing-down distribution (the weak=strong duality is done).
- **8.** The explicit 9-D binary-collision kernel with its scattering
  symmetry (the conservation laws from gain-loss balance are done).
- **9.** The Bethe-Maximon log-integral over photon energy (the
  Maxwellian sqrt(T) scaling and the 1/omega spectral integral are done).
- **10.** Re-routing the whole development's Coquelicot integrals
  through `is_RInt_intuit` (the predicate, its base cases, linearity,
  monotonicity, and uniqueness are done classic-free).
- **11.** Models in which each axiom fails individually — a
  metatheoretic statement about Rocq's models, outside the object logic
  (the reverse-mathematics characterisations are done inside it).

## Build

```
eval $(opam env --switch=rocq9)
make
make audit-check
```
