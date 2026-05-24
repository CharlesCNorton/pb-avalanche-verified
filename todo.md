# TODO

The development compiles clean on the `rocq9` switch with Coquelicot
3.4.4; the axiom footprint (`sig_forall_dec`, `sig_not_dec`, `classic`,
`functional_extensionality_dep`) is guarded by `scripts/check_axioms.sh`,
and the settlement core with its deepenings and rigor cures is mechanised
with complete `Qed` proofs.

Landed since the last revision: the Picard iterates converge in the sup
metric to `n_ash_solution` (`picard_geom_bound`, `picard_converges`); the
figure of merit `M = 3 n_B tau <sigma v>` is derived from the
slowing-down collision integral on the Fokker-Planck steady spectrum
(`figure_of_merit_canonical`, `figure_of_merit_on_steady_spectrum`); the
Gamow-peak exponent attains the Kramers value `3 (b_G^2 / 4T)^{1/3}`
(`gamow_peak_exponent_value`), the peak is a genuine critical point of the
integrand exponent — `d/dE (b_G/sqrt E + E/T) = 0` there
(`gamow_exponent_critical`) — and the exponent is strictly convex on `E > 0`
with closed-form first and second derivatives and positive curvature
(`gamow_exponent_first_deriv`, `gamow_exponent_second_deriv`,
`gamow_exponent_curvature_pos`), so the peak is the unique minimum of the
exponent (the unique maximum of the integrand); and the evaluated Sikora-Weller p-11B
cross section carries its measurement band through the resonance-window
integral and peak (`sikora_weller_integral_error_band`,
`sikora_weller_peak_error_band`). The constructions below carry it
further. Each names the move that closes it.

- Carry the Gamow saddle to the full Laplace asymptotic. The exponent value
  `3 (b_G^2 / 4T)^{1/3}`, the stationary point, the positive curvature, the
  closed-form curvature `phi''(E_peak) = 3 b_G/4 (b_G T/2)^{-5/3}`, and the
  `T^{5/6}` peak width with the resulting `T^{-3/2} * width ~ T^{-2/3}`
  prefactor scaling (`gamow_prefactor_scaling`) are all proved; the one
  remaining step is the Laplace integral approximation `integral exp(-phi) ~
  exp(-phi(E_peak)) sqrt(2 pi / phi''(E_peak))` with a remainder bound, which
  upgrades the scaling law to the full asymptotic constant.
- Reprove the monotonicity of `exp` and a derivative-positivity
  (mean-value) principle directly from the power series, so the midpoint
  Riemann sum's convergence to `exp b - exp a` drops `classic`; the
  closed form `sum_midpoints exp = exp(a+h/2) (exp(nh)-1)/(exp h - 1)` is
  already classic-free, and only the `(h/2)/sinh(h/2) -> 1` ratio bound
  needs the constructive monotonicity. Then the thermal `integral
  exp(-E/T)` and the improper `integral_0^infty` follow classic-free.
- Route every remaining Coquelicot `RInt` use through the classic-free
  `is_RInt_intuit`, building on the `exp` step above, to collapse the
  footprint to the three Dedekind axioms and drop `classic` from the
  manifest.
- Construct the periodic-Bernoulli Peano kernel to carry the order-2
  Euler-Maclaurin identity to all orders, giving Romberg `O(h^{2k+2})` at
  every level `k`.
- Build the irregular Coulomb function `G_0` and the phase shift
  `sigma_0 = arg Gamma(1 + i eta)`, and derive the penetrability
  `P_0 ~ exp(-2 pi eta)` from `1 / (F_0^2 + G_0^2)`.
- Extend Fubini to every continuous integrand via uniform continuity and
  separable-span approximation, lifting the additive-closure restriction.
- Lift the BGK quadratic H-theorem to the full `f ln(f / f_eq)`
  functional. The pointwise core is proved: the Gibbs/Klein inequality
  `f ln(f/f_eq) >= f - f_eq`, the relative-entropy density nonnegativity
  `f ln(f/f_eq) - f + f_eq >= 0`, its vanishing exactly at `f = f_eq`, and
  strict positivity off equilibrium (`gibbs_relative_entropy`,
  `relative_entropy_density_nonneg`, `relative_entropy_density_pos`), so the
  Maxwellian is the unique zero of the H-functional. The remaining step
  integrates this density against the binary `(v,u) <-> (v',u')` collision
  operator to get `dH/dt <= 0`.
- Assemble the Bethe-Maximon total cross section and the full
  Maxwellian-averaged radiated power, joining the spectral integral and
  moment scaling already proved.
- Exhibit, for each axiom in the footprint, a model of the other three in
  which it fails. The constructive axioms admit such models, but a model
  refuting `classic` lives in a topos rather than in Coq's own logic, so
  this step needs an external semantics layer to become a Coq-checked
  independence theorem.

## Build

```
eval $(opam env --switch=rocq9)
make
make audit-check
```
