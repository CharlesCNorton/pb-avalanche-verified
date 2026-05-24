# TODO

Every deepening item now carries a mechanised core with complete `Qed`
proofs. The 43 files in `theories/` compile clean on the `rocq9` switch
with Coquelicot 3.4.4, and the four-axiom footprint
(`sig_forall_dec`, `sig_not_dec`, `classic`,
`functional_extensionality_dep`) is guarded by `scripts/check_axioms.sh`.

The nine residuals named earlier are landed:

1. **Euler-Maclaurin via Bernoulli numbers.** The Bernoulli sequence is
   constructed directly from its defining recurrence
   `sum_{j=0}^{n} C(n+1,j) B_j = 0`, `B_0 = 1` (`bernoulli`, axiom-free);
   the constructed values reproduce `B_0 .. B_8` and satisfy the
   recurrence for `n = 1 .. 5`; and `trap_rule_sq_bernoulli_term`
   identifies the order-2 trapezoidal error with the `B_2/2! h^2
   (f'(b)-f'(a))` term of the expansion.
2. **Coulomb solutions.** `wronskian_constant_2nd_order` and
   `coulomb_wronskian_constant` prove the Wronskian `F G' - F' G` of any
   two solutions of `w'' + (1 - 2 eta / rho) w = 0` is constant in `rho`
   (Abel's identity), the structural relation behind the penetrability
   `1 / (F^2 + G^2)`.
3. **Picard / Banach.** `picard_cont` (every iterate is continuous) and
   `picard_error_one_step` (`e_{n+1}(t) = -1/tau integral_0^t e_n`) with
   `picard_error_contraction` (`|e_{n+1}| <= 1/tau integral |e_n|`) give
   the one-step contraction at the heart of the fixed-point argument.
4. **Fubini.** `fubini_zero` adds the zero element to the
   additive-closure results, so the Fubini-compatible class is closed
   under the full additive structure (zero plus `fubini_sum`).
5. **Delta-source Fokker-Planck.** `slowing_down_delta_source` proves the
   weak drift pairing of the slowing-down spectrum localises onto the
   birth energy (`= -S phi(E_birth)`), with `slowing_down_steady_state`
   the source-balanced corollary.
6. **BGK H-theorem.** `bgk_H_closed_form`, `bgk_H_decreasing` (monotone
   decay) and `bgk_entropy_production` (`dH/dt = -(2/tau) H <= 0`) give
   the quadratic H-theorem for the relaxation.
7. **Bremsstrahlung.** `sigma_spectral_log` integrates the `1/omega`
   spectrum to the Coulomb logarithm and `brems_thermal_power_sqrtT`
   derives the `sqrt(T)` law from the Maxwellian moment scaling.
8. **Constructive integration.** `is_RInt_intuit` carries base cases,
   linearity, monotonicity, uniqueness and the extensionality/`opp`/
   `minus` closure, all `classic`-free.
9. **Reverse mathematics.** `classic <-> DNE <-> Peirce`,
   `sig_forall_dec -> LPO`, the constructive epsilon search, and the
   de Morgan / material-implication / contrapositive / linearity
   characterisations.

## Further constructions

Each landed core extends along a definite line:

- carry the order-2 Euler-Maclaurin identity to the all-orders periodic
  Bernoulli Peano kernel and the Romberg `O(h^{2k+2})` bound at every
  level `k`;
- build the irregular `G_0` and the phase shift
  `sigma_0 = arg Gamma(1 + i eta)` and derive `P_0 ~ exp(-2 pi eta)`
  from `1/(F_0^2 + G_0^2)` using the Wronskian normalisation;
- take the Picard contraction to the uniform `Lim_seq` in the sup metric
  and prove it equals `n_ash_solution`;
- extend Fubini to every continuous integrand via uniform continuity and
  the separable-span approximation;
- iterate the BGK entropy identity into the `f ln(f/f_eq)` functional
  from the binary `(v,u) <-> (v',u')` scattering symmetry;
- assemble the Bethe-Maximon total cross section and the full
  Maxwellian-averaged radiated power;
- route the remaining Coquelicot-integral uses through `is_RInt_intuit`
  so the footprint collapses to the three Dedekind axioms;
- build, per axiom, a model of the other three in which it fails, turning
  the footprint into a Coq-checked independence theorem.

## Build

```
eval $(opam env --switch=rocq9)
make
make audit-check
```
