# TODO

The development compiles clean on the `rocq9` switch with Coquelicot
3.4.4; the axiom footprint (`sig_forall_dec`, `sig_not_dec`, `classic`,
`functional_extensionality_dep`) is guarded by `scripts/check_axioms.sh`,
and the settlement core with its deepenings and rigor cures is mechanised
with complete `Qed` proofs. The constructions below carry it further.
Each names the move that closes it.

- Ingest the evaluated p-11B cross-section data with its measured error
  bars into the interval kernel of `pb_avalanche_spitzer_numerical.v`, so
  the subcriticality endpoints are read from the data rather than from
  chosen rationals.
- Derive the Gamow reactivity magnitude by Laplace's method on the
  Maxwellian-Gamow integral, recovering the Kramers form
  `<sigma v> ~ T^{-2/3} exp(-3 (b_G^2 / 4 T)^{1/3})` to join the
  positivity and `T^{2/3}` peak already proved.
- Extend `is_RInt_intuit` to `exp` via its geometric-sum closed form and
  limit, then prove the thermal `integral exp(-E/T)` and the improper
  `integral_0^infty` classic-free.
- Route every remaining Coquelicot `RInt` use through `is_RInt_intuit`,
  collapsing the footprint to the three Dedekind axioms and dropping
  `classic` from the manifest.
- Construct the periodic-Bernoulli Peano kernel to carry the order-2
  Euler-Maclaurin identity to all orders, giving Romberg `O(h^{2k+2})` at
  every level `k`.
- Build the irregular Coulomb function `G_0` and the phase shift
  `sigma_0 = arg Gamma(1 + i eta)`, and derive the penetrability
  `P_0 ~ exp(-2 pi eta)` from `1 / (F_0^2 + G_0^2)`.
- Take the Picard contraction to the uniform `Lim_seq` in the sup metric
  and prove the limit equals `n_ash_solution`.
- Extend Fubini to every continuous integrand via uniform continuity and
  separable-span approximation, lifting the additive-closure restriction.
- Lift the BGK quadratic H-theorem to the full `f ln(f / f_eq)`
  functional, derived from the binary `(v,u) <-> (v',u')` scattering
  symmetry.
- Assemble the Bethe-Maximon total cross section and the full
  Maxwellian-averaged radiated power, joining the spectral integral and
  moment scaling already proved.
- Build, for each axiom in the footprint, a model of the other three in
  which it fails, turning the footprint into a Coq-checked independence
  theorem.
- Derive the figure of merit `M = 3 n_B tau <sigma v>` from the kinetic
  collision operator rather than positing it, grounding the reduced model
  in the Boltzmann / Fokker-Planck layer already formalised.

## Build

```
eval $(opam env --switch=rocq9)
make
make audit-check
```
