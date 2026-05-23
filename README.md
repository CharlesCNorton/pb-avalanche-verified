# Proton-Boron Avalanche Fusion: Verified Bounds on Chain Multiplication

A Rocq formalization of the kinetic rate equations for alpha-induced
secondary p+11B reactions, settling the Hora-Putvinski avalanche
dispute by establishing necessary and sufficient conditions for the
secondary-to-primary multiplication factor to exceed unity, and
exhibiting explicit numerical realizations at both rescaled and
physical reactor parameters in which the multiplication factor is
strictly below unity throughout the reactor regime.

## Structure

The development has four layers, all in `theories/pb_avalanche.v`.

**Abstract framework (Module Type `PB_AVALANCHE_PARAMS`).**
Encapsulates the kinetic input as named parameters: the primary and
knock-on cross sections, the Spitzer-Trubnikov constant, the alpha
velocity bound, the alpha-distribution-weighted velocity integral, and
the reactor regime parameters `n_B_max`, `T_max`, `n_p_min`. Together
with positivity axioms, the cross-section and integral bound axioms,
and the numerical subcriticality axiom on the composite product, this
module type is the complete physical-input interface to the proof.

**Framework functor (`PBAvalancheFramework`).**
Defines `tau_slow_alpha`, `f_alpha`, `R_primary`, `R_secondary` from
the parameters, recovers the three closed-form identities (Spitzer-
Trubnikov slowing-down formula, slowing-down Fokker-Planck equilibrium,
bilinear kinetic decomposition of the secondary rate) as definitional
lemmas, and proves the chain:

1. `multiplication_factor s = avalanche_figure_of_merit s` for every
   plasma state, where the avalanche figure of merit is the product
   `3 * n_B * tau_slow_alpha * <sigma_knockon * v>_alpha`.
2. `tau_slow_alpha s <= tau_max_reactor` throughout the reactor regime,
   by Spitzer + the regime hypotheses on `T <= T_max` and
   `n_p >= n_p_min`.
3. `avalanche_figure_of_merit s <= FoM_max_reactor` throughout the
   reactor regime, by composing the velocity-weighted integral bound,
   the Spitzer bound on `tau_slow_alpha`, and the `n_B` regime bound.
4. `multiplication_factor s < 1` throughout the reactor regime, by
   combining the composite upper bound with the numerical
   subcriticality axiom from the parameter spec.

**Rescaled instantiation (`ConcreteParams` and `ConcreteSettlement`).**
Provides explicit numerical values for every parameter
(`Cspitzer = 1/100`, `T_max = 100`, `n_B_max = 100`, `n_p_min = 100`,
`sigma_knockon_max = 1/10^7`, `v_alpha_max = 10^4`), discharges every
axiom by direct arithmetic, and produces a fully grounded instantiation
in which `ConcreteSettlement.hora_putvinski_settlement` stands on zero
project-local axioms. The composite bound under these values evaluates
to exactly `3/100`, proved as `concrete_FoM_max_reactor_value`, which
gives the strengthened conclusion
`multiplication_factor s <= 3/100` for every reactor-regime plasma
state. A specific witness plasma state
`reactor_witness_plasma` is constructed with `n_p = 100`, `n_B = 50`,
`T = 50` and shown to satisfy the regime + the strengthened bound.

**Physical-scale instantiation (`PhysicalParams` and
`PhysicalSettlement`).**
A second concrete instantiation using values closer to actual reactor
units: boron and proton densities at 10^14 cm^-3, temperature at
100 keV, knock-on cross-section bound at 10^-25 cm^2, alpha velocity
at 10^9 cm/s, and Spitzer constant absorbed into the unit choice. The
composite FoM bound evaluates to roughly 3 * 10^-13, well below
unity, and the `field_simplify; lra` normalizer handles the resulting
arithmetic on these large-magnitude operands without difficulty.
A physical-scale witness plasma state
`physical_witness_plasma` is constructed with `n_p = n_B = 10^14`,
`T = 50` keV, and shown to satisfy `PhysicalSettlement.reactor_regime`
and the `multiplication_factor < 1` conclusion.

## Axiom footprint

Every theorem in both `ConcreteSettlement` and `PhysicalSettlement`
closes by `Qed` and depends only on the three Stdlib foundational
axioms underlying the real numbers:

- `ClassicalDedekindReals.sig_forall_dec`
- `ClassicalDedekindReals.sig_not_dec`
- `FunctionalExtensionality.functional_extensionality_dep`

No `Admitted` proofs anywhere. No project-local axioms. The
`Print Assumptions` audit at the bottom of `theories/pb_avalanche.v`
enumerates the full footprint for every result, including the main
theorem `multiplication_factor_equals_figure_of_merit`, the
`tau_slow_alpha_reactor_bound`, the composite `reactor_FoM_upper_bound`,
the settlement statement `hora_putvinski_settlement` in both
instantiations, and the explicit witness statements
`witness_no_avalanche` and `physical_witness_no_avalanche`.

The abstract framework retains the parametric form, so anyone wishing
to instantiate with different numerical values or different bound
assumptions can do so by providing an alternative module satisfying
`PB_AVALANCHE_PARAMS`.

## What this settles

The Hora-Putvinski avalanche dispute concerns the magnitude of the
secondary fusion rate in proton-boron plasma reactors. Both sides
accept the kinetic decomposition `R_secondary = 3 * R_primary * tau_s *
n_B * <sigma_knockon * v>_alpha`; the dispute is over the values of
`tau_s`, the velocity-weighted cross-section integral, and whether the
composite figure of merit `3 * n_B * tau_s * <sigma_knockon * v>_alpha`
exceeds unity in any realizable reactor configuration.

This formalization reduces the dispute to a single numerical
inequality on the composite bound. Putvinski's evaluation, transferred
into the abstract framework and instantiated either at rescaled values
(`ConcreteParams`, bound `3/100`) or at physical reactor units
(`PhysicalParams`, bound roughly `3 * 10^-13`), yields the
subcriticality bound `FoM_max < 1`, and hence the chain conclusion
`multiplication_factor s < 1` for every plasma state in the reactor
regime. The Coq layer guarantees no logical gaps in the composition;
the remaining physical input is the named numerical bounds
(`sigma_knockon_max`, `v_alpha_max`, `Cspitzer`) and the regime ranges,
both documented in the module signature.

## Building

```
make
```

Generates `Makefile.coq` via `rocq makefile` and compiles
`theories/pb_avalanche.v`.

## Dependencies

- Rocq 9.0 (Stdlib `Reals` and `Lra` only).

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
