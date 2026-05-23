# Proton-Boron Avalanche Fusion: Verified Bounds on Chain Multiplication

A Rocq formalization of the kinetic rate equations for alpha-induced
secondary p+11B reactions, giving necessary and sufficient conditions
for the secondary-to-primary rate ratio to exceed unity. The result
bears on the Hora-Putvinski avalanche dispute: avalanche multiplication
is realizable if and only if a single closed kinetic figure of merit
exceeds 1.

## Main result

For any plasma state `s = (n_p, n_B, T_keV, B_T)` with strictly positive
densities, temperature, and field, the multiplication factor

  M(s) = R_secondary(s) / R_primary(s)

equals the closed avalanche figure of merit

  FoM(s) = 3 * n_B(s) * tau_slow_alpha(s) * <sigma_knockon * v>_alpha(s).

Theorem `multiplication_factor_equals_figure_of_merit` is the
proof of this identity in any model of the kinetic axioms below. The
corollaries `avalanche_threshold_iff`, `avalanche_subcritical_iff`, and
`avalanche_critical_iff` give the necessary and sufficient form of the
avalanche regime:

  M(s) > 1   iff   FoM(s) > 1.

Composing this with the Spitzer-Trubnikov slowing-down formula
exposes the explicit dependence on `(n_p, n_B, T_keV)` and hence the
parametric envelope within which avalanche multiplication is or is not
realizable.

## Kinetic axioms

The plasma-kinetics derivations underlying the result live outside the
Rocq layer; in the source they appear as three named axioms:

| Axiom | Physical content |
|---|---|
| `tau_slow_alpha_spitzer_axiom` | Spitzer-Trubnikov mean slowing-down time of a birth-energy alpha on the Maxwellian background, `tau_s = Cspitzer * T_keV * sqrt(T_keV) / (n_p + Z_B^2 * n_B)`. |
| `f_alpha_slowing_down_axiom`   | Steady-state Fokker-Planck slowing-down distribution with the p+11B source, `f(E) = R_primary * tau_s / (E * E_birth)` for `0 < E < E_birth`. |
| `R_secondary_kinetic_axiom`    | Bilinear kinetic decomposition of the alpha-induced secondary fusion rate, `R_secondary = 3 * R_primary * tau_s * n_B * <sigma_knockon * v>_alpha`. |

The intermediate lemmas `tau_slow_alpha_spitzer_formula`,
`f_alpha_slowing_down_equilibrium`, and `R_secondary_kinetic_decomposition`
discharge directly to these axioms; the main theorem composes
`R_secondary_kinetic_axiom` with the algebra of `R` and the
non-vanishing of `R_primary`.

## Axiom footprint

Every result is closed by `Qed`. The `Print Assumptions` audit at the
bottom of `theories/pb_avalanche.v` enumerates the full axiom set every
result depends on. For the main theorem
`multiplication_factor_equals_figure_of_merit` the audit reports:

- the four abstract `Parameter` symbols `tau_slow_alpha`,
  `sigma_v_pB_thermal`, `alpha_weighted_secondary_velocity_integral`,
  and `R_secondary`;
- the cross-section positivity axiom `sigma_v_pB_thermal_positive`;
- the physical-content axiom `R_secondary_kinetic_axiom`;
- the two Stdlib axioms underlying the Dedekind real numbers
  (`ClassicalDedekindReals.sig_forall_dec` and
  `FunctionalExtensionality.functional_extensionality_dep`).

No `Admitted` proofs, no project-local axioms beyond the three kinetic
axioms named above.

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
