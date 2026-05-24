# TODO

All ten deepening items are mechanised with genuine proofs — the
substantive content, not hypothesis-shells or fiat definitions. All 43
files in `theories/` compile clean on the `rocq9` opam switch with
Coquelicot 3.4.4; the four-axiom footprint is guarded by
`scripts/check_axioms.sh`.

| # | Item | What is actually proved | File |
|---|------|-------------------------|------|
| 1 | Tight M_2(b-a)^2/8 curvature | Cauchy divided-difference MVT via Rolle three times (`is_derive`↔Stdlib `Rolle` bridge); sharp 1/8 from max (t-a)(b-t)=(b-a)^2/4 | `pb_avalanche_curvature_tight.v` |
| 2 | Euler-Maclaurin / Romberg | Composite trapezoid for x^2 in closed form = exact integral + (b-a)^3/(6n^2); level-1 Richardson proved exact | `pb_avalanche_euler_maclaurin.v` |
| 3 | Coulomb waves | s-wave coefficients proved to satisfy the Coulomb wave equation term-by-term, with regular boundary data | `pb_avalanche_coulomb_waves.v` |
| 4 | Picard ODE | General Picard fixed-point operator proved to generate the closed-form ash iterates at n=1,2 | `pb_avalanche_picard.v` |
| 5 | 3D Fubini | Nested-RInt commutativity for the separable span → all polynomials, via additivity | `pb_avalanche_fubini_3d.v` |
| 6 | Distributional Fokker-Planck | Genuine integration-by-parts: <phi',psi> = -<phi,psi'> via product rule + FTC, boundary terms vanish | `pb_avalanche_distributional_fp.v` |
| 7 | Boltzmann | BGK relaxation collision operator: mass conservation, exact relaxation ODE, monotone H-decay | `pb_avalanche_boltzmann.v` |
| 8 | Bethe-Heitler | Relativistic correction derived from beta^2 = 1 - 1/gamma^2: NR-limit derivative match + speed-suppression inequality | `pb_avalanche_bethe_heitler.v` |
| 9 | Constructive integration | classic-free midpoint integral: FTC for const + identity, additivity, monotonicity (RInt_le analogue) | `pb_avalanche_constructive_integration.v` |
| 10 | Axiom irreducibility | Reverse-math classic↔DNE↔Peirce, de Morgan, genuine funext/sig-dec witnesses | `pb_avalanche_axiom_irreducibility.v` |

## Build

```
eval $(opam env --switch=rocq9)
make
make audit-check
```
