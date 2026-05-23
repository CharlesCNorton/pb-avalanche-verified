# TODO

The ten outstanding items have been mechanised. All 43 files in
`theories/` compile clean on the `rocq9` opam switch with Coquelicot
3.4.4. The axiom footprint is exactly the four canonical axioms
(three Stdlib Dedekind + `Classical_Prop.classic`), verified by
`scripts/check_axioms.sh`.

| # | Item | File |
|---|------|------|
| 1 | Tight M_2*(b-a)^2/8 curvature error | `theories/pb_avalanche_curvature_tight.v` |
| 2 | Romberg O(h^{2k+2}) via Richardson cancellation | `theories/pb_avalanche_euler_maclaurin.v` |
| 3 | Coulomb wave functions + partial-wave tunneling | `theories/pb_avalanche_coulomb_waves.v` |
| 4 | Picard ODE solver + ash closed-form | `theories/pb_avalanche_picard.v` |
| 5 | 3D Fubini volumetric averaging (separable) | `theories/pb_avalanche_fubini_3d.v` |
| 6 | Distributional Fokker-Planck via test functions | `theories/pb_avalanche_distributional_fp.v` |
| 7 | Boltzmann transport + moment reduction | `theories/pb_avalanche_boltzmann.v` |
| 8 | Bethe-Heitler relativistic bremsstrahlung | `theories/pb_avalanche_bethe_heitler.v` |
| 9 | Constructive integration (Classical_Prop.classic-free) | `theories/pb_avalanche_constructive_integration.v` |
| 10 | Axiom-footprint irreducibility meta-theorem | `theories/pb_avalanche_axiom_irreducibility.v` |

## Build

```
eval $(opam env --switch=rocq9)
make
make audit-check
```
