# TODO

The substantive core of every deepening item is mechanised with
complete `Qed` proofs; 43 files in `theories/` compile clean on the
`rocq9` switch with Coquelicot 3.4.4, and the four-axiom footprint is
guarded by `scripts/check_axioms.sh`. The cores landed so far:

- sharp `/8` curvature bound wired into the IAEA segment error;
- CI workflow;
- general `C^2` trapezoidal panel error (tight `/12` constant) via the
  divided-difference MVT;
- Coulomb power-series convergence for all `rho`;
- the closed-form ash solution as the Picard fixed point;
- iterated-integral additivity and Fubini closure under sums;
- the weak=strong Fokker-Planck drift duality;
- collision-invariant conservation from gain-loss balance;
- the `sqrt(T)` bremsstrahlung law from Maxwellian moment scaling;
- uniqueness of the `classic`-free constructive integral;
- the `sig_forall_dec <-> LPO` characterisation.

The next nine items carry those cores to full generality. Each is the
construction that closes it.

## 1. Bernoulli-Peano Euler-Maclaurin to all orders

Construct the Bernoulli-number sequence `B_n : nat -> Q` from the
recurrence `sum_{j=0}^{n} C(n+1,j) B_j = 0`, `B_0 = 1`, and prove the
expansion
`T_n f - integral_a^b f = sum_{j=1}^{k} B_{2j}/(2j)! h^{2j}
(f^(2j-1)(b) - f^(2j-1)(a)) + R_k` with `|R_k| <= C h^{2k+2}` for
`f in C^{2k+2}`, via the periodic-Bernoulli Peano kernel; conclude
`romberg f a b k - integral = O(h^{2k+2})` at every level `k`,
generalising the order-2 panel result already proved.

## 2. Coulomb irregular solution and asymptotic matching

Construct the irregular s-wave Coulomb function `G_0(eta, rho)` and
prove the asymptotic matching
`F_0(eta, rho) ~ sin(rho - eta * ln(2 rho) + sigma_0)` and
`G_0(eta, rho) ~ cos(rho - eta * ln(2 rho) + sigma_0)` as
`rho -> infinity`, with `sigma_0 = arg(Gamma(1 + i eta))`. Define the
penetrability `P_0 = 1 / (F_0^2 + G_0^2)` and derive
`P_0 ~ exp(-2 pi eta)` for `pi eta >> 1` from it, replacing the
postulated `penetrability_s_wave` with this derived value.

## 3. Banach convergence of the Picard iterates

Prove the general Picard iterate sequence `picard F y0 t0 n` is
uniformly Cauchy on `[t0, t0 + T]` for `T < 1/L` (Lipschitz constant
`L` of the right-hand side), define `solve_ode := Lim_seq (picard ...)`
in the sup metric, and prove it equals `n_ash_solution` for the affine
ash equation at every `n` — extending the fixed-point property and the
`n = 1, 2` iterates already proved.

## 4. Fubini for arbitrary continuous integrands

Prove `iter_rint_xyz f = iter_rint_yxz f = iter_rint_zxy f` for every
`f` continuous on the box `[a,b] x [c,d] x [e,g]`, via uniform
continuity and convergence of the 3-D Riemann sums (Stone-Weierstrass
approximation by the separable span on which commutativity is already
established), removing the additive-closure restriction.

## 5. Exact delta-source Fokker-Planck identity

Prove `weak_FP f_slowing phi = S * phi(E_birth)` for the slowing-down
distribution `f_slowing(E) = S * tau(E) / E` and every test function
`phi`, by splitting the weak pairing at `E_birth` and applying the
integration-by-parts identity on each side, building on the weak=strong
drift duality already proved.

## 6. Explicit binary-collision integral

Build the binary Boltzmann collision integral
`C[f](v) = integral integral sigma(g) g (f(v') f(u') - f(v) f(u))
du domega` over post-collision momenta `(v', u')`, and derive the
collision invariants `integral C[f] {1, v, v^2} dv = 0` and the
H-theorem from the `(v,u) <-> (v',u')` scattering symmetry, recovering
the gain-loss conservation laws already proved as its corollary.

## 7. Bethe-Maximon cross section and the sqrt(T) law

Integrate the Bethe-Heitler form factor `F_BH` over emitted-photon
energy to obtain `sigma_BH_total(E)`, form the Maxwellian-averaged
radiated power `integral v_e(E) sigma_BH_total(E) f_M(E, T) dE`, and
derive `bremsstrahlung_NR ~ C Z^2 n_e^2 sqrt(T)` from that integral,
joining it to the Maxwellian moment scaling and spectral integral
already proved.

## 8. Constructive integration across the development

Extend `is_RInt_intuit` with a fundamental theorem of calculus for
general `C^1` integrands and change-of-variables, then route every
Coquelicot-integral use in the development through `is_RInt_intuit`, so
the whole footprint collapses to the three Dedekind axioms — building on
the predicate, base cases, linearity, monotonicity and uniqueness
already proved `classic`-free.

## 9. Axiom-independence models

Construct, for each axiom in the footprint, a model of the remaining
three in which that axiom fails, together with a plasma state that
falsifies `hora_putvinski_settlement` in that model, turning the
four-axiom footprint into a Coq-checked independence theorem — extending
the reverse-mathematics characterisations (`classic <-> DNE <->
Peirce`, `sig_forall_dec <-> LPO`) already proved.

## Build

```
eval $(opam env --switch=rocq9)
make
make audit-check
```
