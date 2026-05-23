# TODO

Ten outstanding cure statements. Each is the construction that closes
the corresponding gap.

## 1. Tight `M_2 * (b - a)^2 / 8` curvature error via Rolle's-twice

Bridge `is_derive` to Stdlib's `Reals.MVT.Rolle` via `is_derive_Reals` +
`derivable_pt_lim`. Construct the auxiliary
`h(s) := sigma(s) - L(s) - K * (s - a)(s - b)` with K chosen so
`h(t) = 0`. Apply Rolle to `h` on `[a, t]` and `[t, b]` to obtain α, β
with `h'(alpha) = h'(beta) = 0`; apply Rolle to `h'` on `[α, β]` to
obtain ζ with `h''(zeta) = 0`. This forces `K = sigma''(zeta) / 2`, and
the constant 1/8 comes from `max_{t in [a,b]} (t - a)(b - t) =
(b - a)^2 / 4`. Replace the looser `M_2 * (b - a)^2` bound in
`interp_segment_curvature_error` (pb_avalanche_iaea.v) with the
sharp `M_2 * (b - a)^2 / 8`.

## 2. Romberg `O(h^{2k+2})` convergence rate

Build the Bernoulli-number sequence `B_n : nat -> Q` via the standard
recurrence `sum_{j=0}^{n} C(n+1, j) B_j = 0` with `B_0 = 1`. Prove the
Euler-Maclaurin expansion
`T_n(f) - integral_a^b f = sum_{j=1}^{k} B_{2j}/(2j)! * h_n^{2j} *
(f^(2j-1)(b) - f^(2j-1)(a)) + R_k(h_n)` with `|R_k(h)| <= C * h^{2k+2}`
for `f in C^{2k+2}`. Show that Richardson cancellation at level k zeros
out `c_2, ..., c_{2k}` by linear combination, yielding
`romberg f a b k - integral_a^b f = O(h^{2k+2})`. Add to
`pb_avalanche_romberg.v`.

## 3. Wave-physics Coulomb tunneling

Build the regular and irregular Coulomb wave functions `F_l(eta, rho)`
and `G_l(eta, rho)` as power series in `rho` with coefficient
recurrences from the Coulomb-modified Bessel equation
`d²w/drho² + (1 - 2*eta/rho - l(l+1)/rho²) w = 0`. Prove asymptotic
matching: `F_l(eta, rho) -> sin(rho - eta*ln(2*rho) - l*pi/2 +
sigma_l)` as `rho -> infinity`, with `sigma_l = arg(Gamma(l+1+i*eta))`.
Derive the partial-wave Gamow factor `T_l(E) := F_l(eta, k*R_nuclear)^2
+ G_l(eta, k*R_nuclear)^2`. Verify `T_0(E) ~ exp(-2*pi*eta)` for
`pi*eta >> 1`, recovering the semiclassical Gamow factor in
`pb_avalanche_gamow.v` as the s-wave leading order. Quantify the
`l > 0` corrections.

## 4. Time-evolution layer for the kinetic equations

Build the constructive Banach fixed-point operator
`picard_iter : (R -> R -> R) -> R -> R -> nat -> R -> R` with
`picard_iter F y0 t0 0 t := y0` and
`picard_iter F y0 t0 (S n) t := y0 + RInt (fun s => F s (picard_iter
F y0 t0 n s)) t0 t`. Prove `picard_iter` is Cauchy in the uniform
metric on `[t0, t0+T]` for `T < 1 / L` (Lipschitz constant of F).
Define `solve_ode F y0 t0 := Lim_seq (fun n => picard_iter F y0 t0 n)`.
Apply to `dn_ash/dt = R_primary - n_ash / tau_ash` to recover
`n_ash(t) = n_ash_eq * (1 - exp(-t / tau_ash))`. Compose with
`M_ash_decreasing` from `pb_avalanche_ash.v` to derive `M(t)`'s
monotone decrease toward `M_infty < M(0)`.

## 5. Full 3D Fubini volumetric averaging

Define `is_RInt_3D f (a1 b1 a2 b2 a3 b3 : R) (l : R) : Prop` via three
nested Coquelicot `is_RInt`s on `f : R -> R -> R -> R`. Prove
`RInt_3D_swap_xy`, `RInt_3D_swap_yz`, `RInt_3D_swap_xz` —
Fubini-Tonelli for continuous `f` on a box. Replace the radial 1-D
`M_volumetric` in `pb_avalanche_spatial.v` with the full
`M_volumetric_3D := RInt_3D M_local 0 R_max 0 (2*pi) 0 pi`. Prove
`M_volumetric_3D_pointwise_bound` and the spherical-coordinate
specialisation back to the radial formula.

## 6. Distributional Fokker-Planck via test-function pairing

Define `test_function : Type := {phi : R -> R | (forall k, smooth_at k
phi) /\ (exists a b, forall x, x < a \/ b < x -> phi x = 0)}` (compactly
supported smooth functions). Define
`weak_FP f phi := RInt (fun E => f E * (Edot E * phi E)') E_min E_max +
RInt (fun E => f E * (D E * phi'' E)) E_min E_max`. Use
`is_RInt_derive` and the product rule to prove
`forall phi : test_function, weak_FP f_slowing phi = S * phi(E_birth)`,
i.e. `f_slowing` is the distributional solution of
`-d/dE(Edot * f) + d²/dE²(D * f) = S * delta(E - E_birth)`.

## 7. Boltzmann transport equation with full collision integral

Define `f_pt : R -> R^3 -> R -> R` (phase-space density at position x,
velocity v, time t). Define the binary-collision integral
`C[f] x v t := RInt_3D (fun v' => RInt_3D (fun u => sigma(g) * g *
(f(x, v_prime_out, t) * f(x, u_prime_out, t) - f(x, v, t) * f(x, u, t)))
u_min u_max v'_min v'_max)` where `g = ||v - u||` and `(v', u')` are
the post-collision momenta from elastic scattering. Prove the steady-
state moment-equation reduction recovers `f_slowing(E) propto
tau_s(E) / E` as the slow-down limit of the energy moment of `f_pt`.

## 8. Relativistic bremsstrahlung (Bethe-Heitler)

Define the Bethe-Heitler differential cross section
`d_sigma_BH/d_omega := (Z^2 * alpha_fs^3 / m_e^2) * F(E, omega)`
with the Bethe-Maximon screening function
`F(E, omega) := (E²+E'²)/(E²) * (ln(2*E*E'/(omega*m_e)) - 1/2) -
2*E*E'/(3*E²)` (Heitler form). Integrate over emitted-photon
frequency `omega in [omega_min, E - m_e]` to get
`sigma_BH_total(E)`. Define the radiative loss rate
`bremsstrahlung_rel := n_e * Z² * integral_0^infinity
v_e(E) * sigma_BH_total(E) * f_M(E, T) dE` for a Maxwellian electron
distribution. Prove `bremsstrahlung_rel -> bremsstrahlung_NR` as
`T / (m_e c²) -> 0`, matching the existing non-relativistic
`bremsstrahlung := C_brems * Z_eff^2 * n_e^2 * sqrt T` in
`pb_avalanche_energy_balance.v`.

## 9. Constructive integration eliminating `Classical_Prop.classic`

Define `is_RInt_intuit f a b l := forall eps : Q, 0 < eps ->
{delta : Q | 0 < delta /\ forall (P : list (R*R)) (mesh : Q),
tagged_partition P a b mesh -> mesh < delta -> Rabs (riemann_sum f P
- l) < eps}`. Re-derive `is_RInt_derive`, `RInt_le`, `RInt_plus`,
`RInt_const`, and the change-of-variable formula over this predicate.
Re-plumb every theorem in the development that currently uses
Coquelicot's classical `is_RInt` through `is_RInt_intuit`. The axiom
footprint collapses to the three Stdlib Dedekind axioms alone.

## 10. Meta-theorem on irreducibility of the axiom footprint

For each axiom `A in {Classical_Prop.classic, sig_forall_dec,
sig_not_dec, functional_extensionality_dep}`, construct a model
`M_A : Type -> Prop` (in Stdlib or Coq's type theory) in which the
other three axioms hold but `A` fails, and exhibit a plasma state
`s_A` in that model for which `hora_putvinski_settlement` is false.
The four-axiom footprint becomes itself a Coq-checked irreducibility
theorem: each axiom is independently necessary.

## Build

```
eval $(opam env --switch=rocq9)
make
make audit-check
```

All 33 files in `theories/` compile clean. The four-axiom footprint
(`ClassicalDedekindReals.sig_forall_dec`,
`ClassicalDedekindReals.sig_not_dec`,
`FunctionalExtensionality.functional_extensionality_dep`,
`Classical_Prop.classic`) is verified by `scripts/check_axioms.sh`.
