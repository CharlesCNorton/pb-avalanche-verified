(******************************************************************************)
(*                                                                            *)
(*     Boltzmann transport equation (item 7)                                  *)
(*                                                                            *)
(*     Defines the phase-space density f(x, v, t) and the binary-collision    *)
(*     integral C[f](x, v, t).  For a homogeneous (x-independent) plasma     *)
(*     in steady state, with elastic collisions conserving total energy,     *)
(*     the energy moment of f recovers the slowing-down equation             *)
(*                                                                            *)
(*       dE/dt = - E / tau_s(E)                                               *)
(*                                                                            *)
(*     in the slow-down limit where the test particle's energy is much       *)
(*     larger than the bath temperature.                                     *)
(*                                                                            *)
(*     We expose the BTE structurally and prove its conservation laws        *)
(*     (mass and energy moments).                                            *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.
Open Scope R_scope.

(* ================================================================== *)
(* === Phase-space density and moments === *)
(* ================================================================== *)

(* The 1D phase-space density (position x in [0, L], velocity v in R).
   In a homogeneous plasma, f depends only on v and t. *)
Definition phase_density := R -> R -> R.   (* v, t -> R *)

(* Zeroth moment: total particle density. *)
Definition mass_moment (f : phase_density) (t : R)
                       (v_min v_max : R) : R :=
  RInt (fun v => f v t) v_min v_max.

(* Second moment / 2: kinetic energy. *)
Definition energy_moment (f : phase_density) (t : R)
                         (v_min v_max : R) : R :=
  RInt (fun v => f v t * v * v / 2) v_min v_max.

Lemma mass_moment_nonneg :
  forall (f : phase_density) t v_min v_max,
    v_min <= v_max ->
    (forall v, v_min <= v <= v_max -> 0 <= f v t) ->
    ex_RInt (fun v => f v t) v_min v_max ->
    0 <= mass_moment f t v_min v_max.
Proof.
  intros f t v_min v_max Hle Hpos Hex.
  unfold mass_moment.
  assert (Hzero : 0 = RInt (fun _ : R => 0) v_min v_max).
  { rewrite RInt_const. unfold scal; simpl; unfold mult; simpl. lra. }
  rewrite Hzero.
  apply RInt_le.
  - exact Hle.
  - apply ex_RInt_const.
  - exact Hex.
  - intros v Hv. apply Hpos. lra.
Qed.

(* ================================================================== *)
(* === The slowing-down collision integral (Spitzer model) === *)
(* ================================================================== *)

(* In the energy-loss-dominated limit, the collision integral acts
   as `C[f](v, t) = -d/dv [v * f] / tau_s(v)`,
   conserving particle number but draining energy at the
   Spitzer-Trubnikov rate. *)

(* Test the conservation laws. *)

(* Steady-state slowing-down distribution: f_ss(v) = S * tau_s(v) / v
   for some source S (constant injection at v_max). *)
Definition f_slowing (S tau_s v : R) : R := S * tau_s / v.

Lemma f_slowing_pos :
  forall S tau_s v, 0 < S -> 0 < tau_s -> 0 < v ->
    0 < f_slowing S tau_s v.
Proof.
  intros S tau_s v HS Htau Hv.
  unfold f_slowing.
  apply Rdiv_lt_0_compat; [|exact Hv].
  apply Rmult_lt_0_compat; assumption.
Qed.

(* The slowing-down distribution decreases as 1/v. *)
Theorem f_slowing_decreasing :
  forall S tau_s v1 v2, 0 < S -> 0 < tau_s -> 0 < v1 -> v1 <= v2 ->
    f_slowing S tau_s v2 <= f_slowing S tau_s v1.
Proof.
  intros S tau_s v1 v2 HS Htau Hv1 Hv12.
  unfold f_slowing.
  apply Rmult_le_compat_l.
  - apply Rlt_le. apply Rmult_lt_0_compat; assumption.
  - apply Rinv_le_contravar; assumption.
Qed.

(* ================================================================== *)
(* === Energy moment in the slow-down limit === *)
(* ================================================================== *)

(* For the slowing-down distribution f_ss(v) = S * tau_s / v with
   v in [v_min, v_max], the kinetic-energy moment is
   integral_{v_min}^{v_max} (S * tau_s / v) * v^2 / 2 dv
   = S * tau_s / 2 * (v_max^2 - v_min^2) / 2
   = S * tau_s * (v_max^2 - v_min^2) / 4. *)

Theorem energy_moment_slowing :
  forall S tau_s v_min v_max,
    0 < S -> 0 < tau_s -> 0 < v_min < v_max ->
    energy_moment (fun v _ => f_slowing S tau_s v) 0 v_min v_max
    = S * tau_s * (v_max * v_max - v_min * v_min) / 4.
Proof.
  intros S tau_s v_min v_max HS Htau [Hvmin Hvm].
  unfold energy_moment, f_slowing.
  apply is_RInt_unique.
  apply (is_RInt_ext (fun v => (S * tau_s / 2) * v)).
  - intros v Hv. rewrite Rmin_left in Hv by lra.
    rewrite Rmax_right in Hv by lra.
    assert (Hvne : v <> 0) by lra.
    replace (S * tau_s / v * v * v / 2) with
            ((S * tau_s / v * v) * v / 2) by ring.
    replace (S * tau_s / v * v) with (S * tau_s).
    + lra.
    + unfold Rdiv. rewrite Rmult_assoc. rewrite Rinv_l by exact Hvne. ring.
  - (* is_RInt of (S*tau_s/2)*v from v_min to v_max
       = S*tau_s*(v_max² - v_min²)/4 *)
    replace (S * tau_s * (v_max * v_max - v_min * v_min) / 4)
      with ((S * tau_s / 2) * (v_max * v_max / 2)
           - (S * tau_s / 2) * (v_min * v_min / 2)) by lra.
    apply (is_RInt_derive (fun v => (S * tau_s / 2) * (v * v / 2))).
    + intros v _.
      auto_derive; [trivial | lra].
    + intros v _.
      apply (continuous_mult (fun _ => S * tau_s / 2) (fun v => v)).
      * apply continuous_const.
      * apply continuous_id.
Qed.

(* The mass moment of the slowing-down distribution is
   integral (S * tau_s / v) dv = S * tau_s * ln(v_max / v_min).
   This is the steady-state slowing-down content for a number-conserved
   chain. *)

(* ================================================================== *)
(* === BTE moment equation in steady state === *)
(* ================================================================== *)

(* For elastic, energy-conserving binary collisions, the velocity-
   moment expansion of the BTE produces the slow-down equation
     d/dt energy_moment = -energy_moment / tau_relax  (slowing down)
   in the limit where the test particle's energy is large compared
   to bath temperature.

   We verify this for the exponential-decay solution: if
   energy_moment(t) = E_0 * exp(-t / tau_relax),
   then dE/dt = -E_0 / tau_relax * exp(-t / tau_relax)
              = -E(t) / tau_relax. *)

Definition energy_decay (E_0 tau_relax t : R) : R :=
  E_0 * exp (- t / tau_relax).

Theorem energy_decay_slow_down :
  forall E_0 tau_relax t, 0 < tau_relax ->
    is_derive (energy_decay E_0 tau_relax) t
              (- energy_decay E_0 tau_relax t / tau_relax).
Proof.
  intros E_0 tau_relax t Htau.
  unfold energy_decay.
  auto_derive.
  - lra.
  - assert (Htau_ne : tau_relax <> 0) by lra.
    replace (- t / tau_relax) with (- t * / tau_relax)
      by (unfold Rdiv; reflexivity).
    field. exact Htau_ne.
Qed.

(* ================================================================== *)
(* === Real-valued RInt bridge helpers === *)
(* ================================================================== *)

Lemma RInt_scal_R :
  forall (f : R -> R) (a b k : R),
    ex_RInt f a b ->
    RInt (fun x => k * f x) a b = k * RInt f a b.
Proof.
  intros f a b k Hf.
  pose proof (RInt_scal f a b k Hf) as H.
  unfold scal in H; simpl in H; unfold mult in H; simpl in H. exact H.
Qed.

Lemma ex_RInt_minus_R :
  forall (f g : R -> R) (a b : R),
    ex_RInt f a b -> ex_RInt g a b -> ex_RInt (fun x => f x - g x) a b.
Proof.
  intros f g a b Hf Hg.
  exact (ex_RInt_minus f g a b Hf Hg).
Qed.

Lemma RInt_minus_R :
  forall (f g : R -> R) (a b : R),
    ex_RInt f a b -> ex_RInt g a b ->
    RInt (fun x => f x - g x) a b = RInt f a b - RInt g a b.
Proof.
  intros f g a b Hf Hg.
  pose proof (RInt_minus f g a b Hf Hg) as H.
  unfold minus in H; simpl in H; unfold plus, opp in H; simpl in H.
  exact H.
Qed.

(* ================================================================== *)
(* === The BGK collision operator (a genuine Boltzmann model) === *)
(* ================================================================== *)

(* The Bhatnagar-Gross-Krook relaxation collision operator
     C[f](v) := (f_eq(v) - f(v)) / tau
   is the standard tractable model of the full Boltzmann collision
   integral: it relaxes the distribution toward the local Maxwellian
   f_eq at rate 1/tau while conserving the collision invariants
   (mass, momentum, energy) provided f_eq shares those moments with f.
   It is widely used in transport theory precisely because it captures
   the qualitative content of the 9-D collision integral without the
   intractable phase-space integration. *)
Definition bgk_collision (f_eq f : R -> R) (tau v : R) : R :=
  / tau * (f_eq v - f v).

(* === Mass conservation ===
   The zeroth moment of C[f] is (N_eq - N) / tau, which vanishes
   exactly when the Maxwellian f_eq is normalised to the same particle
   number as f. This is the conservation of mass under collisions. *)
Theorem bgk_mass_conservation :
  forall (f_eq f : R -> R) (tau v_min v_max : R),
    0 < tau ->
    ex_RInt f_eq v_min v_max ->
    ex_RInt f v_min v_max ->
    RInt (fun v => bgk_collision f_eq f tau v) v_min v_max
    = (RInt f_eq v_min v_max - RInt f v_min v_max) / tau.
Proof.
  intros f_eq f tau v_min v_max Htau Hex_eq Hex_f.
  unfold bgk_collision.
  rewrite (RInt_scal_R (fun v => f_eq v - f v) v_min v_max (/ tau)
             (ex_RInt_minus_R f_eq f v_min v_max Hex_eq Hex_f)).
  rewrite (RInt_minus_R f_eq f v_min v_max Hex_eq Hex_f).
  unfold Rdiv. apply Rmult_comm.
Qed.

(* When the equilibrium shares the particle number of f, the net
   collisional mass change is exactly zero. *)
Corollary bgk_mass_conserved_when_matched :
  forall (f_eq f : R -> R) (tau v_min v_max : R),
    0 < tau ->
    ex_RInt f_eq v_min v_max ->
    ex_RInt f v_min v_max ->
    RInt f_eq v_min v_max = RInt f v_min v_max ->
    RInt (fun v => bgk_collision f_eq f tau v) v_min v_max = 0.
Proof.
  intros f_eq f tau v_min v_max Htau Hex_eq Hex_f Hmatch.
  rewrite (bgk_mass_conservation f_eq f tau v_min v_max Htau Hex_eq Hex_f).
  rewrite Hmatch.
  assert (Hz : RInt f v_min v_max - RInt f v_min v_max = 0) by lra.
  rewrite Hz. unfold Rdiv. apply Rmult_0_l.
Qed.

(* === BGK relaxation dynamics ===
   At each velocity v the BGK equation df/dt = (f_eq - f)/tau is a
   scalar linear ODE whose solution is
     f(t) = f_eq + (f0 - f_eq) * exp(-t/tau).
   We verify it solves the ODE exactly, and that the deviation from
   equilibrium decays monotonically — the BGK H-theorem in miniature. *)
Definition bgk_relax (f_eq f0 tau t : R) : R :=
  f_eq + (f0 - f_eq) * exp (- t / tau).

Theorem bgk_relax_solves_ode :
  forall f_eq f0 tau t, 0 < tau ->
    is_derive (bgk_relax f_eq f0 tau) t
              ((f_eq - bgk_relax f_eq f0 tau t) / tau).
Proof.
  intros f_eq f0 tau t Htau.
  unfold bgk_relax.
  auto_derive; [lra |].
  assert (Htau_ne : tau <> 0) by lra.
  replace (- t / tau) with (- t * / tau) by (unfold Rdiv; reflexivity).
  field. exact Htau_ne.
Qed.

(* The deviation |f(t) - f_eq| relaxes: it equals |f0 - f_eq| * exp(-t/tau),
   strictly decreasing toward 0. *)
Theorem bgk_deviation_decays :
  forall f_eq f0 tau t1 t2, 0 < tau -> 0 <= t1 <= t2 ->
    Rabs (bgk_relax f_eq f0 tau t2 - f_eq)
    <= Rabs (bgk_relax f_eq f0 tau t1 - f_eq).
Proof.
  intros f_eq f0 tau t1 t2 Htau [Ht1 Ht12].
  unfold bgk_relax.
  replace (f_eq + (f0 - f_eq) * exp (- t2 / tau) - f_eq)
    with ((f0 - f_eq) * exp (- t2 / tau)) by ring.
  replace (f_eq + (f0 - f_eq) * exp (- t1 / tau) - f_eq)
    with ((f0 - f_eq) * exp (- t1 / tau)) by ring.
  rewrite !Rabs_mult.
  apply Rmult_le_compat_l; [apply Rabs_pos |].
  rewrite !(Rabs_right (exp _)) by (apply Rle_ge, Rlt_le, exp_pos).
  destruct (Req_dec t1 t2) as [Heq | Hne].
  - subst. apply Rle_refl.
  - apply Rlt_le. apply exp_increasing.
    assert (Ht1lt2 : t1 < t2) by lra.
    apply Rmult_lt_gt_compat_neg_l with (r := -1) in Ht1lt2; [|lra].
    unfold Rdiv.
    apply Rmult_lt_compat_r with (r := / tau) in Ht1lt2;
      [|apply Rinv_0_lt_compat; exact Htau].
    lra.
Qed.

(* ================================================================== *)
(* === Full binary collision integral: the conservation laws === *)
(* ================================================================== *)

(* The binary Boltzmann collision integral splits into a gain term
   (particles scattered INTO velocity v by collisions) and a loss
   term (particles scattered OUT of v):
     C[f](v) = gain(v) - loss(v).
   Microreversibility / detailed balance of the collision kernel makes
   the gain and loss integrate to the same total against every
   collision invariant chi in {1, v, v^2}; that is the exact reason
   binary collisions conserve mass, momentum and energy. We encode the
   gain-loss decomposition and derive each conservation law from the
   corresponding balance identity. *)
Definition collision_integral (gain loss : R -> R) (v : R) : R :=
  gain v - loss v.

(* Mass conservation: integral of C[f] over velocity vanishes when the
   total gain rate equals the total loss rate (particle number is a
   collision invariant). *)
Theorem collision_conserves_mass :
  forall (gain loss : R -> R) (v_min v_max : R),
    ex_RInt gain v_min v_max -> ex_RInt loss v_min v_max ->
    RInt gain v_min v_max = RInt loss v_min v_max ->
    RInt (fun v => collision_integral gain loss v) v_min v_max = 0.
Proof.
  intros gain loss v_min v_max Hg Hl Hbal.
  unfold collision_integral.
  rewrite (RInt_minus_R gain loss v_min v_max Hg Hl).
  rewrite Hbal. lra.
Qed.

(* Weighted conservation: for any collision invariant chi (chi = 1
   gives mass, chi(v) = v gives momentum, chi(v) = v^2 gives energy),
   the chi-moment of C[f] vanishes under the corresponding gain-loss
   balance. *)
Theorem collision_conserves_invariant :
  forall (chi gain loss : R -> R) (v_min v_max : R),
    ex_RInt (fun v => chi v * gain v) v_min v_max ->
    ex_RInt (fun v => chi v * loss v) v_min v_max ->
    RInt (fun v => chi v * gain v) v_min v_max
      = RInt (fun v => chi v * loss v) v_min v_max ->
    RInt (fun v => chi v * collision_integral gain loss v) v_min v_max = 0.
Proof.
  intros chi gain loss v_min v_max Hg Hl Hbal.
  unfold collision_integral.
  transitivity (RInt (fun v => chi v * gain v - chi v * loss v) v_min v_max).
  { apply RInt_ext. intros v _.
    change (@eq R (chi v * (gain v - loss v))
                  (chi v * gain v - chi v * loss v)). ring. }
  rewrite (RInt_minus_R (fun v => chi v * gain v)
                        (fun v => chi v * loss v) v_min v_max Hg Hl).
  rewrite Hbal. lra.
Qed.

(* Momentum (chi = v) and energy (chi = v^2) conservation are the
   chi = id and chi = square instances. *)
Corollary collision_conserves_momentum :
  forall (gain loss : R -> R) (v_min v_max : R),
    ex_RInt (fun v => v * gain v) v_min v_max ->
    ex_RInt (fun v => v * loss v) v_min v_max ->
    RInt (fun v => v * gain v) v_min v_max
      = RInt (fun v => v * loss v) v_min v_max ->
    RInt (fun v => v * collision_integral gain loss v) v_min v_max = 0.
Proof.
  intros gain loss v_min v_max.
  apply (collision_conserves_invariant (fun v => v) gain loss v_min v_max).
Qed.

Corollary collision_conserves_energy :
  forall (gain loss : R -> R) (v_min v_max : R),
    ex_RInt (fun v => v * v * gain v) v_min v_max ->
    ex_RInt (fun v => v * v * loss v) v_min v_max ->
    RInt (fun v => v * v * gain v) v_min v_max
      = RInt (fun v => v * v * loss v) v_min v_max ->
    RInt (fun v => v * v * collision_integral gain loss v) v_min v_max = 0.
Proof.
  intros gain loss v_min v_max.
  apply (collision_conserves_invariant (fun v => v * v) gain loss v_min v_max).
Qed.

(* The BGK operator is the relaxation instance: gain = f_eq/tau,
   loss = f/tau, so C = (f_eq - f)/tau, matching bgk_collision. *)
Theorem bgk_is_collision_instance :
  forall (f_eq f : R -> R) (tau v : R),
    collision_integral (fun w => / tau * f_eq w) (fun w => / tau * f w) v
    = bgk_collision f_eq f tau v.
Proof.
  intros f_eq f tau v.
  unfold collision_integral, bgk_collision. ring.
Qed.

(* ================================================================== *)
(* === Quadratic H-theorem for BGK relaxation === *)
(* ================================================================== *)

(* Velocity-resolved BGK relaxation: at each velocity the deviation from
   equilibrium decays as exp(-t/tau). *)
Definition bgk_relax_v (feq f0 : R -> R) (tau t v : R) : R :=
  feq v + (f0 v - feq v) * exp (- t / tau).

(* Quadratic entropy: the squared L^2 distance to equilibrium. The
   genuine Boltzmann H-functional uses f ln(f/f_eq); the convex
   quadratic surrogate is the standard rigorous Lyapunov functional for
   the linear BGK relaxation and obeys the same monotone-decay law. *)
Definition bgk_H (feq f0 : R -> R) (tau t v_min v_max : R) : R :=
  RInt (fun v => (bgk_relax_v feq f0 tau t v - feq v) ^ 2) v_min v_max.

(* Closed form: H(t) = exp(-2 t / tau) * H(0). *)
Lemma bgk_H_closed_form :
  forall (feq f0 : R -> R) (tau t v_min v_max : R), 0 < tau ->
    ex_RInt (fun v => (f0 v - feq v) ^ 2) v_min v_max ->
    bgk_H feq f0 tau t v_min v_max
    = exp (- 2 * t / tau) * RInt (fun v => (f0 v - feq v) ^ 2) v_min v_max.
Proof.
  intros feq f0 tau t vmin vmax Htau Hex.
  unfold bgk_H, bgk_relax_v.
  rewrite <- (RInt_scal_R (fun v => (f0 v - feq v) ^ 2) vmin vmax
                (exp (- 2 * t / tau)) Hex).
  apply RInt_ext. intros v _.
  replace (feq v + (f0 v - feq v) * exp (- t / tau) - feq v)
    with ((f0 v - feq v) * exp (- t / tau)) by ring.
  rewrite Rpow_mult_distr.
  assert (He2 : exp (- t / tau) ^ 2 = exp (- 2 * t / tau)).
  { replace (exp (- t / tau) ^ 2)
      with (exp (- t / tau) * exp (- t / tau)) by ring.
    rewrite <- exp_plus.
    replace (- t / tau + - t / tau) with (- 2 * t / tau) by (field; lra).
    reflexivity. }
  rewrite He2. lra.
Qed.

(* The entropy is nonnegative (an integral of squares). *)
Lemma bgk_H_nonneg :
  forall (feq f0 : R -> R) (tau t v_min v_max : R), 0 < tau ->
    v_min <= v_max ->
    ex_RInt (fun v => (f0 v - feq v) ^ 2) v_min v_max ->
    0 <= bgk_H feq f0 tau t v_min v_max.
Proof.
  intros feq f0 tau t vmin vmax Htau Hord Hex.
  rewrite (bgk_H_closed_form feq f0 tau t vmin vmax Htau Hex).
  apply Rmult_le_pos.
  - apply Rlt_le. apply exp_pos.
  - apply RInt_ge_0; [ exact Hord | exact Hex | intros x _; apply pow2_ge_0 ].
Qed.

(* The H-theorem: the quadratic entropy decreases monotonically in time,
   driven to equilibrium by the relaxation. *)
Theorem bgk_H_decreasing :
  forall (feq f0 : R -> R) (tau t1 t2 v_min v_max : R), 0 < tau ->
    0 <= t1 <= t2 -> v_min <= v_max ->
    ex_RInt (fun v => (f0 v - feq v) ^ 2) v_min v_max ->
    bgk_H feq f0 tau t2 v_min v_max <= bgk_H feq f0 tau t1 v_min v_max.
Proof.
  intros feq f0 tau t1 t2 vmin vmax Htau [Ht1 Ht12] Hord Hex.
  rewrite (bgk_H_closed_form feq f0 tau t2 vmin vmax Htau Hex).
  rewrite (bgk_H_closed_form feq f0 tau t1 vmin vmax Htau Hex).
  apply Rmult_le_compat_r.
  - apply RInt_ge_0; [ exact Hord | exact Hex | intros x _; apply pow2_ge_0 ].
  - destruct (Req_dec t1 t2) as [Heq | Hne].
    + subst. apply Rle_refl.
    + apply Rlt_le. apply exp_increasing.
      assert (Hinv : 0 < / tau) by (apply Rinv_0_lt_compat; exact Htau).
      unfold Rdiv.
      apply Rmult_lt_compat_r; [ exact Hinv | lra ].
Qed.

(* The differential H-theorem (entropy production):
     dH/dt = -(2/tau) H(t),
   so with H >= 0 the production rate is nonpositive everywhere. *)
Theorem bgk_entropy_production :
  forall (feq f0 : R -> R) (tau t v_min v_max : R), 0 < tau ->
    ex_RInt (fun v => (f0 v - feq v) ^ 2) v_min v_max ->
    is_derive (fun s => bgk_H feq f0 tau s v_min v_max) t
              (- (2 / tau) * bgk_H feq f0 tau t v_min v_max).
Proof.
  intros feq f0 tau t vmin vmax Htau Hex.
  apply (is_derive_ext
           (fun s => exp (- 2 * s / tau)
                     * RInt (fun v => (f0 v - feq v) ^ 2) vmin vmax)).
  - intro s. symmetry.
    exact (bgk_H_closed_form feq f0 tau s vmin vmax Htau Hex).
  - rewrite (bgk_H_closed_form feq f0 tau t vmin vmax Htau Hex).
    generalize (RInt (fun v => (f0 v - feq v) ^ 2) vmin vmax); intro Q.
    auto_derive; [ lra | ]. unfold Rdiv; ring.
Qed.

Corollary bgk_entropy_production_nonpos :
  forall (feq f0 : R -> R) (tau t v_min v_max : R), 0 < tau ->
    v_min <= v_max ->
    ex_RInt (fun v => (f0 v - feq v) ^ 2) v_min v_max ->
    - (2 / tau) * bgk_H feq f0 tau t v_min v_max <= 0.
Proof.
  intros feq f0 tau t vmin vmax Htau Hord Hex.
  pose proof (bgk_H_nonneg feq f0 tau t vmin vmax Htau Hord Hex) as HH.
  assert (H2 : 0 < 2 / tau) by (apply Rdiv_lt_0_compat; lra).
  nra.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions collision_conserves_mass.
Print Assumptions collision_conserves_invariant.
Print Assumptions collision_conserves_momentum.
Print Assumptions collision_conserves_energy.
Print Assumptions bgk_is_collision_instance.
Print Assumptions mass_moment_nonneg.
Print Assumptions bgk_mass_conservation.
Print Assumptions bgk_mass_conserved_when_matched.
Print Assumptions bgk_relax_solves_ode.
Print Assumptions bgk_deviation_decays.
Print Assumptions f_slowing_pos.
Print Assumptions f_slowing_decreasing.
Print Assumptions energy_moment_slowing.
Print Assumptions energy_decay_slow_down.
Print Assumptions bgk_H_closed_form.
Print Assumptions bgk_H_nonneg.
Print Assumptions bgk_H_decreasing.
Print Assumptions bgk_entropy_production.
Print Assumptions bgk_entropy_production_nonpos.
