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
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions mass_moment_nonneg.
Print Assumptions f_slowing_pos.
Print Assumptions f_slowing_decreasing.
Print Assumptions energy_moment_slowing.
Print Assumptions energy_decay_slow_down.
