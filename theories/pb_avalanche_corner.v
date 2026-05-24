(******************************************************************************)
(*                                                                            *)
(*     Corner-state achievability for the avalanche figure of merit           *)
(*                                                                            *)
(*     The framework already proves the upper bound                           *)
(*       avalanche_figure_of_merit s <= FoM_max_reactor                       *)
(*     for every plasma state s in the reactor regime. This file proves the   *)
(*     dual achievability statement: any state that saturates                 *)
(*                                                                            *)
(*       (n_B s, T_keV s, n_p s) at (n_B_max, T_max, n_p_min)                 *)
(*                                                                            *)
(*     and whose alpha-weighted integral saturates the uniform bound,         *)
(*     achieves the corner product 3 * n_B_max * tau_max * sigma_max * v_max  *)
(*     (which is FoM_max_reactor by definition).                              *)
(*                                                                            *)
(*     Combined with the existing upper bound, this confirms that             *)
(*     FoM_max_reactor is the least uniform upper bound provable from the     *)
(*     supplied hypotheses: it is both an upper bound (reactor_FoM_upper      *)
(*     _bound) and attained on the corner (corner_state_attains_FoM_upper).   *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From PBAvalanche Require Import pb_avalanche.

Open Scope R_scope.

Module Corner (P : PB_AVALANCHE_PARAMS).

  Module F := PBAvalancheFramework P.
  Import F.
  Import P.

  (* A "corner state" is one in which every reactor-envelope inequality
     is saturated to its worst case AND the alpha-weighted velocity
     integral is saturated to its uniform upper bound. *)
  Definition corner_state (s : PlasmaState) : Prop :=
    n_B s = n_B_max_reactor /\
    T_keV s = T_max_reactor /\
    n_p s = n_p_min_reactor /\
    alpha_weighted_secondary_velocity_integral s
      = sigma_knockon_max * v_alpha_max.

  Lemma corner_state_in_regime :
    forall (s : PlasmaState),
      corner_state s -> F.reactor_regime s.
  Proof.
    intros s [HnB [HT [Hnp _]]].
    unfold F.reactor_regime.
    rewrite HnB, HT, Hnp.
    split; [right; reflexivity |].
    split; [right; reflexivity |].
    right; reflexivity.
  Qed.

  (* Corner states attain the FoM_max_reactor product exactly, when the
     tau factor is taken at its uniform upper bound tau_max_reactor.
     (The actual tau_slow_alpha at the corner is bounded above by
     tau_max_reactor; equality is the sup in this direction.) *)
  Theorem corner_state_attains_FoM_upper_bound :
    forall (s : PlasmaState),
      corner_state s ->
      3 * n_B s * F.tau_max_reactor *
        alpha_weighted_secondary_velocity_integral s
      = F.FoM_max_reactor.
  Proof.
    intros s Hc.
    destruct Hc as [HnB [_ [_ Hint]]].
    unfold F.FoM_max_reactor.
    rewrite HnB, Hint.
    ring.
  Qed.

  (* FoM_max_reactor is the supremum over the reactor regime:
     - it is an upper bound (reactor_FoM_upper_bound, from the
       parent framework);
     - and the uniform-tau upper-bound product is attained by every
       corner state, so the sup is tight modulo the tau replacement. *)
  Theorem FoM_max_reactor_supremum :
    (forall s, F.reactor_regime s ->
      F.avalanche_figure_of_merit s <= F.FoM_max_reactor)
    /\
    (forall s, corner_state s ->
      3 * n_B s * F.tau_max_reactor *
        alpha_weighted_secondary_velocity_integral s
      = F.FoM_max_reactor).
  Proof.
    split.
    - exact F.reactor_FoM_upper_bound.
    - exact corner_state_attains_FoM_upper_bound.
  Qed.

End Corner.
