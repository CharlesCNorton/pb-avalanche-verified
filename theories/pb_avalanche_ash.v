(******************************************************************************)
(*                                                                            *)
(*     Helium-ash transport with Z_eff raising (item 23)                      *)
(*                                                                            *)
(*     Extends the plasma state with an ash density n_ash (thermalised        *)
(*     helium nuclei) and redoes the Spitzer slowing-down time with the       *)
(*     ion-scattering Z_eff denominator                                       *)
(*                                                                            *)
(*       n_eff = n_p + Z_B^2 n_B + Z_alpha^2 n_ash.                           *)
(*                                                                            *)
(*     Ash accumulation raises n_eff, shortens tau_slow_alpha, and so         *)
(*     reduces the multiplication factor — a formal self-quenching            *)
(*     mechanism.                                                             *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra ZArith.
From PBAvalanche Require Import pb_avalanche.

Open Scope R_scope.

(* ================================================================== *)
(* === Ash-extended plasma state === *)
(* ================================================================== *)

(* Helium-ash density. *)

(* Alpha-particle nuclear charge (Z_alpha = 2 for helium-4). *)
Definition Z_alpha : R := 2.

Record PlasmaStateAsh : Type := mkPlasmaStateAsh {
  psa_n_p   : R;
  psa_n_B   : R;
  psa_n_ash : R;
  psa_T     : R;
  psa_B     : R;
  psa_pos_n_p   : 0 < psa_n_p;
  psa_pos_n_B   : 0 < psa_n_B;
  psa_pos_n_ash : 0 <= psa_n_ash;  (* ash can be zero initially *)
  psa_pos_T     : 0 < psa_T;
  psa_pos_B     : 0 < psa_B;
}.

(* The effective ion-scattering density including ash contribution. *)
Definition n_eff_with_ash (s : PlasmaStateAsh) : R :=
  psa_n_p s + Z_B * Z_B * psa_n_B s + Z_alpha * Z_alpha * psa_n_ash s.

Lemma n_eff_with_ash_pos :
  forall s, 0 < n_eff_with_ash s.
Proof.
  intros s. unfold n_eff_with_ash.
  pose proof (psa_pos_n_p s) as Hp.
  pose proof (psa_pos_n_B s) as HB.
  pose proof (psa_pos_n_ash s) as Hash.
  assert (HZB : 0 < Z_B * Z_B * psa_n_B s).
  { apply Rmult_lt_0_compat;
      [apply Rmult_lt_0_compat; unfold Z_B; lra | exact HB]. }
  assert (HZa : 0 <= Z_alpha * Z_alpha * psa_n_ash s).
  { apply Rmult_le_pos; [unfold Z_alpha; lra | exact Hash]. }
  lra.
Qed.

(* The Spitzer slowing-down time with ash correction. *)
Definition tau_slow_alpha_ash (Cspitzer : R) (s : PlasmaStateAsh) : R :=
  Cspitzer * psa_T s * sqrt (psa_T s) / n_eff_with_ash s.

Lemma tau_slow_alpha_ash_pos :
  forall Cspitzer s, 0 < Cspitzer ->
    0 < tau_slow_alpha_ash Cspitzer s.
Proof.
  intros Cspitzer s HC. unfold tau_slow_alpha_ash.
  pose proof (n_eff_with_ash_pos s) as Hpos.
  pose proof (psa_pos_T s) as HTpos.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat; assumption.
    + apply sqrt_lt_R0; exact HTpos.
  - apply Rinv_0_lt_compat; exact Hpos.
Qed.

(* ================================================================== *)
(* === Monotonicity in ash density === *)
(* ================================================================== *)

(* tau_slow_alpha_ash is decreasing in psa_n_ash. *)
Theorem tau_slow_alpha_ash_decreasing :
  forall Cspitzer
    (n_p n_B n_ash1 n_ash2 T B : R)
    (Hp_p : 0 < n_p) (Hp_B : 0 < n_B)
    (Hp_a1 : 0 <= n_ash1) (Hp_a2 : 0 <= n_ash2)
    (Hp_T : 0 < T) (Hp_B' : 0 < B),
    0 < Cspitzer ->
    n_ash1 <= n_ash2 ->
    tau_slow_alpha_ash Cspitzer
      (mkPlasmaStateAsh n_p n_B n_ash2 T B Hp_p Hp_B Hp_a2 Hp_T Hp_B') <=
    tau_slow_alpha_ash Cspitzer
      (mkPlasmaStateAsh n_p n_B n_ash1 T B Hp_p Hp_B Hp_a1 Hp_T Hp_B').
Proof.
  intros Cspitzer n_p n_B n_ash1 n_ash2 T B Hp_p Hp_B Hp_a1 Hp_a2 Hp_T Hp_B'
         HC Hash.
  unfold tau_slow_alpha_ash, n_eff_with_ash. simpl.
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos.
    + apply Rmult_le_pos; [apply Rlt_le, HC | apply Rlt_le, Hp_T].
    + apply sqrt_pos.
  - apply Rinv_le_contravar.
    + apply Rplus_lt_le_0_compat.
      * apply Rplus_lt_0_compat; [exact Hp_p |].
        apply Rmult_lt_0_compat; [unfold Z_B; lra | exact Hp_B].
      * apply Rmult_le_pos; [unfold Z_alpha; nra | exact Hp_a1].
    + assert (Hzalpha : 0 <= Z_alpha * Z_alpha)
        by (unfold Z_alpha; nra).
      assert (Hineq : Z_alpha * Z_alpha * n_ash1 <= Z_alpha * Z_alpha * n_ash2)
        by (apply Rmult_le_compat_l; assumption).
      lra.
Qed.

(* ================================================================== *)
(* === Multiplication factor decreases with ash === *)
(* ================================================================== *)

(* Given an "abstract" alpha-weighted velocity integral I (positive)
   and the kinetic factorization M = 3 * n_B * tau * I, the M values
   at two different ash densities (with everything else equal)
   satisfy M(n_ash_high) <= M(n_ash_low). This is the formal
   self-quenching content. *)

Definition M_ash (Cspitzer I : R) (s : PlasmaStateAsh) : R :=
  3 * psa_n_B s * tau_slow_alpha_ash Cspitzer s * I.

Theorem M_ash_decreasing :
  forall Cspitzer I
    (n_p n_B n_ash1 n_ash2 T B : R)
    (Hp_p : 0 < n_p) (Hp_B : 0 < n_B)
    (Hp_a1 : 0 <= n_ash1) (Hp_a2 : 0 <= n_ash2)
    (Hp_T : 0 < T) (Hp_B' : 0 < B),
    0 < Cspitzer -> 0 <= I -> n_ash1 <= n_ash2 ->
    M_ash Cspitzer I
      (mkPlasmaStateAsh n_p n_B n_ash2 T B Hp_p Hp_B Hp_a2 Hp_T Hp_B') <=
    M_ash Cspitzer I
      (mkPlasmaStateAsh n_p n_B n_ash1 T B Hp_p Hp_B Hp_a1 Hp_T Hp_B').
Proof.
  intros Cspitzer I n_p n_B n_ash1 n_ash2 T B Hp_p Hp_B Hp_a1 Hp_a2 Hp_T Hp_B'
         HC HI Hash.
  unfold M_ash. simpl.
  apply Rmult_le_compat_r; [exact HI |].
  apply Rmult_le_compat_l.
  - apply Rmult_le_pos.
    + lra.
    + apply Rlt_le, Hp_B.
  - apply (tau_slow_alpha_ash_decreasing Cspitzer n_p n_B n_ash1 n_ash2 T B
             Hp_p Hp_B Hp_a1 Hp_a2 Hp_T Hp_B'); assumption.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions n_eff_with_ash_pos.
Print Assumptions tau_slow_alpha_ash_pos.
Print Assumptions tau_slow_alpha_ash_decreasing.
Print Assumptions M_ash_decreasing.
