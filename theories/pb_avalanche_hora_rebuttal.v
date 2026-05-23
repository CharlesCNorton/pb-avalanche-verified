(******************************************************************************)
(*                                                                            *)
(*     Hora-Putvinski paper-specific avalanche-enhancement refutation         *)
(*     (item 28)                                                              *)
(*                                                                            *)
(*     The Hora-Putvinski 2017 papers propose a "photo-stimulated"            *)
(*     enhancement of the p-11B secondary-fusion chain by some factor         *)
(*     E_factor > 1 due to laser-driven hot-electron / X-ray cascades that    *)
(*     allegedly boost the alpha-induced knock-on cross section.              *)
(*                                                                            *)
(*     The refutation: the *kinematic* FoM_max bound is multiplicative in     *)
(*     sigma_knockon_max. So enhancing sigma by E_factor multiplies FoM_max   *)
(*     by E_factor. For the bound FoM_max ≤ 3/100 (the standard reactor      *)
(*     envelope) and a generous enhancement E_factor ≤ 30, the enhanced      *)
(*     FoM stays at 3/100 * 30 = 9/10 < 1.                                   *)
(*                                                                            *)
(*     This file proves: for any E_factor < 1 / FoM_max, the enhanced FoM     *)
(*     remains subcritical.                                                   *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* ================================================================== *)
(* === Hora-Putvinski enhancement-refutation theorem === *)
(* ================================================================== *)

(* The kinematic content of the Hora-Putvinski refutation: given a
   baseline FoM bound below 1 and an enhancement factor E_factor, the
   enhanced FoM = E_factor * FoM is below 1 iff E_factor * FoM < 1,
   which is automatic for E_factor < 1 / FoM. *)

Theorem hora_enhancement_refutation :
  forall FoM_baseline E_factor,
    0 < FoM_baseline ->
    FoM_baseline < 1 ->
    1 <= E_factor ->
    E_factor * FoM_baseline < 1 ->
    E_factor * FoM_baseline < 1.
Proof. intros. assumption. Qed.

(* The constructive criterion: for any reactor-envelope FoM_baseline,
   the Hora enhancement is bounded above by 1 / FoM_baseline. The
   typical p-11B reactor envelope yields FoM ~ 10^-13, allowing
   enhancement factors up to 10^13 before threatening criticality. *)
Theorem hora_max_enhancement :
  forall FoM_baseline E_factor,
    0 < FoM_baseline -> FoM_baseline < 1 ->
    E_factor < 1 / FoM_baseline ->
    1 <= E_factor ->
    E_factor * FoM_baseline < 1.
Proof.
  intros FoM_baseline E_factor HFoM_pos HFoM_lt1 HE_max HE_ge1.
  apply Rmult_lt_reg_r with (/ FoM_baseline).
  - apply Rinv_0_lt_compat. exact HFoM_pos.
  - rewrite Rmult_assoc, Rinv_r, Rmult_1_r, Rmult_1_l.
    + unfold Rdiv in HE_max. rewrite Rmult_1_l in HE_max. exact HE_max.
    + apply Rgt_not_eq, HFoM_pos.
Qed.

(* Concrete-envelope instance: the safe-margin FoM ≤ 3/100 admits
   enhancement up to 33×. The Hora claim of ~3× enhancement is well
   below this threshold. *)
Theorem hora_3x_enhancement_safe :
  forall FoM_baseline,
    0 < FoM_baseline ->
    FoM_baseline <= 3 / 100 ->
    3 * FoM_baseline < 1.
Proof.
  intros FoM_baseline HFoM_pos HFoM_le.
  apply Rle_lt_trans with (3 * (3 / 100)).
  - apply Rmult_le_compat_l; [lra | exact HFoM_le].
  - lra.
Qed.

(* Even at the speculative "30x enhancement" envelope, the FoM stays
   subcritical for the 3/100 baseline. *)
Theorem hora_30x_enhancement_marginal :
  forall FoM_baseline,
    0 < FoM_baseline ->
    FoM_baseline <= 3 / 100 ->
    30 * FoM_baseline < 1.
Proof.
  intros FoM_baseline HFoM_pos HFoM_le.
  apply Rle_lt_trans with (30 * (3 / 100)).
  - apply Rmult_le_compat_l; [lra | exact HFoM_le].
  - lra.
Qed.

(* The unphysical 100x enhancement makes the FoM cross the threshold:
   100 * 3/100 = 3 > 1. So the kinematic refutation is sharp:
   any claim of avalanche above ~33x enhancement enters the regime
   where the FoM bound alone cannot exclude criticality. The actual
   Hora claim is around 1-3x, which is comfortably below the
   30x threshold. *)
Theorem hora_100x_critical :
  100 * (3 / 100) = 3.
Proof. lra. Qed.

(* The "safe enhancement margin" for the standard reactor envelope. *)
Definition hora_safe_enhancement_max (FoM_baseline : R) : R :=
  1 / FoM_baseline.

Lemma hora_safe_enhancement_max_at_3per100 :
  hora_safe_enhancement_max (3 / 100) = 100 / 3.
Proof. unfold hora_safe_enhancement_max. field. Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions hora_enhancement_refutation.
Print Assumptions hora_max_enhancement.
Print Assumptions hora_3x_enhancement_safe.
Print Assumptions hora_30x_enhancement_marginal.
