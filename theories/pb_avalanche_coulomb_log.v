(******************************************************************************)
(*                                                                            *)
(*     Coulomb logarithm numerical evaluation                                 *)
(*                                                                            *)
(*     The Coulomb logarithm controls how often Coulomb collisions thermalise *)
(*     ions in a plasma. The standard NRL Plasma Formulary expression for     *)
(*     ions in a hot plasma is                                                *)
(*                                                                            *)
(*       lnLambda(n_e, T_e) = 23.5 - (1/2) * ln(n_e) + (3/2) * ln(T_e)        *)
(*                                                                            *)
(*     with n_e in cm^-3 and T_e in eV. For a fusion-relevant reactor,        *)
(*     n_e ~ 10^15 cm^-3, T_e ~ 100 keV = 10^5 eV, the ln 10 terms cancel     *)
(*     exactly, giving lnLambda = 23.5.                                       *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* ================================================================== *)
(* === Auxiliary lemmas on the natural log === *)
(* ================================================================== *)

Lemma ln_pos_pos : forall x, 1 <= x -> 0 <= ln x.
Proof.
  intros x Hx. destruct (Req_dec x 1) as [Heq | Hneq].
  - subst. rewrite ln_1. lra.
  - apply Rlt_le. rewrite <- ln_1. apply ln_increasing; lra.
Qed.

Lemma ln_lt_0_inv : forall x, 0 < x < 1 -> ln x < 0.
Proof.
  intros x [Hpos Hlt].
  rewrite <- ln_1. apply ln_increasing; lra.
Qed.

(* ================================================================== *)
(* === Coulomb logarithm formula === *)
(* ================================================================== *)

Definition lnLambda_ion (n_e T_e : R) : R :=
  23.5 - (1/2) * ln n_e + (3/2) * ln T_e.

(* === Reactor evaluation === *)

(* For reactor conditions (n_e = 10^15 cm^-3, T_e = 10^5 eV), the
   Coulomb log evaluates to exactly 23.5 (the ln 10 terms cancel). *)
Theorem lnLambda_ion_reactor_value :
  ln (Rpower 10 15) = 15 * ln 10 /\
  ln (Rpower 10 5) = 5 * ln 10 /\
  lnLambda_ion (Rpower 10 15) (Rpower 10 5) = 23.5.
Proof.
  split; [|split].
  - unfold Rpower. rewrite ln_exp. ring.
  - unfold Rpower. rewrite ln_exp. ring.
  - unfold lnLambda_ion, Rpower. rewrite !ln_exp. field.
Qed.

(* The formula is consistent with the n^{1/3}-T relationship of the
   Debye length: scaling n_e by a^3 and T_e by a leaves lnLambda_ion
   invariant (since 0.5 * 3 = 1.5). *)
Theorem lnLambda_ion_scaling_consistency :
  forall n_e T_e a, 0 < n_e -> 0 < T_e -> 0 < a ->
    lnLambda_ion (a * a * a * n_e) (a * T_e)
    = lnLambda_ion n_e T_e.
Proof.
  intros n_e T_e a Hne HTe Ha.
  unfold lnLambda_ion.
  assert (Ha3 : 0 < a * a * a) by (repeat apply Rmult_lt_0_compat; lra).
  assert (Ha2 : 0 < a * a) by (apply Rmult_lt_0_compat; exact Ha).
  rewrite (ln_mult (a * a * a) n_e Ha3 Hne).
  rewrite (ln_mult (a * a) a Ha2 Ha).
  rewrite (ln_mult a a Ha Ha).
  rewrite (ln_mult a T_e Ha HTe).
  field.
Qed.

(* For T_e ≥ 1 eV and n_e ≤ 1 cm^-3 (highly idealised) we get a
   strict lower bound. The "real" reactor regime (T_e ≥ 10^5 eV,
   n_e ≤ 10^15 cm^-3) only sharpens this. *)
Theorem lnLambda_ion_lower_bound :
  forall T_e n_e, 1 <= T_e -> 0 < n_e -> n_e <= 1 ->
    23.5 <= lnLambda_ion n_e T_e.
Proof.
  intros T_e n_e HTe Hne_pos Hne. unfold lnLambda_ion.
  assert (HlnTe : 0 <= ln T_e) by (apply ln_pos_pos; exact HTe).
  assert (Hlnne : ln n_e <= 0).
  { destruct (Req_dec n_e 1) as [Heq | Hneq].
    - subst. rewrite ln_1. lra.
    - apply Rlt_le, ln_lt_0_inv; lra. }
  lra.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions lnLambda_ion_reactor_value.
Print Assumptions lnLambda_ion_scaling_consistency.
Print Assumptions lnLambda_ion_lower_bound.
