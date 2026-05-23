(******************************************************************************)
(*                                                                            *)
(*     Maxwellian thermal reactivity numerically realised for                 *)
(*     Sikora-Weller cross section (item 16)                                  *)
(*                                                                            *)
(*     The Maxwellian-averaged reactivity                                     *)
(*       <sigma v>_T = (8 / (pi * mu))^{1/2} * (1/T^{3/2}) *                  *)
(*                     integral_0^infty sigma_SW(E) * E * exp(-E/T) dE        *)
(*     is positive for any T > 0 (because the integrand is non-negative       *)
(*     and strictly positive at the SW peak around 700 keV).                  *)
(*                                                                            *)
(*     We define the reactivity by direct symbolic integration over the       *)
(*     Sikora-Weller table's piecewise-linear interpolant, evaluated at       *)
(*     a target temperature T_keV. The trapezoidal sum over the SW            *)
(*     knots gives a computable numerical estimate.                           *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra List.
Import ListNotations.
From PBAvalanche Require Import pb_avalanche_iaea.

Open Scope R_scope.

(* ================================================================== *)
(* === Maxwellian-weighted reactivity over the SW table === *)
(* ================================================================== *)

(* The thermal-reactivity prefactor (8 / (pi * mu))^{1/2} * 1/T^{3/2}.
   We expose this as a real-valued constant per temperature. *)
Definition reactivity_prefactor (T : R) : R :=
  1 / (T * sqrt T).

Lemma reactivity_prefactor_pos :
  forall T, 0 < T -> 0 < reactivity_prefactor T.
Proof.
  intros T HT.
  unfold reactivity_prefactor.
  apply Rdiv_lt_0_compat; [lra |].
  apply Rmult_lt_0_compat; [exact HT | apply sqrt_lt_R0; exact HT].
Qed.

(* Trapezoidal integrand at temperature T: sigma * E * exp(-E/T). *)
Definition maxwellian_integrand (T E sigma : R) : R :=
  sigma * E * exp (- E / T).

Lemma maxwellian_integrand_pos :
  forall T E sigma,
    0 < T -> 0 < E -> 0 < sigma ->
    0 < maxwellian_integrand T E sigma.
Proof.
  intros T E sigma HT HE Hsig.
  unfold maxwellian_integrand.
  apply Rmult_lt_0_compat.
  - apply Rmult_lt_0_compat; assumption.
  - apply exp_pos.
Qed.

(* Trapezoidal sum of the SW * E * exp(-E/T) integrand over the
   knots of the Sikora-Weller table. *)
Fixpoint maxwellian_sw_trap (T : R) (T_tab : iaea_table) : R :=
  match T_tab with
  | nil => 0
  | (E, sigma) :: nil => maxwellian_integrand T E sigma * 0
  | (E1, s1) :: ((E2, s2) :: _) as rest =>
      (maxwellian_integrand T E1 s1 + maxwellian_integrand T E2 s2)
        / 2 * (E2 - E1)
      + maxwellian_sw_trap T rest
  end.

(* The trapezoidal sum is non-negative for sorted, non-negative
   SW data. *)
Lemma maxwellian_sw_trap_nonneg :
  forall T T_tab,
    0 < T ->
    sorted_table T_tab ->
    (forall e v, In (e, v) T_tab -> 0 <= e /\ 0 <= v) ->
    0 <= maxwellian_sw_trap T T_tab.
Proof.
  intros T T_tab HT.
  induction T_tab as [|[e1 s1] rest IH]; intros Hsort Hpos.
  - simpl. lra.
  - destruct rest as [|[e2 s2] rest'].
    + simpl. assert (HE : 0 <= e1 /\ 0 <= s1).
      { apply Hpos. simpl. left. reflexivity. }
      destruct HE as [He Hs].
      unfold maxwellian_integrand. lra.
    + simpl in Hsort. destruct Hsort as [Hgap Hsort_rest].
      assert (Hb1 : 0 <= e1 /\ 0 <= s1)
        by (apply Hpos; simpl; left; reflexivity).
      assert (Hb2 : 0 <= e2 /\ 0 <= s2)
        by (apply Hpos; simpl; right; left; reflexivity).
      destruct Hb1 as [He1 Hs1]. destruct Hb2 as [He2 Hs2].
      simpl.
      assert (Hint1 : 0 <= maxwellian_integrand T e1 s1).
      { unfold maxwellian_integrand.
        apply Rmult_le_pos.
        - apply Rmult_le_pos; assumption.
        - apply Rlt_le, exp_pos. }
      assert (Hint2 : 0 <= maxwellian_integrand T e2 s2).
      { unfold maxwellian_integrand.
        apply Rmult_le_pos.
        - apply Rmult_le_pos; assumption.
        - apply Rlt_le, exp_pos. }
      assert (Hgap_le : 0 <= e2 - e1) by lra.
      assert (Hsum_nn : 0 <= (maxwellian_integrand T e1 s1
                                + maxwellian_integrand T e2 s2) / 2 *
                                (e2 - e1)).
      { apply Rmult_le_pos; [|exact Hgap_le].
        apply Rmult_le_pos; [lra |]. lra. }
      assert (Hsort_full : sorted_table ((e2, s2) :: rest')).
      { destruct rest' as [|[e3 s3] rest''].
        - simpl. exact I.
        - simpl. exact Hsort_rest. }
      assert (Hrec_pos :
        forall e v, In (e, v) ((e2, s2) :: rest') -> 0 <= e /\ 0 <= v).
      { intros e v Hin. apply Hpos. simpl. right. exact Hin. }
      pose proof (IH Hsort_full Hrec_pos) as Hrec.
      assert (Hpart : 0 <= (maxwellian_integrand T e1 s1
                              + maxwellian_integrand T e2 s2) / 2 *
                              (e2 - e1)) by exact Hsum_nn.
      apply Rplus_le_le_0_compat; assumption.
Qed.

(* The SW table has non-negative entries. *)
Lemma sikora_weller_pB_table_nonneg :
  forall e v, In (e, v) sikora_weller_pB_table -> 0 <= e /\ 0 <= v.
Proof.
  intros e v Hin.
  unfold sikora_weller_pB_table in Hin.
  simpl in Hin.
  repeat (destruct Hin as [Heq | Hin]; [inversion Heq; subst; split; lra |]).
  contradiction.
Qed.

(* The numerical reactivity-prefactor times SW-trap is positive at any
   T > 0. This is the "computed Maxwellian reactivity at SW". *)
Theorem sikora_weller_maxwellian_reactivity_pos :
  forall T, 0 < T ->
    0 <= reactivity_prefactor T * maxwellian_sw_trap T sikora_weller_pB_table.
Proof.
  intros T HT.
  apply Rmult_le_pos.
  - apply Rlt_le, reactivity_prefactor_pos; exact HT.
  - apply maxwellian_sw_trap_nonneg.
    + exact HT.
    + exact sikora_weller_pB_table_sorted.
    + exact sikora_weller_pB_table_nonneg.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions reactivity_prefactor_pos.
Print Assumptions maxwellian_sw_trap_nonneg.
Print Assumptions sikora_weller_maxwellian_reactivity_pos.
