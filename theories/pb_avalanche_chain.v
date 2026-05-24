(******************************************************************************)
(*                                                                            *)
(*     Time-integrated geometric chain                                        *)
(*                                                                            *)
(*     The all-generations multiplication M_total := sum_{n=0}^{infty} M^n.   *)
(*     For |M| < 1, this geometric series converges to 1 / (1 - M), giving   *)
(*     the absolute long-time integrated secondary-fusion contribution as     *)
(*                                                                            *)
(*       R_total = R_primary / (1 - M).                                       *)
(*                                                                            *)
(*     For M >= 1 the series diverges — the formal "avalanche" condition.    *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
From Coquelicot Require Import Coquelicot.

Open Scope R_scope.

(* ================================================================== *)
(* === Geometric chain sum === *)
(* ================================================================== *)

(* The total multiplication chain for |M| < 1 evaluates exactly to
   1 / (1 - M). Coquelicot's Series_geom gives this directly. *)
Theorem M_chain_total :
  forall M, Rabs M < 1 ->
    Series (fun n => M ^ n) = / (1 - M).
Proof. exact Series_geom. Qed.

(* For M in [0, 1) (the physical case), the chain converges with
   absolute multiplication R_primary / (1 - M). *)
Theorem chain_convergence :
  forall M, 0 <= M -> M < 1 ->
    is_series (fun n => M ^ n) (/ (1 - M)).
Proof.
  intros M HM_low HM_high.
  apply is_series_geom.
  apply Rabs_def1; lra.
Qed.

Theorem chain_sum_nonneg :
  forall M, 0 <= M -> M < 1 ->
    0 <= / (1 - M).
Proof.
  intros M HM_low HM_high.
  apply Rlt_le, Rinv_0_lt_compat. lra.
Qed.

(* Safety margin in terms of the total chain sum: when M = FoM_max,
   the chain sum is 1 / (1 - FoM_max), giving an explicit upper
   bound on the cumulative secondary-fusion contribution relative
   to the primary rate. *)
Definition chain_total (M : R) : R := / (1 - M).

Lemma chain_total_pos :
  forall M, M < 1 -> 0 < chain_total M.
Proof.
  intros M HM. unfold chain_total. apply Rinv_0_lt_compat. lra.
Qed.

Lemma chain_total_monotone :
  forall M1 M2, M1 < 1 -> M2 < 1 -> M1 <= M2 ->
    chain_total M1 <= chain_total M2.
Proof.
  intros M1 M2 H1 H2 H12. unfold chain_total.
  apply Rinv_le_contravar; [lra | lra].
Qed.

(* At the ConcreteSettlement bound (M = 3/100), the chain total
   evaluates to 100/97. *)
Lemma chain_total_at_concrete :
  chain_total (3 / 100) = 100 / 97.
Proof. unfold chain_total. field. Qed.

Lemma chain_total_concrete_bound :
  chain_total (3 / 100) <= 2.
Proof. rewrite chain_total_at_concrete. lra. Qed.

(* For the PhysicalSettlement bound (M <= 3/10^13), the chain total
   barely exceeds unity. *)
Lemma chain_total_at_physical :
  chain_total (3 / 10000000000000) =
  1 / (1 - 3 / 10000000000000).
Proof. unfold chain_total. field. Qed.

(* ================================================================== *)
(* === Avalanche divergence: M >= 1 case === *)
(* ================================================================== *)

(* For M >= 1, the geometric series diverges: no finite chain total. *)
Lemma chain_diverges_at_one :
  forall M, 1 <= M -> ~ ex_series (fun n => M ^ n).
Proof.
  intros M HM [l Hseries].
  (* Necessary condition for convergence: terms tend to zero. *)
  pose proof (ex_series_lim_0 (fun n => M ^ n)
                (ex_intro _ l Hseries)) as H0.
  (* M^n >= 1 for all n; combined with M^n -> 0, derive contradiction. *)
  assert (Hpow_ge_1 : forall n : nat, 1 <= M ^ n).
  { intro n. induction n as [| n IH].
    - simpl. lra.
    - simpl. apply Rle_trans with (M * 1); [lra |].
      apply Rmult_le_compat_l; lra. }
  pose proof (is_lim_seq_const 1) as Hconst.
  pose proof (is_lim_seq_le_loc (fun _ : nat => 1) (fun n => M ^ n) 1 0)
    as Hcmp.
  assert (Hle : Rbar_le 1 0).
  { apply Hcmp.
    - apply filter_forall. intros n. exact (Hpow_ge_1 n).
    - exact Hconst.
    - exact H0. }
  simpl in Hle. lra.
Qed.

(* ================================================================== *)
(* === Per-generation chain rates === *)
(* ================================================================== *)

(* The rate at generation n is M^n * R_primary. Concretely:
   - generation 0 = primary rate (R_primary)
   - generation 1 = secondary rate (M * R_primary)
   - generation 2 = tertiary rate (M^2 * R_primary)
   - generation 3 = quaternary rate (M^3 * R_primary)
   - ...
   In a chain that doesn't avalanche, each generation is strictly
   smaller than the previous, with ratio M < 1. *)
Definition R_generation (R_primary M : R) (n : nat) : R :=
  R_primary * M ^ n.

Lemma R_generation_zero : forall R_primary M, R_generation R_primary M 0 = R_primary.
Proof. intros. unfold R_generation. simpl. ring. Qed.

Lemma R_generation_succ :
  forall R_primary M n,
    R_generation R_primary M (S n) = M * R_generation R_primary M n.
Proof. intros. unfold R_generation. simpl. ring. Qed.

Definition R_secondary_rate (R_primary M : R) : R := R_generation R_primary M 1.
Definition R_tertiary_rate  (R_primary M : R) : R := R_generation R_primary M 2.
Definition R_quaternary_rate (R_primary M : R) : R := R_generation R_primary M 3.

Lemma R_secondary_rate_eq : forall R M,
  R_secondary_rate R M = M * R.
Proof. intros. unfold R_secondary_rate, R_generation. simpl. ring. Qed.

Lemma R_tertiary_rate_eq : forall R M,
  R_tertiary_rate R M = M * M * R.
Proof. intros. unfold R_tertiary_rate, R_generation. simpl. ring. Qed.

Lemma R_quaternary_rate_eq : forall R M,
  R_quaternary_rate R M = M * M * M * R.
Proof. intros. unfold R_quaternary_rate, R_generation. simpl. ring. Qed.

(* For 0 <= M < 1, each successive generation strictly decreases. *)
Lemma R_generation_decreasing :
  forall R_primary M n,
    0 < R_primary -> 0 <= M < 1 ->
    R_generation R_primary M (S n) <= R_generation R_primary M n.
Proof.
  intros R_primary M n HR [HM_lo HM_hi].
  rewrite R_generation_succ.
  unfold R_generation.
  pose proof (pow_le M n HM_lo) as Hpow_pos.
  pose proof (Rmult_le_pos R_primary (M ^ n)
                (Rlt_le _ _ HR) Hpow_pos) as Hprod_pos.
  nra.
Qed.

(* Generation-n rate goes to zero as n -> infty for M in [0, 1). *)
Lemma R_generation_lim :
  forall R_primary M,
    0 < R_primary -> Rabs M < 1 ->
    is_lim_seq (fun n => R_generation R_primary M n) 0.
Proof.
  intros R_primary M HR HM.
  unfold R_generation.
  pose proof (is_lim_seq_scal_l (fun n => M ^ n) R_primary (Finite 0)
                (is_lim_seq_geom M HM)) as Hs.
  simpl in Hs.
  replace 0 with (R_primary * 0) by ring.
  exact Hs.
Qed.

(* Sum of all generations: total chain converges and matches
   R_primary / (1 - M). *)
Theorem R_chain_total :
  forall R_primary M,
    0 <= M -> M < 1 ->
    is_series (fun n => R_generation R_primary M n) (R_primary / (1 - M)).
Proof.
  intros R_primary M HM_lo HM_hi.
  unfold R_generation.
  replace (R_primary / (1 - M)) with (R_primary * / (1 - M)).
  2: { unfold Rdiv. ring. }
  apply (is_series_scal_l R_primary (fun n => M ^ n)).
  exact (chain_convergence M HM_lo HM_hi).
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions M_chain_total.
Print Assumptions chain_convergence.
Print Assumptions chain_total_pos.
Print Assumptions chain_total_monotone.
Print Assumptions chain_total_at_concrete.
Print Assumptions chain_diverges_at_one.
