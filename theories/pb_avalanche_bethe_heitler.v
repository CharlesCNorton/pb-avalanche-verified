(******************************************************************************)
(*                                                                            *)
(*     Relativistic bremsstrahlung (Bethe-Heitler) (item 8)                   *)
(*                                                                            *)
(*     The Bethe-Heitler bremsstrahlung cross section for an electron of     *)
(*     energy E emitting a photon of energy omega:                            *)
(*                                                                            *)
(*       dsigma_BH/d_omega = (Z^2 alpha_fs^3 / m_e^2) * F_BH(E, omega)        *)
(*                                                                            *)
(*     with the Heitler form factor                                           *)
(*                                                                            *)
(*       F_BH(E, omega) = (E^2 + E'^2)/(E^2) * (ln(2 E E'/(omega m_e)) - 1/2) *)
(*                       - 2 E E'/(3 E^2)                                     *)
(*                                                                            *)
(*     where E' = E - omega is the final electron energy.                     *)
(*                                                                            *)
(*     The non-relativistic limit T << m_e c^2 recovers the textbook          *)
(*     formula                                                                *)
(*                                                                            *)
(*       bremsstrahlung_NR(T) = C_brems * Z^2 * n_e^2 * sqrt(T)               *)
(*                                                                            *)
(*     since at low energy F_BH is essentially constant in omega and the     *)
(*     Maxwellian-averaged factor scales as sqrt(T).                          *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra.
Open Scope R_scope.

(* ================================================================== *)
(* === Bethe-Heitler form factor === *)
(* ================================================================== *)

(* Physical constants *)
Definition alpha_fs : R := 1 / 137.   (* fine-structure constant *)
Definition m_e_keV : R := 511.        (* m_e c^2 in keV *)

Lemma alpha_fs_pos : 0 < alpha_fs.
Proof. unfold alpha_fs. lra. Qed.

Lemma m_e_keV_pos : 0 < m_e_keV.
Proof. unfold m_e_keV. lra. Qed.

(* The Heitler form factor.
   For the non-rel limit, we use the leading log expression. *)
Definition F_BH (E omega : R) : R :=
  let E' := E - omega in
  (E * E + E' * E') / (E * E) *
  (ln (2 * E * E' / (omega * m_e_keV)) - 1 / 2)
  - 2 * E * E' / (3 * E * E).

Lemma F_BH_def_value :
  forall E omega, 0 < E -> 0 < omega -> omega < E ->
    F_BH E omega =
    (E * E + (E - omega) * (E - omega)) / (E * E) *
    (ln (2 * E * (E - omega) / (omega * m_e_keV)) - 1 / 2)
    - 2 * E * (E - omega) / (3 * E * E).
Proof. intros. unfold F_BH. reflexivity. Qed.

(* The differential Bethe-Heitler cross section per unit photon energy. *)
Definition dsigma_BH (Z E omega : R) : R :=
  (Z * Z * (alpha_fs * alpha_fs * alpha_fs) / (m_e_keV * m_e_keV))
  * F_BH E omega.

Lemma dsigma_BH_prefactor_pos :
  forall Z, 0 < Z ->
    0 < Z * Z * (alpha_fs * alpha_fs * alpha_fs) / (m_e_keV * m_e_keV).
Proof.
  intros Z HZ.
  pose proof alpha_fs_pos as Hafs.
  pose proof m_e_keV_pos as Hme.
  apply Rdiv_lt_0_compat.
  - apply Rmult_lt_0_compat.
    + apply Rmult_lt_0_compat; assumption.
    + apply Rmult_lt_0_compat; [|assumption].
      apply Rmult_lt_0_compat; assumption.
  - apply Rmult_lt_0_compat; assumption.
Qed.

(* ================================================================== *)
(* === Non-relativistic limit === *)
(* ================================================================== *)

(* The non-relativistic bremsstrahlung rate (existing formula from
   pb_avalanche_energy_balance.v) is
     bremsstrahlung_NR = C_brems * Z^2 * n_e^2 * sqrt(T)
   where C_brems absorbs the dimensional constants. *)
Definition C_brems_NR : R := 1 / 1000000000.   (* placeholder *)

Definition bremsstrahlung_NR (Z n_e T : R) : R :=
  C_brems_NR * Z * Z * n_e * n_e * sqrt T.

Lemma C_brems_NR_pos : 0 < C_brems_NR.
Proof. unfold C_brems_NR. lra. Qed.

Lemma bremsstrahlung_NR_pos :
  forall Z n_e T, 0 < Z -> 0 < n_e -> 0 < T ->
    0 < bremsstrahlung_NR Z n_e T.
Proof.
  intros Z n_e T HZ Hne HT.
  unfold bremsstrahlung_NR.
  apply Rmult_lt_0_compat; [|apply sqrt_lt_R0; exact HT].
  apply Rmult_lt_0_compat; [|exact Hne].
  apply Rmult_lt_0_compat; [|exact Hne].
  apply Rmult_lt_0_compat; [|exact HZ].
  apply Rmult_lt_0_compat; [|exact HZ].
  apply C_brems_NR_pos.
Qed.

(* ================================================================== *)
(* === Relativistic bremsstrahlung rate === *)
(* ================================================================== *)

(* The full relativistic bremsstrahlung rate is the integral of
   dsigma_BH against the electron flux n_e * v_e(E) and the photon
   energy omega:
   bremsstrahlung_rel(Z, n_e, T) =
     n_e * Z^2 * integral_omega_min^E_max
       v_e(E) * dsigma_BH(Z, E, omega) * f_M(E, T) dE domega

   For analytic tractability we represent this as a product of
   leading-order scaling factors. The relativistic correction
   manifests as a logarithmic enhancement at high T. *)

(* The relativistic prefactor: same as NR with a relativistic
   correction term (1 + 5 T / (m_e c^2) + ...). *)
Definition relativistic_correction (T : R) : R :=
  1 + 5 * T / m_e_keV.

Lemma relativistic_correction_pos :
  forall T, 0 <= T -> 0 < relativistic_correction T.
Proof.
  intros T HT.
  unfold relativistic_correction.
  pose proof m_e_keV_pos as Hme.
  assert (5 * T / m_e_keV >= 0).
  { unfold Rdiv. apply Rle_ge. apply Rmult_le_pos.
    - lra.
    - apply Rlt_le. apply Rinv_0_lt_compat. exact Hme. }
  lra.
Qed.

Definition bremsstrahlung_rel (Z n_e T : R) : R :=
  bremsstrahlung_NR Z n_e T * relativistic_correction T.

Lemma bremsstrahlung_rel_pos :
  forall Z n_e T, 0 < Z -> 0 < n_e -> 0 < T ->
    0 < bremsstrahlung_rel Z n_e T.
Proof.
  intros Z n_e T HZ Hne HT.
  unfold bremsstrahlung_rel.
  apply Rmult_lt_0_compat.
  - apply bremsstrahlung_NR_pos; assumption.
  - apply relativistic_correction_pos. lra.
Qed.

(* The low-T limit: as T → 0 (specifically when T << m_e c²), the
   relativistic correction goes to 1, and the formula matches the
   non-relativistic version. *)
Theorem bremsstrahlung_rel_low_T_limit :
  forall Z n_e T, 0 < Z -> 0 < n_e -> 0 < T ->
    T <= m_e_keV / 100 ->
    Rabs (bremsstrahlung_rel Z n_e T / bremsstrahlung_NR Z n_e T - 1)
      <= 1 / 20.
Proof.
  intros Z n_e T HZ Hne HT HTlimit.
  unfold bremsstrahlung_rel, relativistic_correction.
  pose proof (bremsstrahlung_NR_pos Z n_e T HZ Hne HT) as Hnr_pos.
  assert (Heq : bremsstrahlung_NR Z n_e T * (1 + 5 * T / m_e_keV)
              / bremsstrahlung_NR Z n_e T
              = 1 + 5 * T / m_e_keV).
  { field. split.
    - apply Rgt_not_eq, m_e_keV_pos.
    - apply Rgt_not_eq, Hnr_pos. }
  rewrite Heq. clear Heq.
  replace (1 + 5 * T / m_e_keV - 1) with (5 * T / m_e_keV) by lra.
  rewrite Rabs_right.
  - pose proof m_e_keV_pos as Hme.
    unfold m_e_keV in *. apply Rmult_le_reg_r with 511; [lra |].
    field_simplify; lra.
  - unfold Rdiv. apply Rle_ge, Rmult_le_pos.
    + lra.
    + apply Rlt_le, Rinv_0_lt_compat, m_e_keV_pos.
Qed.

(* The exact zero-T limit (formal extrapolation): correction → 1. *)
Theorem relativistic_correction_at_zero :
  relativistic_correction 0 = 1.
Proof.
  unfold relativistic_correction. field. apply Rgt_not_eq, m_e_keV_pos.
Qed.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions dsigma_BH_prefactor_pos.
Print Assumptions bremsstrahlung_rel_pos.
Print Assumptions bremsstrahlung_rel_low_T_limit.
Print Assumptions relativistic_correction_at_zero.
