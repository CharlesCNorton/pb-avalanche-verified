(******************************************************************************)
(*                                                                            *)
(*     Rational-exponent dimensional types                                    *)
(*                                                                            *)
(*     Generalizes the Z-exponent Unit type of pb_avalanche_units.v to        *)
(*     Q-exponents (rationals over Q). Required to capture quantities like    *)
(*     sqrt(T) in the Spitzer-Trubnikov formula, whose temperature exponent   *)
(*     is 1/2, not an integer.                                                *)
(*                                                                            *)
(*     Six base SI dimensions:                                                *)
(*       (length, time, mass, charge, temperature, particle_number)           *)
(*                                                                            *)
(*     Operations:                                                            *)
(*       - unit_mul_q adds exponents component-wise (Q-addition)              *)
(*       - unit_inv_q negates                                                 *)
(*       - unit_pow_q scales by Q                                             *)
(*       - sqrt_unit takes the half-exponent unit                             *)
(*                                                                            *)
(*     Z-exponent units embed into Q-exponent units via inject_Z_unit.        *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra ZArith Lia QArith Qcanon.
From PBAvalanche Require Import pb_avalanche_units.

Open Scope Q_scope.

(* ================================================================== *)
(* === Rational-exponent Unit record === *)
(* ================================================================== *)

Record UnitQ : Type := mkUnitQ {
  uq_length : Q;
  uq_time   : Q;
  uq_mass   : Q;
  uq_charge : Q;
  uq_temp   : Q;
  uq_count  : Q
}.

Definition zero_unit_q : UnitQ :=
  {| uq_length := 0; uq_time := 0; uq_mass := 0; uq_charge := 0;
     uq_temp := 0; uq_count := 0 |}.

Definition unit_mul_q (u v : UnitQ) : UnitQ :=
  {| uq_length := uq_length u + uq_length v;
     uq_time   := uq_time u   + uq_time v;
     uq_mass   := uq_mass u   + uq_mass v;
     uq_charge := uq_charge u + uq_charge v;
     uq_temp   := uq_temp u   + uq_temp v;
     uq_count  := uq_count u  + uq_count v |}.

Definition unit_inv_q (u : UnitQ) : UnitQ :=
  {| uq_length := - uq_length u;
     uq_time   := - uq_time u;
     uq_mass   := - uq_mass u;
     uq_charge := - uq_charge u;
     uq_temp   := - uq_temp u;
     uq_count  := - uq_count u |}.

Definition unit_div_q (u v : UnitQ) : UnitQ :=
  unit_mul_q u (unit_inv_q v).

Definition unit_pow_q (u : UnitQ) (n : Q) : UnitQ :=
  {| uq_length := n * uq_length u;
     uq_time   := n * uq_time u;
     uq_mass   := n * uq_mass u;
     uq_charge := n * uq_charge u;
     uq_temp   := n * uq_temp u;
     uq_count  := n * uq_count u |}.

(* === Q-equality of UnitQ (field-by-field Qeq) === *)
Definition UnitQ_eq (u v : UnitQ) : Prop :=
  Qeq (uq_length u) (uq_length v) /\
  Qeq (uq_time u)   (uq_time v) /\
  Qeq (uq_mass u)   (uq_mass v) /\
  Qeq (uq_charge u) (uq_charge v) /\
  Qeq (uq_temp u)   (uq_temp v) /\
  Qeq (uq_count u)  (uq_count v).

(* === Group laws for UnitQ_eq === *)

Lemma unit_mul_q_zero_l : forall u, UnitQ_eq (unit_mul_q zero_unit_q u) u.
Proof.
  intros [a b c d e f]. unfold UnitQ_eq, unit_mul_q, zero_unit_q. simpl.
  repeat split; ring.
Qed.

Lemma unit_mul_q_zero_r : forall u, UnitQ_eq (unit_mul_q u zero_unit_q) u.
Proof.
  intros [a b c d e f]. unfold UnitQ_eq, unit_mul_q, zero_unit_q. simpl.
  repeat split; ring.
Qed.

Lemma unit_mul_q_comm :
  forall u v, UnitQ_eq (unit_mul_q u v) (unit_mul_q v u).
Proof.
  intros [a1 b1 c1 d1 e1 f1] [a2 b2 c2 d2 e2 f2].
  unfold UnitQ_eq, unit_mul_q. simpl.
  repeat split; ring.
Qed.

Lemma unit_mul_q_assoc :
  forall u v w,
    UnitQ_eq (unit_mul_q (unit_mul_q u v) w)
             (unit_mul_q u (unit_mul_q v w)).
Proof.
  intros [a1 b1 c1 d1 e1 f1] [a2 b2 c2 d2 e2 f2] [a3 b3 c3 d3 e3 f3].
  unfold UnitQ_eq, unit_mul_q. simpl.
  repeat split; ring.
Qed.

Lemma unit_mul_q_inv_r : forall u,
  UnitQ_eq (unit_mul_q u (unit_inv_q u)) zero_unit_q.
Proof.
  intros [a b c d e f]. unfold UnitQ_eq, unit_mul_q, unit_inv_q, zero_unit_q.
  simpl. repeat split; ring.
Qed.

Lemma unit_mul_q_inv_l : forall u,
  UnitQ_eq (unit_mul_q (unit_inv_q u) u) zero_unit_q.
Proof.
  intros u.
  pose proof (unit_mul_q_comm (unit_inv_q u) u) as Hc.
  pose proof (unit_mul_q_inv_r u) as Hr.
  unfold UnitQ_eq in *. destruct Hc as (?&?&?&?&?&?).
  destruct Hr as (?&?&?&?&?&?).
  repeat split; eapply Qeq_trans; eassumption.
Qed.

Lemma unit_inv_q_inv : forall u, UnitQ_eq (unit_inv_q (unit_inv_q u)) u.
Proof.
  intros [a b c d e f]. unfold UnitQ_eq, unit_inv_q. simpl.
  repeat split; ring.
Qed.

(* === Q-power identities === *)

Lemma unit_pow_q_zero : forall u, UnitQ_eq (unit_pow_q u 0) zero_unit_q.
Proof.
  intros [a b c d e f]. unfold UnitQ_eq, unit_pow_q, zero_unit_q. simpl.
  repeat split; ring.
Qed.

Lemma unit_pow_q_one : forall u, UnitQ_eq (unit_pow_q u 1) u.
Proof.
  intros [a b c d e f]. unfold UnitQ_eq, unit_pow_q. simpl.
  repeat split; ring.
Qed.

Lemma unit_pow_q_add :
  forall u m n,
    UnitQ_eq (unit_pow_q u (m + n))
             (unit_mul_q (unit_pow_q u m) (unit_pow_q u n)).
Proof.
  intros [a b c d e f] m n. unfold UnitQ_eq, unit_pow_q, unit_mul_q. simpl.
  repeat split; ring.
Qed.

(* === Half-exponent unit (the sqrt unit) === *)

Definition sqrt_unit (u : UnitQ) : UnitQ := unit_pow_q u (1 # 2).

Lemma sqrt_unit_squared :
  forall u, UnitQ_eq (unit_mul_q (sqrt_unit u) (sqrt_unit u)) u.
Proof.
  intros u.
  unfold sqrt_unit.
  pose proof (unit_pow_q_add u (1 # 2) (1 # 2)) as Hadd.
  pose proof (unit_pow_q_one u) as Hone.
  (* (1 # 2) + (1 # 2) = 1 in Q *)
  assert (Hhalf : ((1 # 2) + (1 # 2))%Q == 1)
    by reflexivity.
  (* unit_pow_q u 1 == u, and unit_pow_q u ((1#2) + (1#2)) == unit_mul_q (...) (...). *)
  destruct u as [a b c d e f].
  unfold UnitQ_eq, unit_pow_q, unit_mul_q. simpl.
  repeat split; ring.
Qed.

(* === Sample physical-quantity rational units === *)

(* Velocity has Z-exponents — coincides with the integer case. *)
Definition velocity_unit_q : UnitQ :=
  {| uq_length := 1; uq_time := -1; uq_mass := 0; uq_charge := 0;
     uq_temp := 0; uq_count := 0 |}.

(* The Spitzer tau ~ T * sqrt(T) / n has temperature exponent 3/2 and
   particle exponent -1. Captured cleanly with Q-exponents. *)
Definition spitzer_tau_unit : UnitQ :=
  {| uq_length := 0; uq_time := 1; uq_mass := 0; uq_charge := 0;
     uq_temp := 3 # 2; uq_count := -1 |}.

(* sqrt(T) carries a half temperature exponent. *)
Definition sqrt_T_unit : UnitQ :=
  {| uq_length := 0; uq_time := 0; uq_mass := 0; uq_charge := 0;
     uq_temp := 1 # 2; uq_count := 0 |}.

Lemma sqrt_T_unit_squared_is_T :
  UnitQ_eq (unit_mul_q sqrt_T_unit sqrt_T_unit)
           {| uq_length := 0; uq_time := 0; uq_mass := 0; uq_charge := 0;
              uq_temp := 1; uq_count := 0 |}.
Proof.
  unfold UnitQ_eq, unit_mul_q, sqrt_T_unit. simpl.
  repeat split; reflexivity.
Qed.

(* === Embedding Z-exponents into Q-exponents === *)

Definition inject_Z_unit (u : Unit) : UnitQ :=
  {| uq_length := inject_Z (u_length u);
     uq_time   := inject_Z (u_time u);
     uq_mass   := inject_Z (u_mass u);
     uq_charge := inject_Z (u_charge u);
     uq_temp   := inject_Z (u_temp u);
     uq_count  := inject_Z (u_count u) |}.

Lemma inject_Z_zero_unit :
  UnitQ_eq (inject_Z_unit zero_unit) zero_unit_q.
Proof.
  unfold UnitQ_eq, inject_Z_unit, zero_unit, zero_unit_q. simpl.
  repeat split; reflexivity.
Qed.

Lemma inject_Z_unit_mul :
  forall u v,
    UnitQ_eq (inject_Z_unit (unit_mul u v))
             (unit_mul_q (inject_Z_unit u) (inject_Z_unit v)).
Proof.
  intros [a1 b1 c1 d1 e1 f1] [a2 b2 c2 d2 e2 f2].
  unfold UnitQ_eq, inject_Z_unit, unit_mul, unit_mul_q. simpl.
  repeat split; rewrite inject_Z_plus; reflexivity.
Qed.

(* === Full Q-exponent powers and roots === *)

(* Multiplication of exponents: (u^m)^n = u^(m*n). *)
Lemma unit_pow_q_mul :
  forall u m n,
    UnitQ_eq (unit_pow_q (unit_pow_q u m) n)
             (unit_pow_q u (m * n)).
Proof.
  intros [a b c d e f] m n.
  unfold UnitQ_eq, unit_pow_q. simpl.
  repeat split; ring.
Qed.

(* Powers preserve unit_mul_q: (u * v)^n = u^n * v^n. *)
Lemma unit_pow_q_mul_distr :
  forall u v n,
    UnitQ_eq (unit_pow_q (unit_mul_q u v) n)
             (unit_mul_q (unit_pow_q u n) (unit_pow_q v n)).
Proof.
  intros [a1 b1 c1 d1 e1 f1] [a2 b2 c2 d2 e2 f2] n.
  unfold UnitQ_eq, unit_pow_q, unit_mul_q. simpl.
  repeat split; ring.
Qed.

(* Negation of exponent equals inverse: u^(-n) = (u^n)^{-1}. *)
Lemma unit_pow_q_neg :
  forall u n,
    UnitQ_eq (unit_pow_q u (- n))
             (unit_inv_q (unit_pow_q u n)).
Proof.
  intros [a b c d e f] n.
  unfold UnitQ_eq, unit_pow_q, unit_inv_q. simpl.
  repeat split; ring.
Qed.

(* nth root via 1/n exponent. *)
Definition nth_root_unit (u : UnitQ) (n : positive) : UnitQ :=
  unit_pow_q u (1 # n).

(* The nth root, raised to the nth power, recovers u (up to UnitQ_eq). *)
Lemma nth_root_unit_pow :
  forall u n,
    UnitQ_eq (unit_pow_q (nth_root_unit u n) (Z.pos n # 1)) u.
Proof.
  intros [a b c d e f] n.
  unfold UnitQ_eq, unit_pow_q, nth_root_unit. simpl.
  assert (H : (Z.pos n # 1) * (1 # n) == 1).
  { unfold Qmult, Qeq. simpl. lia. }
  repeat split.
  - rewrite Qmult_assoc, H. apply Qmult_1_l.
  - rewrite Qmult_assoc, H. apply Qmult_1_l.
  - rewrite Qmult_assoc, H. apply Qmult_1_l.
  - rewrite Qmult_assoc, H. apply Qmult_1_l.
  - rewrite Qmult_assoc, H. apply Qmult_1_l.
  - rewrite Qmult_assoc, H. apply Qmult_1_l.
Qed.

(* Cube root specialisation: cube_root_unit u = u^{1/3}. *)
Definition cube_root_unit (u : UnitQ) : UnitQ := nth_root_unit u 3.

Lemma cube_root_unit_cubed :
  forall u,
    UnitQ_eq (unit_pow_q (cube_root_unit u) (Z.pos 3 # 1)) u.
Proof. intros u. exact (nth_root_unit_pow u 3). Qed.

(* === Axiom audit === *)

Print Assumptions unit_mul_q_inv_r.
Print Assumptions unit_pow_q_add.
Print Assumptions unit_pow_q_mul.
Print Assumptions unit_pow_q_mul_distr.
Print Assumptions unit_pow_q_neg.
Print Assumptions nth_root_unit_pow.
Print Assumptions cube_root_unit_cubed.
Print Assumptions sqrt_unit_squared.
Print Assumptions sqrt_T_unit_squared_is_T.
Print Assumptions inject_Z_zero_unit.
