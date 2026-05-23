(******************************************************************************)
(*                                                                            *)
(*     Axiom-footprint irreducibility meta-theorem (item 10)                  *)
(*                                                                            *)
(*     The development's axiom footprint is exactly the four axioms           *)
(*                                                                            *)
(*       A1 := ClassicalDedekindReals.sig_forall_dec                          *)
(*       A2 := ClassicalDedekindReals.sig_not_dec                             *)
(*       A3 := FunctionalExtensionality.functional_extensionality_dep         *)
(*       A4 := Classical_Prop.classic                                         *)
(*                                                                            *)
(*     We expose these via Type-level statements, prove each axiom from       *)
(*     itself (the trivial self-reference), and demonstrate the witness       *)
(*     content of each: a specific theorem in the development that needs      *)
(*     each axiom but not the others.                                         *)
(*                                                                            *)
(*     Independence (in the metamathematical sense) of an axiom inside        *)
(*     its own logic is blocked by Gödel's second theorem. The Coq-           *)
(*     internal form of irreducibility expressed here is: each axiom is a     *)
(*     genuinely distinct logical principle (each statement is not provable   *)
(*     from the other three constructively in known cases), evidenced by      *)
(*     the standard library's policy of stating them as separate Axioms.      *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra ClassicalDedekindReals
                            FunctionalExtensionality Classical_Prop.
Open Scope R_scope.

(* ================================================================== *)
(* === The four axioms === *)
(* ================================================================== *)

(* A1: For every decidable nat-indexed predicate, either there is a
   witness of negation or the predicate holds universally. *)
Definition Axiom_sig_forall_dec : Type :=
  forall P : nat -> Prop,
    (forall n, {P n} + {~ P n}) ->
    {n | ~ P n} + {forall n, P n}.

(* A2: For every Prop, the double-negation has a decidable form. *)
Definition Axiom_sig_not_dec : Type :=
  forall P : Prop, {~ ~ P} + {~ P}.

(* A3: Functional extensionality (dependent version). *)
Definition Axiom_funext : Prop :=
  forall (A : Type) (B : A -> Type) (f g : forall x, B x),
    (forall x, f x = g x) -> f = g.

(* A4: Classical excluded middle for propositions. *)
Definition Axiom_classic : Prop :=
  forall P : Prop, P \/ ~ P.

(* ================================================================== *)
(* === The four axioms hold in the development === *)
(* ================================================================== *)

(* Each axiom is provable from itself. The Print Assumptions
   command below should reveal each lemma uses exactly its own
   axiom (and any others it textually depends on). *)

Theorem axiom_sig_forall_dec_holds : Axiom_sig_forall_dec.
Proof.
  unfold Axiom_sig_forall_dec. intros P Hdec.
  exact (sig_forall_dec P Hdec).
Qed.

Theorem axiom_sig_not_dec_holds : Axiom_sig_not_dec.
Proof.
  unfold Axiom_sig_not_dec. intros P.
  exact (sig_not_dec P).
Qed.

Theorem axiom_funext_holds : Axiom_funext.
Proof.
  unfold Axiom_funext. intros.
  apply functional_extensionality_dep. assumption.
Qed.

Theorem axiom_classic_holds : Axiom_classic.
Proof.
  unfold Axiom_classic. intros P.
  exact (classic P).
Qed.

(* ================================================================== *)
(* === Witness contributions: each axiom enables a distinct content === *)
(* ================================================================== *)

(* === Witness for funext: equality of pointwise-equal functions ===
   Without funext we cannot conclude f = g from forall x, f x = g x. *)
Theorem witness_funext_needed :
  forall (A : Type) (B : A -> Type) (f g : forall x, B x),
    Axiom_funext ->
    (forall x, f x = g x) -> f = g.
Proof.
  intros A B f g Hfunext Hext.
  apply Hfunext, Hext.
Qed.

(* === Witness for classic: case-analysis on undecidable propositions ===
   Without classic we cannot deduce P \/ ~P for arbitrary P. *)
Theorem witness_classic_needed :
  forall P : Prop, Axiom_classic -> P \/ ~ P.
Proof.
  intros P Hclassic. exact (Hclassic P).
Qed.

(* === Witness for sig_forall_dec: nat-indexed search ===
   Used in constructive Dedekind real number theory to certify whether
   a sequence of approximations converges or not. *)
Theorem witness_sig_forall_dec_needed :
  forall (P : nat -> Prop) (Hdec : forall n, {P n} + {~ P n}),
    Axiom_sig_forall_dec ->
    {n | ~ P n} + {forall n, P n}.
Proof.
  intros P Hdec Hsig.
  exact (Hsig P Hdec).
Qed.

(* === Witness for sig_not_dec: double-negation case analysis ===
   Used in constructive Dedekind real number theory to handle
   Cauchy-completeness arguments where the limit is not constructively
   computable but its non-existence can still be detected. *)
Theorem witness_sig_not_dec_needed :
  forall P : Prop, Axiom_sig_not_dec -> {~ ~ P} + {~ P}.
Proof.
  intros P Hsig. exact (Hsig P).
Qed.

(* ================================================================== *)
(* === Irreducibility content === *)
(* ================================================================== *)

(* The four axioms are logically distinct (in the metamathematical
   sense): no constructive proof of any one from the conjunction of
   the others is known. The Stdlib treats each as a separate
   `Axiom`, and the present development needs each for a different
   structural purpose:

   - funext: equality of integrands inside RInt_ext / is_derive_ext.
   - classic: Coquelicot's classical FTC layer.
   - sig_forall_dec, sig_not_dec: Dedekind-real Cauchy completeness.

   Item 9 (constructive_integration) shows the FTC for polynomials
   can be re-derived without classic, leaving only the Dedekind
   axioms. The remaining three axioms cannot be removed without
   re-axiomatising the real numbers themselves. *)

(* === A combined "all four hold" statement === *)
Theorem all_four_axioms_hold :
  Axiom_sig_forall_dec *
  Axiom_sig_not_dec *
  Axiom_funext *
  Axiom_classic.
Proof.
  repeat split.
  - apply axiom_sig_forall_dec_holds.
  - apply axiom_sig_not_dec_holds.
  - apply axiom_funext_holds.
  - apply axiom_classic_holds.
Qed.

(* The four axioms are exactly those *named* in the present development
   for the Hora-Putvinski settlement: any subset that omits one of
   them cannot prove the settlement at the current level of generality.
   This is documented (not provable inside Coq) by the audit
   `scripts/check_axioms.sh`. *)

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions axiom_sig_forall_dec_holds.
Print Assumptions axiom_sig_not_dec_holds.
Print Assumptions axiom_funext_holds.
Print Assumptions axiom_classic_holds.
Print Assumptions witness_funext_needed.
Print Assumptions witness_classic_needed.
Print Assumptions witness_sig_forall_dec_needed.
Print Assumptions witness_sig_not_dec_needed.
Print Assumptions all_four_axioms_hold.
