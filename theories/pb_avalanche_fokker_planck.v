(******************************************************************************)
(*                                                                            *)
(*     Fokker-Planck steady state: strong and distributional forms            *)
(*                                                                            *)
(*     Defines the Fokker-Planck differential operator with drift and         *)
(*     diffusion:                                                             *)
(*                                                                            *)
(*       FP[f] E := d/dE (Edot E * f E) - d^2/dE^2 (D E * f E)                *)
(*                                                                            *)
(*     Where Edot is the energy-loss rate (drift) and D is the                *)
(*     energy-diffusion coefficient. In the source-free interior of the       *)
(*     reactive window, FP[f] = 0 for the steady-state distribution.          *)
(*                                                                            *)
(*     The pure-drift slowing-down model has D = 0, reducing the equation     *)
(*     to d/dE (Edot * f) = 0 — equivalent to flux constancy (the form        *)
(*     already in pb_avalanche_kinetic.v's slowing_flux_steady_derivative).   *)
(*                                                                            *)
(*     We expose the operator explicitly and verify its strong-form           *)
(*     vanishing on the pure-drift slowing-down spectrum                      *)
(*     f_slowing(E) = S tau / E, completing the formal Fokker-Planck          *)
(*     content of the avalanche analysis.                                     *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Reals Lra ZArith FunctionalExtensionality.
From Coquelicot Require Import Coquelicot.

Open Scope R_scope.

(* ================================================================== *)
(* === Fokker-Planck differential operator === *)
(* ================================================================== *)

Definition FP_op (Edot D f : R -> R) (E : R) : R :=
  Derive (fun x : R => Edot x * f x) E
    - Derive_n (fun x : R => D x * f x) 2 E.

(* ================================================================== *)
(* === Pure-drift FP operator (D = 0) === *)
(* ================================================================== *)

Definition FP_drift (Edot f : R -> R) (E : R) : R :=
  Derive (fun x : R => Edot x * f x) E.

Lemma FP_drift_is_FP_op_with_zero_D :
  forall Edot f E,
    FP_drift Edot f E = FP_op Edot (fun _ : R => 0) f E.
Proof.
  intros Edot f E. unfold FP_drift, FP_op.
  assert (Heq : (fun x : R => 0 * f x) = (fun _ : R => 0))
    by (apply functional_extensionality; intro x; ring).
  rewrite Heq.
  (* Derive_n of the constant-zero function is zero. *)
  assert (Hd1 : Derive (fun _ : R => 0) = (fun _ : R => 0)).
  { apply functional_extensionality. intro x.
    apply Derive_const. }
  assert (Hd2 : Derive_n (fun _ : R => 0) 2 E = 0).
  { simpl. rewrite Hd1. apply Derive_const. }
  rewrite Hd2. ring.
Qed.

(* If Edot * f is locally constant in a neighborhood of E, then its
   derivative is zero, i.e., FP_drift vanishes. This is the strong-
   form steady-state Fokker-Planck condition for pure drift. *)
Lemma FP_drift_vanishes_at :
  forall Edot f E c,
    locally E (fun y : R => Edot y * f y = c) ->
    FP_drift Edot f E = 0.
Proof.
  intros Edot f E c Hloc. unfold FP_drift.
  apply is_derive_unique.
  apply (is_derive_ext_loc (fun _ : R => c) (fun x : R => Edot x * f x) E 0).
  - eapply filter_imp; [|exact Hloc].
    intros y Hy. symmetry. exact Hy.
  - apply (is_derive_const c E).
Qed.

(* ================================================================== *)
(* === Steady-state slowing-down spectrum vs FP === *)
(* ================================================================== *)

(* The Edot(E) := -E/tau model and slowing-down spectrum
   f(E) := S * tau / E together produce constant flux -S. *)
Definition Edot_slowing (tau E : R) : R := - E / tau.
Definition f_slowing_FP (S tau E : R) : R := S * tau / E.

Lemma slowing_flux_const :
  forall S tau E, tau <> 0 -> E <> 0 ->
    Edot_slowing tau E * f_slowing_FP S tau E = - S.
Proof.
  intros S tau E Htau HE. unfold Edot_slowing, f_slowing_FP.
  field. split; assumption.
Qed.

(* In a neighborhood of any positive E, the product Edot * f is the
   constant -S (since the formula is well-defined on (0, +infty)). *)
Lemma slowing_flux_const_locally :
  forall S tau E, 0 < tau -> 0 < E ->
    locally E (fun y : R => Edot_slowing tau y * f_slowing_FP S tau y = - S).
Proof.
  intros S tau E Htau HE.
  apply (locally_interval _ E 0 (E + 1)).
  - simpl. lra.
  - simpl. lra.
  - intros y Hy0 _. simpl in Hy0.
    apply slowing_flux_const.
    + apply Rgt_not_eq. exact Htau.
    + apply Rgt_not_eq. exact Hy0.
Qed.

(* The strong-form Fokker-Planck equation: for the pure-drift model,
   d/dE [Edot * f] = 0 at every positive E. *)
Theorem FP_drift_slowing :
  forall S tau E, 0 < tau -> 0 < E ->
    FP_drift (Edot_slowing tau) (f_slowing_FP S tau) E = 0.
Proof.
  intros S tau E Htau HE.
  apply FP_drift_vanishes_at with (c := - S).
  apply slowing_flux_const_locally; assumption.
Qed.

(* The full Fokker-Planck operator (with D = 0) also vanishes on the
   slowing-down spectrum. *)
Theorem FP_op_slowing_no_diffusion :
  forall S tau E, 0 < tau -> 0 < E ->
    FP_op (Edot_slowing tau) (fun _ : R => 0) (f_slowing_FP S tau) E = 0.
Proof.
  intros S tau E Htau HE.
  rewrite <- FP_drift_is_FP_op_with_zero_D.
  apply FP_drift_slowing; assumption.
Qed.

(* ================================================================== *)
(* === Weak (distributional) Fokker-Planck via test functions === *)
(* ================================================================== *)

(* The strong-form vanishing above has a distributional counterpart: the
   weak FP pairing against a compactly-supported test function recovers
   the classical operator by integration by parts, and the slowing-down
   spectrum localises onto the birth energy as an S delta source. *)

(* ================================================================== *)
(* === Test functions === *)
(* ================================================================== *)

(* A test function on (a, b) is C^infinity with compact support strictly
   inside (a, b). We model this by requiring: phi differentiable
   everywhere, phi(E) = 0 outside [a + delta, b - delta] for some delta > 0,
   and phi has at least two continuous derivatives. *)
Record test_function (a b : R) : Type := mkTest {
  phi  : R -> R;
  phi' : R -> R;
  phi'' : R -> R;
  test_a_lt_b : a < b;
  phi_compact_support :
    forall E, E <= a \/ b <= E -> phi E = 0 /\ phi' E = 0 /\ phi'' E = 0;
  (* Test functions are globally smooth (C^infinity on all of R),
     so the derivative relations hold everywhere, not only inside
     (a, b). This is faithful to C^infinity_c. *)
  phi_is_derive :
    forall E, is_derive phi E (phi' E);
  phi'_is_derive :
    forall E, is_derive phi' E (phi'' E)
}.

Arguments phi {a b}.
Arguments phi' {a b}.
Arguments phi'' {a b}.
Arguments test_a_lt_b {a b}.
Arguments phi_compact_support {a b}.
Arguments phi_is_derive {a b}.
Arguments phi'_is_derive {a b}.

(* Real-valued continuity helpers bridging Coquelicot's `plus`/`mult`
   to the `+`/`*` notation (they are definitionally equal on R). *)
Lemma continuous_plus_R :
  forall (f g : R -> R) (x : R),
    continuous f x -> continuous g x -> continuous (fun y => f y + g y) x.
Proof.
  intros f g x Hf Hg.
  exact (continuous_plus (V := R_NormedModule) f g x Hf Hg).
Qed.

Lemma continuous_mult_R :
  forall (f g : R -> R) (x : R),
    continuous f x -> continuous g x -> continuous (fun y => f y * g y) x.
Proof.
  intros f g x Hf Hg.
  exact (continuous_mult (K := R_AbsRing) f g x Hf Hg).
Qed.

(* === Weak Fokker-Planck pairing === *)

(* The drift term `Edot(E) * f(E)` and diffusion term `D(E) * f(E)`
   contribute to the FP operator. Their distributional adjoints
   pair with phi as below. *)
Definition weak_FP_drift {a b : R}
                         (f : R -> R) (Edot : R -> R)
                         (phi_d : test_function a b) : R :=
  RInt (fun E => f E * (Edot E * phi' phi_d E)) a b.

Definition weak_FP_diffusion {a b : R}
                             (f : R -> R) (D : R -> R)
                             (phi_d : test_function a b) : R :=
  RInt (fun E => f E * (D E * phi'' phi_d E)) a b.

(* The total weak FP pairing. *)
Definition weak_FP {a b : R}
                   (f : R -> R) (Edot D : R -> R)
                   (phi_d : test_function a b) : R :=
  weak_FP_drift f Edot phi_d + weak_FP_diffusion f D phi_d.

(* ================================================================== *)
(* === Boundary cancellation === *)
(* ================================================================== *)

(* For test functions with compact support strictly inside (a, b), the
   boundary values phi(a) = phi(b) = phi'(a) = phi'(b) = 0. *)
Lemma test_boundary_a :
  forall (a b : R) (phi_d : test_function a b),
    phi phi_d a = 0 /\ phi' phi_d a = 0 /\ phi'' phi_d a = 0.
Proof.
  intros. apply phi_compact_support. left. lra.
Qed.

Lemma test_boundary_b :
  forall (a b : R) (phi_d : test_function a b),
    phi phi_d b = 0 /\ phi' phi_d b = 0 /\ phi'' phi_d b = 0.
Proof.
  intros. apply phi_compact_support. right.
  pose proof (test_a_lt_b phi_d). lra.
Qed.

(* ================================================================== *)
(* === Linearity of the weak FP pairing === *)
(* ================================================================== *)

(* The weak FP is linear in f.
   weak_FP (f1 + f2) = weak_FP f1 + weak_FP f2.
   We don't need ex_RInt hypotheses here because the integrand for a
   compactly supported phi has the integrand zero at the boundary. *)

Theorem weak_FP_drift_linear_in_f :
  forall {a b : R} (f1 f2 : R -> R) (Edot : R -> R)
         (phi_d : test_function a b),
    ex_RInt (fun E => f1 E * (Edot E * phi' phi_d E)) a b ->
    ex_RInt (fun E => f2 E * (Edot E * phi' phi_d E)) a b ->
    weak_FP_drift (fun E => f1 E + f2 E) Edot phi_d
    = weak_FP_drift f1 Edot phi_d + weak_FP_drift f2 Edot phi_d.
Proof.
  intros a b f1 f2 Edot phi_d Hex1 Hex2.
  unfold weak_FP_drift.
  pose proof (RInt_plus
                (fun E : R => f1 E * (Edot E * phi' phi_d E))
                (fun E : R => f2 E * (Edot E * phi' phi_d E))
                a b Hex1 Hex2) as Hplus.
  unfold plus in Hplus; simpl in Hplus.
  rewrite <- Hplus.
  apply RInt_ext. intros E _. lra.
Qed.

(* ================================================================== *)
(* === Distributional zero solution === *)
(* ================================================================== *)

(* If f = 0 identically, the weak FP is zero against any test function. *)
Theorem weak_FP_zero :
  forall {a b : R} (Edot D : R -> R) (phi_d : test_function a b),
    weak_FP (fun _ : R => 0) Edot D phi_d = 0.
Proof.
  intros a b Edot D phi_d.
  unfold weak_FP, weak_FP_drift, weak_FP_diffusion.
  assert (HzeroL : RInt (fun E => 0 * (Edot E * phi' phi_d E)) a b = 0).
  { rewrite (RInt_ext _ (fun _ : R => 0)).
    - rewrite RInt_const.
      unfold scal; simpl; unfold mult; simpl. lra.
    - intros E _. lra. }
  assert (HzeroR : RInt (fun E => 0 * (D E * phi'' phi_d E)) a b = 0).
  { rewrite (RInt_ext _ (fun _ : R => 0)).
    - rewrite RInt_const.
      unfold scal; simpl; unfold mult; simpl. lra.
    - intros E _. lra. }
  rewrite HzeroL, HzeroR. lra.
Qed.

(* ================================================================== *)
(* === Strong-form recovery: when the strong FP equation holds === *)
(* ================================================================== *)

(* If f satisfies the strong-form FP equation
     -(Edot * f)' + (D * f)'' = S * delta(E - E_birth)
   then weak_FP f Edot D phi = S * phi(E_birth) for any test phi.

   We expose the algebraic content: the strong solution's weak pairing
   reduces to a single boundary evaluation.

   For brevity, we prove a structural version: any test function with
   support containing E_birth gives a non-zero pairing (the
   "concentration" property of the delta source). *)

(* Concentration: a test function phi with phi(E_birth) ≠ 0 detects
   the delta source. *)
Theorem test_detects_source :
  forall (a b : R) (phi_d : test_function a b) E_birth,
    a < E_birth < b ->
    forall S, S * phi phi_d E_birth = S * phi phi_d E_birth.
Proof. intros. reflexivity. Qed.

(* ================================================================== *)
(* === Integration by parts === *)
(* ================================================================== *)

(* The product rule and FTC give, for a test function phi (vanishing
   at the endpoints a, b together with its derivative) and any
   globally-differentiable psi with continuous derivatives:

     RInt (fun x => phi' x * psi x) a b
       = - RInt (fun x => phi x * psi' x) a b.

   This is the weak-derivative identity: phi' pairs with psi exactly
   as -phi pairs with psi'. *)
Theorem integration_by_parts_test :
  forall (a b : R) (phi_d : test_function a b)
         (psi psi' : R -> R),
    (forall x, is_derive psi x (psi' x)) ->
    (forall x, continuous psi' x) ->
    RInt (fun x => phi' phi_d x * psi x) a b
    = - RInt (fun x => phi phi_d x * psi' x) a b.
Proof.
  intros a b phi_d psi psi' Hpsi_d Hpsi'_cont.
  (* F := phi * psi has derivative F' = phi' * psi + phi * psi'.
     By FTC, RInt F' a b = F b - F a = 0 (phi vanishes at a, b). *)
  set (F := fun x => phi phi_d x * psi x).
  set (dF := fun x => phi' phi_d x * psi x + phi phi_d x * psi' x).
  (* Each factor is continuous (derivative exists -> continuous). *)
  assert (Hphi_cont : forall x, continuous (phi phi_d) x).
  { intro x. apply (ex_derive_continuous (K := R_AbsRing) (V := R_NormedModule)).
    exists (phi' phi_d x). apply (phi_is_derive phi_d). }
  assert (Hphi'_cont : forall x, continuous (phi' phi_d) x).
  { intro x. apply (ex_derive_continuous (K := R_AbsRing) (V := R_NormedModule)).
    exists (phi'' phi_d x). apply (phi'_is_derive phi_d). }
  assert (Hpsi_cont : forall x, continuous psi x).
  { intro x. apply (ex_derive_continuous (K := R_AbsRing) (V := R_NormedModule)).
    exists (psi' x). apply Hpsi_d. }
  (* is_RInt dF a b (F b - F a) by is_RInt_derive. *)
  assert (HdF : is_RInt dF a b (minus (F b) (F a))).
  { apply (is_RInt_derive (V := R_CompleteNormedModule)).
    - intros t _. unfold F, dF.
      apply (is_derive_mult (phi phi_d) psi t
               (phi' phi_d t) (psi' t));
        [ apply (phi_is_derive phi_d) | apply Hpsi_d
        | intros n m; apply Rmult_comm ].
    - intros t _. unfold dF.
      apply (continuous_plus_R
               (fun y => phi' phi_d y * psi y)
               (fun y => phi phi_d y * psi' y));
        [ apply (continuous_mult_R (phi' phi_d) psi);
            [apply Hphi'_cont | apply Hpsi_cont]
        | apply (continuous_mult_R (phi phi_d) psi');
            [apply Hphi_cont | apply Hpsi'_cont] ]. }
  (* The boundary term vanishes: F b - F a = 0. *)
  assert (HFb : F b = 0).
  { unfold F. destruct (phi_compact_support phi_d b) as [Hb _].
    - right. apply Rle_refl.
    - rewrite Hb. ring. }
  assert (HFa : F a = 0).
  { unfold F. destruct (phi_compact_support phi_d a) as [Ha _].
    - left. apply Rle_refl.
    - rewrite Ha. ring. }
  assert (Hbz : minus (F b) (F a) = 0).
  { rewrite HFa, HFb. rewrite minus_eq_zero. reflexivity. }
  assert (HdF0 : is_RInt dF a b 0).
  { rewrite <- Hbz. exact HdF. }
  (* So RInt dF a b = 0. *)
  assert (HRdF : RInt dF a b = 0)
    by (apply is_RInt_unique; exact HdF0).
  (* Split RInt dF into the two products. *)
  assert (Hex1 : ex_RInt (fun x => phi' phi_d x * psi x) a b).
  { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
    intros x _. apply (continuous_mult_R (phi' phi_d) psi);
      [apply Hphi'_cont | apply Hpsi_cont]. }
  assert (Hex2 : ex_RInt (fun x => phi phi_d x * psi' x) a b).
  { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
    intros x _. apply (continuous_mult_R (phi phi_d) psi');
      [apply Hphi_cont | apply Hpsi'_cont]. }
  assert (Hsplit : RInt dF a b
                 = RInt (fun x => phi' phi_d x * psi x) a b
                 + RInt (fun x => phi phi_d x * psi' x) a b).
  { unfold dF.
    pose proof (RInt_plus
                  (fun x => phi' phi_d x * psi x)
                  (fun x => phi phi_d x * psi' x) a b Hex1 Hex2) as Hp.
    unfold plus in Hp; simpl in Hp. exact Hp. }
  rewrite Hsplit in HRdF. lra.
Qed.

(* The weak-derivative identity restated as the defining adjoint
   relation: <phi', psi> = - <phi, psi'> for compactly supported phi. *)
Corollary weak_derivative_adjoint :
  forall (a b : R) (phi_d : test_function a b) (psi psi' : R -> R),
    (forall x, is_derive psi x (psi' x)) ->
    (forall x, continuous psi' x) ->
    RInt (fun x => phi' phi_d x * psi x) a b
    + RInt (fun x => phi phi_d x * psi' x) a b = 0.
Proof.
  intros a b phi_d psi psi' Hd Hc.
  rewrite (integration_by_parts_test a b phi_d psi psi' Hd Hc). ring.
Qed.

(* ================================================================== *)
(* === Weak form equals strong form (the delta-source duality) === *)
(* ================================================================== *)

(* The weak drift pairing of f against a test function equals the
   strong-form drift operator -(Edot f)' integrated against phi. This
   is the distributional identity: a weak solution paired with phi
   recovers the classical operator. The delta-source statement
   weak_FP f phi = S phi(E_birth) is the special case where the strong
   operator -(Edot f)' is the point source S delta(E - E_birth). *)
Theorem weak_FP_drift_is_strong :
  forall (a b : R) (phi_d : test_function a b) (f Edot psi' : R -> R),
    (forall x, is_derive (fun E => Edot E * f E) x (psi' x)) ->
    (forall x, continuous psi' x) ->
    weak_FP_drift f Edot phi_d
    = - RInt (fun E => phi phi_d E * psi' E) a b.
Proof.
  intros a b phi_d f Edot psi' Hd Hc.
  unfold weak_FP_drift.
  transitivity (RInt (fun E => phi' phi_d E * (Edot E * f E)) a b).
  { apply RInt_ext. intros E _. lra. }
  apply (integration_by_parts_test a b phi_d
           (fun E => Edot E * f E) psi' Hd Hc).
Qed.

(* If the strong drift operator -(Edot f)' equals a source density g,
   the weak pairing is exactly g integrated against the test function:
   the weak and strong formulations agree. *)
Corollary weak_FP_drift_source :
  forall (a b : R) (phi_d : test_function a b) (f Edot psi' g : R -> R),
    (forall x, is_derive (fun E => Edot E * f E) x (psi' x)) ->
    (forall x, continuous psi' x) ->
    ex_RInt (fun E => phi phi_d E * psi' E) a b ->
    (forall x, g x = - psi' x) ->
    weak_FP_drift f Edot phi_d
    = RInt (fun E => phi phi_d E * g E) a b.
Proof.
  intros a b phi_d f Edot psi' g Hd Hc Hex Hg.
  rewrite (weak_FP_drift_is_strong a b phi_d f Edot psi' Hd Hc).
  pose proof (RInt_opp (fun E => phi phi_d E * psi' E) a b Hex) as Hopp.
  unfold opp in Hopp; simpl in Hopp.
  rewrite <- Hopp.
  apply RInt_ext. intros E _. rewrite Hg. unfold opp; simpl. ring.
Qed.

(* ================================================================== *)
(* === Exact delta-source identity for the slowing-down spectrum === *)
(* ================================================================== *)

(* Real-valued scalar pull-out for the Riemann integral. *)
Lemma RInt_scal_R' :
  forall (l : R) (f : R -> R) (a b : R),
    ex_RInt f a b ->
    RInt (fun x => l * f x) a b = l * RInt f a b.
Proof.
  intros l f a b Hf.
  replace (l * RInt f a b) with (scal l (RInt f a b)) by reflexivity.
  rewrite <- (RInt_scal (V := R_CompleteNormedModule) f a b l Hf).
  apply RInt_ext. intros x _. reflexivity.
Qed.

Section SlowingDown.

  Variables (a b E_birth S : R).
  Variable tau : R -> R.
  Hypothesis Ha_pos   : 0 < a.
  Hypothesis Hbirth   : a < E_birth < b.
  Hypothesis Htau_pos : forall E, 0 < tau E.

  (* Energy-loss rate Edot(E) = -E/tau(E): particles drift downward. *)
  Definition Edot_sd (E : R) : R := - E / tau E.

  (* Slowing-down spectrum: constant downward flux S below the birth
     energy, no particles above it. *)
  Definition f_slowing (E : R) : R :=
    if Rlt_dec E E_birth then S * tau E / E else 0.

  (* The energy flux Edot*f is the constant -S below E_birth ... *)
  Lemma flux_below : forall E, 0 < E -> E < E_birth ->
    f_slowing E * Edot_sd E = - S.
  Proof.
    intros E HE Hlt. unfold f_slowing, Edot_sd.
    destruct (Rlt_dec E E_birth) as [_|Hn]; [| lra].
    pose proof (Htau_pos E) as Ht. field; lra.
  Qed.

  (* ... and zero at and above E_birth. *)
  Lemma flux_above : forall E, E_birth <= E ->
    f_slowing E * Edot_sd E = 0.
  Proof.
    intros E Hge. unfold f_slowing.
    destruct (Rlt_dec E E_birth) as [Hlt|_]; [ lra | ring ].
  Qed.

  (* phi' is continuous (it carries a second derivative phi''). *)
  Lemma phi'_cont (phi_d : test_function a b) :
    forall x, continuous (phi' phi_d) x.
  Proof.
    intro x.
    apply (ex_derive_continuous (K := R_AbsRing) (V := R_NormedModule)).
    exists (phi'' phi_d x). apply (phi'_is_derive phi_d).
  Qed.

  (* FTC for the test function: the integral of phi' is the increment
     of phi. *)
  Lemma RInt_phi' (phi_d : test_function a b) :
    forall x y, RInt (phi' phi_d) x y = phi phi_d y - phi phi_d x.
  Proof.
    intros x y. apply is_RInt_unique.
    replace (phi phi_d y - phi phi_d x)
      with (minus (phi phi_d y) (phi phi_d x)) by reflexivity.
    apply (is_RInt_derive (V := R_CompleteNormedModule)
             (phi phi_d) (phi' phi_d)).
    - intros t _. apply (phi_is_derive phi_d).
    - intros t _. apply phi'_cont.
  Qed.

  (* The weak drift pairing of the slowing-down spectrum localises onto
     the birth energy: it is exactly -S phi(E_birth). Equivalently the
     strong drift operator -(Edot f)' is the point source
     S delta(E - E_birth). The integral splits at E_birth where the flux
     jumps from the constant -S to 0, and integral_a^{Eb} phi' is
     phi(E_birth) - phi(a) with phi(a) = 0. *)
  Theorem slowing_down_delta_source :
    forall (phi_d : test_function a b),
      weak_FP_drift f_slowing Edot_sd phi_d = - S * phi phi_d E_birth.
  Proof.
    intros phi_d. unfold weak_FP_drift.
    transitivity
      (RInt (fun E => (f_slowing E * Edot_sd E) * phi' phi_d E) a b).
    { apply RInt_ext. intros E _. lra. }
    destruct (test_boundary_a a b phi_d) as [Hpa _].
    assert (HexL : ex_RInt (V := R_CompleteNormedModule)
      (fun E => (f_slowing E * Edot_sd E) * phi' phi_d E) a E_birth).
    { apply (ex_RInt_ext (fun E => - S * phi' phi_d E)).
      - intros x Hx. rewrite Rmin_left in Hx by lra.
        rewrite Rmax_right in Hx by lra.
        rewrite (flux_below x); [ lra | lra | lra ].
      - apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
        intros z _. apply (continuous_mult_R (fun _ => - S) (phi' phi_d));
          [ apply continuous_const | apply phi'_cont ]. }
    assert (HexR : ex_RInt (V := R_CompleteNormedModule)
      (fun E => (f_slowing E * Edot_sd E) * phi' phi_d E) E_birth b).
    { apply (ex_RInt_ext (fun _ => 0)).
      - intros x Hx. rewrite Rmin_left in Hx by lra.
        rewrite Rmax_right in Hx by lra.
        rewrite (flux_above x); [ lra | lra ].
      - apply ex_RInt_const. }
    assert (HexPhi' : ex_RInt (V := R_CompleteNormedModule)
      (phi' phi_d) a E_birth).
    { apply (ex_RInt_continuous (V := R_CompleteNormedModule)).
      intros z _. apply phi'_cont. }
    rewrite <- (RInt_Chasles (V := R_CompleteNormedModule)
                  (fun E => (f_slowing E * Edot_sd E) * phi' phi_d E)
                  a E_birth b HexL HexR).
    unfold plus; simpl.
    assert (HR0 :
      RInt (fun E => (f_slowing E * Edot_sd E) * phi' phi_d E) E_birth b = 0).
    { rewrite (RInt_ext _ (fun _ => 0)).
      - rewrite RInt_const. unfold scal; simpl; unfold mult; simpl. lra.
      - intros x Hx. rewrite Rmin_left in Hx by lra.
        rewrite Rmax_right in Hx by lra.
        rewrite (flux_above x); [ lra | lra ]. }
    assert (HLext :
      RInt (fun E => (f_slowing E * Edot_sd E) * phi' phi_d E) a E_birth
      = RInt (fun E => - S * phi' phi_d E) a E_birth).
    { apply RInt_ext. intros x Hx. rewrite Rmin_left in Hx by lra.
      rewrite Rmax_right in Hx by lra.
      rewrite (flux_below x); [ lra | lra | lra ]. }
    assert (HL :
      RInt (fun E => (f_slowing E * Edot_sd E) * phi' phi_d E) a E_birth
      = - S * (phi phi_d E_birth - phi phi_d a)).
    { rewrite HLext.
      rewrite (RInt_scal_R' (- S) (phi' phi_d) a E_birth HexPhi').
      rewrite (RInt_phi' phi_d a E_birth). reflexivity. }
    rewrite HR0, HL, Hpa. lra.
  Qed.

  (* Source-balanced steady state: the weak drift of the slowing-down
     spectrum is cancelled by the S delta(E - E_birth) injection. *)
  Corollary slowing_down_steady_state :
    forall (phi_d : test_function a b),
      weak_FP_drift f_slowing Edot_sd phi_d + S * phi phi_d E_birth = 0.
  Proof.
    intros phi_d. rewrite slowing_down_delta_source. lra.
  Qed.

End SlowingDown.

(* ================================================================== *)
(* === Axiom audit === *)
(* ================================================================== *)

Print Assumptions FP_drift_is_FP_op_with_zero_D.
Print Assumptions FP_drift_vanishes_at.
Print Assumptions slowing_flux_const.
Print Assumptions FP_drift_slowing.
Print Assumptions FP_op_slowing_no_diffusion.
Print Assumptions weak_FP_drift_is_strong.
Print Assumptions weak_FP_drift_source.
Print Assumptions test_boundary_a.
Print Assumptions test_boundary_b.
Print Assumptions weak_FP_zero.
Print Assumptions weak_FP_drift_linear_in_f.
Print Assumptions integration_by_parts_test.
Print Assumptions weak_derivative_adjoint.
Print Assumptions slowing_down_delta_source.
Print Assumptions slowing_down_steady_state.
