Require Import Coq.Arith.Cantor.
(* Require Import Coq.Logic.FunctionalExtensionality. *)
(* Require Import Coq.Logic.PropExtensionality. *)
Require Import Coq.Sets.Ensembles.
(* Require Import Coq.Sets.Finite_sets. *)
Require Import Coq.Sets.Image.
(* Require Import Coq.Sets.Infinite_sets. *)
(* Require Import Coq.Sets.Integers. *)
Require Import Lia.

Arguments In {_} _ _ : assert.
Arguments Im {_ _} _ _ _ : assert.
Arguments Included {_} _ _ : assert.
Arguments Inhabited {_} _ : assert.
Arguments Empty_set {_} _ : assert.
Arguments Full_set {_} _ : assert.
Arguments Singleton {_} _ _ : assert.
Arguments Union {_} _ _ _ : assert.
Arguments Intersection {_} _ _ _ : assert.
Arguments Same_set {_} _ _ : assert.

Record filter (A : Ensemble nat) (F : Ensemble (Ensemble nat)) : Type := {
  filter_inhabited : In F A;
  filter_subsets : forall X, In F X -> Included X A;
  filter_closed : forall X Y, Included X A -> Included Y A ->
    In F (Intersection X Y) <-> In F X /\ In F Y;
}.

Definition improper_def (A : Ensemble nat) : Ensemble (Ensemble nat) :=
  fun S => Included S A.

Definition improper A : filter A (improper_def A).
Proof.
  constructor.
  - intro; trivial.
  - intro; trivial.
  - split; [firstorder|].
    intros [? ?] ? [? ?].
    firstorder.
Defined.

Definition simple A : filter A (Singleton A).
Proof.
  constructor.
  - constructor.
  - intros ? H; inversion H; firstorder.
  - intros X Y XA YA; split; intros H; inversion H; subst.
    + set (XeqA := Extensionality_Ensembles nat X (Intersection X Y) (conj XA (Intersection_decreases_l _ _ _))).
      set (YeqA := Extensionality_Ensembles nat Y (Intersection X Y) (conj YA (Intersection_decreases_r _ _ _))).
      rewrite YeqA at 3.
      rewrite <- XeqA.
      firstorder.
    + inversion H0; inversion H1; subst.
      replace (Intersection Y Y) with Y.
      * constructor.
      * apply Extensionality_Ensembles.
        split; do 2 intro.
        -- constructor; assumption.
        -- destruct H2; assumption.
Defined.

Definition preimage (A B : Ensemble nat) (f : nat -> nat) : Ensemble nat :=
  fun x => In A x /\ In B (f x).

(* Lemma preimage_dist_intersection A X Y f : *)
(*   Same_set (preimage A (Intersection X Y) f) (Intersection (preimage A X f) (preimage A Y f)). *)
(* Proof. *)
(*   split. *)
(*   - intros ? ?. *)
(*     inversion H. *)
(*     firstorder. *)
(*     split. *)
(*     firstorder. *)

Lemma preimage_filter A F X Y f (filterF : filter A F) :
  In F (preimage A (Intersection X Y) f) <-> In F (preimage A X f) /\ In F (preimage A Y f).
Proof.
  split; intros.
