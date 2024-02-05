
Require Import Coq.Unicode.Utf8.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Image.
Require Import Coq.Vectors.Vector.
Require Import Coq.Sets.Classical_sets.
(* Require Import Coq.Logic.FunctionalExtensionality. *)
(* Require Import Coq.Logic.ProofIrrelevance. *)

Reserved Notation "f '⁻¹' ( Y )" (at level 1, Y at level 99, format "f '⁻¹' ( Y )").

Notation "∅" := (Empty_set _).
Notation "x ∈ A" := (Ensembles.In _ A x) (at level 50, no associativity).
Notation "A ⊆ B" := (Ensembles.Included _ A B) (at level 50, no associativity).
Notation "A ∩ B" := (Ensembles.Intersection _ A B) (at level 40, left associativity).
Notation "A ∪ B" := (Ensembles.Union _ A B) (at level 50, left associativity).
Notation "A =s B" := (Ensembles.Same_set _ A B) (at level 95, no associativity).
Notation "f [ A ]" := (Image.Im _ _ A f) (at level 1, A at level 99, format "f [ A ]").

Definition set_function {U} (A B : Ensemble U) : Type :=
  { f : U → U & f[A] ⊆ B }.

Notation "A ⇒ B" := (set_function A B) (at level 99, right associativity, B at level 200).

Definition set_function_apply {U A B} (f : A ⇒ B) : U → U := projT1 f.

Coercion set_function_apply : set_function >-> Funclass.

Section Filters.
  (* The universe type *)
  Variable U : Type.

  (* `Filter A F` represents the fact that `F` is a filter on `A` *)
  Record Filter (A : Ensemble U) (F : Ensemble (Ensemble U)) : Type := {
    (* Filters are nonempty sets *)
    filter_nonempty : Inhabited _ F;
    (* Every element of F is a subset of A *)
    filter_subsets : ∀ X, X ∈ F → X ⊆ A;
    (* The filter property *)
    filter_closed : ∀ X Y, X ⊆ A → Y ⊆ A → X ∩ Y ∈ F ↔ X ∈ F ∧ Y ∈ F;
  }.

  (* Although F is defined only to be nonempty, this implies it contains A *)
  Lemma filter_contains_top {A F} : Filter A F → A ∈ F.
  Proof.
    intros filterF.
    destruct filterF as [inhabited subset closed].
    destruct inhabited as [S SF].
    assert (SA : S ⊆ A) by firstorder.

    assert (SAA : S ∩ A ⊆ A).
    { intros x xSA. inversion xSA. assumption. }
    assert (AA : A ⊆ A) by firstorder.
    destruct (closed (S ∩ A) A SAA AA).
    assert (S ∩ A ∩ A = S).
    {
      apply Extensionality_Ensembles.
      split.
      - intros x xSAA.
        inversion xSAA.
        inversion H1.
        assumption.
      - intros x xS.
        constructor.
        constructor.
        assumption.
        apply SA; assumption.
        apply SA; assumption.
    }
    rewrite <- H1 in SF.
    destruct (H SF).
    assumption.
  Qed.

  (* UF := ∪F. This equivalently the largest set in F. *)
  Definition universe (F : Ensemble (Ensemble U)) : Ensemble U :=
    λ x, ∃ S, S ∈ F ∧ x ∈ S.

  (* NA := {S | S ⊆ A} is a filter, known as the improper filter *)
  Definition improper (A : Ensemble U) : Ensemble (Ensemble U) :=
    λ S, S ⊆ A.

  Definition improper_filter (A : Ensemble U) : Filter A (improper A).
  Proof.
    constructor.
    - exists ∅.
      firstorder.
    - firstorder.
    - intros; split; [ firstorder | ].
      intros ? ? xXY.
      destruct xXY.
      firstorder.
  Qed.

  Lemma improper_universe (A : Ensemble U) :
    universe (improper A) =s A.
  Proof. firstorder. Qed.

  Definition simple (A : Ensemble U) : Ensemble (Ensemble U) :=
    Singleton _ A.

  Definition simple_filter (A : Ensemble U) : Filter A (simple A).
  Proof.
    constructor.
    - exists A; firstorder.
    - intros X H.
      destruct H.
      firstorder.
    - intros X Y XA YA.
      split.
      + intros H; inversion H; subst.
        split.
        * assert (X = X ∩ Y). { apply Extensionality_Ensembles. split. assumption. do 2 intro. destruct H0; assumption. }
          rewrite H0 at 2.
          constructor.
        * assert (Y = X ∩ Y). { apply Extensionality_Ensembles. split. assumption. do 2 intro. destruct H0; assumption. }
          rewrite H0 at 2.
          constructor.
      + intros [H1 H2].
        inversion H1; subst.
        inversion H2; subst.
        assert (Y ∩ Y = Y). { apply Extensionality_Ensembles. split; do 2 intro. inversion H; assumption. constructor; assumption. }
        rewrite H.
        constructor.
  Qed.

  Definition preimage {A B} (f : A ⇒ B) (Y : Ensemble U) : Ensemble U :=
    λ x, x ∈ A ∧ f x ∈ Y.

  Notation "f '⁻¹' ( Y )" := (preimage f Y).

  Lemma preimage_image {A B X} (f : A ⇒ B) : X ⊆ A → X ⊆ f⁻¹(f[X]).
  Proof.
    intros XA x xX.
    split.
    - apply XA; apply xX.
    - apply Im_intro with (x := x); trivial.
  Qed.

  Lemma image_preimage {A B Y} (f : A ⇒ B) : f[f⁻¹(Y)] ⊆ Y.
  Proof.
    intros y yim.
    destruct yim; subst.
    destruct H.
    assumption.
  Qed.

  Lemma preimage_subset_domain {A B} (f : A ⇒ B) Y : f⁻¹(Y) ⊆ A.
  Proof. firstorder. Qed.

  Lemma preimage_domain {A B} (f : A ⇒ B) : f⁻¹(B) =s A.
  Proof.
    split.
    - firstorder.
    - intros x H.
      split; try assumption.
      apply (projT2 f).
      apply Im_def.
      assumption.
  Qed.

  Lemma preimage_intersect_domain {A B} (f : A ⇒ B) Y : f⁻¹(Y) ∩ A =s f⁻¹(Y).
  Proof.
    split; intros ? H.
    - destruct H; assumption.
    - constructor.
      + assumption.
      + apply (preimage_subset_domain f Y).
        assumption.
  Qed.

  Lemma preimage_dist_intersection {A B} (f : A ⇒ B) X Y :
    f⁻¹(X) ∩ f⁻¹(Y) =s f⁻¹(X ∩ Y).
  Proof.
    split.
    - intros _ [u [uA fuX] [_ fuY]].
      split; [ | constructor ]; assumption.
    - intros u [uA fuXY].
      inversion fuXY.
      constructor; split; assumption.
  Qed.

  Lemma preimage_filter_property {A B F X Y} (f : A ⇒ B) :
    Filter A F → f⁻¹(X ∩ Y) ∈ F ↔ f⁻¹(X) ∈ F ∧ f⁻¹(Y) ∈ F.
  Proof.
    intros filterF.
    set (Dist := preimage_dist_intersection f X Y).
    specialize (Ensembles.Extensionality_Ensembles _ _ _ Dist) as DistEq.
    rewrite <- DistEq.
    apply (filter_closed _ _ filterF); apply preimage_subset_domain.
  Qed.

  (* A function is continuous if the preimage of open sets are open *)
  Definition continuous {A B} (f : A ⇒ B) (F G : Ensemble (Ensemble U)) : Type :=
    ∀ Y, Y ∈ G → f⁻¹(Y) ∈ F.

  Definition mapping_filter {A B} (f : A ⇒ B) (F : Ensemble (Ensemble U)) : Ensemble (Ensemble U) :=
    λ X, X ⊆ B ∧ f⁻¹(X) ∈ F.

  Lemma mapping_filter_continuous {A B} F (f : A ⇒ B) :
    continuous f F (mapping_filter f F).
  Proof.
    intros Y [YB fYF].
    assumption.
  Qed.

  Lemma mapping_filter_inhabited {A B F} (f : A ⇒ B) :
    Filter A F →
    Inhabited _ (mapping_filter f F).
  Proof.
    intros filterF.
    exists B.
    set (has_top := filter_contains_top filterF).
    destruct filterF as [inhabited subset closed].
    split; [ firstorder | ].
    rewrite (Extensionality_Ensembles _ _ _ (preimage_domain f)).
    assumption.
  Qed.

  Lemma mapping_filter_filter {A B F} (f : A ⇒ B) :
    Filter A F →
    Filter B (mapping_filter f F).
  Proof.
    intros filterF.
    destruct filterF as [inhabited subsets closed] eqn:E.
    constructor.
    - exists B.
      split; [ firstorder | ].
      rewrite (Extensionality_Ensembles _ _ _ (preimage_domain f)).
      apply (filter_contains_top filterF).
    - firstorder.
    - intros X Y XB YB.
      set (Dist := Extensionality_Ensembles _ _ _ (preimage_dist_intersection f X Y)).
      unfold mapping_filter, Ensembles.In.
      rewrite <- Dist.
      split.
      + intros.
        destruct H.
        split; split.
        * assumption.
        * rewrite (filter_closed _ _ filterF f⁻¹(X) f⁻¹(Y)) in H0;
          firstorder.
        * assumption.
        * rewrite (filter_closed _ _ filterF f⁻¹(X) f⁻¹(Y)) in H0;
          firstorder.
      + intros.
        destruct H.
        split.
        * intros u uXY.
          destruct uXY.
          firstorder.
        * rewrite (filter_closed _ _ filterF f⁻¹(X) f⁻¹(Y));
          firstorder.
  Defined.

  Definition Morphism (A B : Ensemble U) (F G : Ensemble (Ensemble U)) : Type :=
    { f : A ⇒ B & G ⊆ mapping_filter f F }.

  Definition id_setfun (A : Ensemble U) : A ⇒ A.
  Proof.
    exists (λ x, x).
    intros x H.
    destruct H; subst; assumption.
  Defined.

  Definition id {A F} (filterF : Filter A F) : Morphism A A F F.
  Proof.
    eexists (id_setfun A).
    intros X XF.
    split.
    - apply (filter_subsets _ _ filterF); assumption.
    - assert ((id_setfun A)⁻¹(X) = X).
      {
        apply Extensionality_Ensembles; firstorder.
      }
      rewrite H; assumption.
  Defined.

  Definition compose {A B C F G H} `(Filter A F) `(Filter B G) `(Filter C H)
    (f : Morphism A B F G) (g : Morphism B C G H) : Morphism A C F H.
  Proof.
    set (hfun := λ a, projT1 g (projT1 f a)).
    destruct f as [f Hf]; destruct g as [g Hg].
    assert (hfun_dom : hfun[A] ⊆ C).
    { 
      unfold hfun.
      simpl.
      unfold mapping_filter in Hf, Hg.
      set (projT2 f); simpl in *.
      set (projT2 g); simpl in *.
      intros x xIm.
      destruct xIm; subst.
      assert (f x ∈ B). { apply (projT2 f). apply Im_def. assumption. }
      apply (projT2 g).
      eapply Im_intro.
      eassumption.
      reflexivity.
    }
    set (h := existT (λ h, h[A] ⊆ C) hfun hfun_dom).
    exists h.
  Admitted.

End Filters.

Section NatFilters.

  Variable k : nat.

  Definition U := Vector.t nat k.

  Inductive obj : Type :=
    | obj_intro
        (A : Ensemble U)
        (F : Ensemble (Ensemble U))
        (filterF : Filter _ A F) : obj.

  Definition mor (X Y : obj) : Type :=
    let 'obj_intro A F filterF := X in
    let 'obj_intro B G filterG := Y in
    Morphism _ A B F G.

  Definition terminal : obj :=
    obj_intro
      (Singleton _ (Vector.const 0 k))
      (simple U (Singleton U (Vector.const 0 k)))
      (simple_filter U _).

End NatFilters.


