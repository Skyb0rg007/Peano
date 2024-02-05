Require Import Coq.Arith.Cantor.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.
Require Import Coq.Sets.Image.
Require Import Coq.Sets.Infinite_sets.
Require Import Coq.Sets.Integers.
Require Import Coq.Unicode.Utf8.

Notation "∅" := (Empty_set _).
Notation "x ∈ A" := (Ensembles.In _ A x) (at level 50, no associativity).
Notation "A ⊆ B" := (Ensembles.Included _ A B) (at level 50, no associativity).
Notation "A ∩ B" := (Ensembles.Intersection _ A B) (at level 40, left associativity).
Notation "A ∪ B" := (Ensembles.Union _ A B) (at level 50, left associativity).
Notation "A =s B" := (Ensembles.Same_set _ A B) (at level 95, no associativity).
Notation "f [ A ]" := (Image.Im _ _ A f) (at level 1, A at level 99, format "f [ A ]").
Notation "∀ ( x ∈ S ) , P" := (∀ x, x ∈ S → P) (at level 200, right associativity, x binder).
Notation "∀ ( x ⊆ S ) , P" := (∀ x, x ⊆ S → P) (at level 200, right associativity, x binder).
Notation "∀ ( x ≥ N ) , P" := (∀ x, x ≥ N → P) (at level 200, right associativity, x binder).
Notation "∃ ( x ∈ S ) , P" := (∃ x, x ∈ S ∧ P) (at level 200, right associativity, x binder).

Definition bounded (S : Ensemble nat) : Prop :=
  ∃ N, ∀(n ∈ S), n ≤ N.

Definition unbounded (S : Ensemble nat) : Prop :=
  ∀ N, ∃(M ∈ S), M > N.

Lemma bounded_not_unbounded {S} : bounded S → ¬ unbounded S.
Proof.
  intros [N H1] H2.
  destruct (H2 N) as [x [xInS xGtN]].
  destruct (H1 x xInS) as [|y xLty].
  - apply (Nat.lt_irrefl x xGtN).
  - apply Le.le_Sn_le_stt in xGtN.
    apply Nat.le_ngt in xLty.
    contradiction.
Qed.

Lemma bounded_subset {A B} : bounded A → B ⊆ A → bounded B.
Proof.
  intros [N NboundsA] BsubA.
  exists N.
  intros n nInB.
  apply NboundsA, BsubA, nInB.
Qed.

Definition obj : Type := Ensemble nat.

Inductive preimage {A B} (X : Ensemble A) (f : A → B) (Y : Ensemble B) : Ensemble A :=
  | Preimage_intro (x : A) : x ∈ X → f x ∈ Y → x ∈ preimage X f Y.

Lemma preimage_equiv {X Y} (f : nat → nat) (P : nat → Prop) :
  (∀(x ∈ preimage X f Y), P x) ↔ (∀(x ∈ X), f x ∈ Y → P x).
Proof.
  split.
  - intros H x xX Px.
    apply H.
    constructor; assumption.
  - intros H _ [x xX fxY].
    apply H; assumption.
Qed.

Definition inverse_image_bounded (d c : obj) (f : nat → nat) : Prop :=
  ∀(A ⊆ c), bounded A → bounded (preimage d f A).

Definition inverse_image_bounded' (d c : obj) (f : nat → nat) : Prop :=
  ∀(N ∈ c), ∃(M ∈ d), ∀(m ∈ d), m > M → f m ≥ N.

Definition mor (d c : obj) : Type :=
  { f : nat → nat | f[d] ⊆ c ∧ inverse_image_bounded d c f }.

Lemma iib_compat {A B : obj} (f : nat → nat) (fdom : f[A] ⊆ B) :
  inverse_image_bounded' A B f → inverse_image_bounded A B f.
Proof.
  unfold inverse_image_bounded, inverse_image_bounded'.
  intros IIB.
  intros X XB [N NboundsX].
  set (IIB N )

  split.
  - intros IIB N Nc.
    (* unfold bounded in IIB. *)
    set (A := Singleton nat N).
    assert (Ac : A ⊆ c). { intros x xA; inversion xA; subst; assumption. }
    assert (Abounded : bounded A). { exists N; intros n nA; inversion nA; constructor. }
    destruct (IIB A Ac Abounded) as [M MboundsPre].
    eexists.
    split.
    2: {
      intros m md mM.
    }
    unfold preimage in MboundsPre.
Qed.

Definition mor_app {d c} (f : mor d c) : nat → nat := proj1_sig f.

Definition mor_eq {d c} (f g : mor d c) : Prop :=
  ∃ N, ∀(n ≥ N), n ∈ d → mor_app f n = mor_app g n.

Definition pi1 p := fst (Cantor.of_nat p).

Definition pi2 p := snd (Cantor.of_nat p).

Definition pullback {d1 d2 c} (f : mor d1 c) (g : mor d2 c) : Ensemble nat :=
  λ p, pi1 p ∈ d1 ∧ pi2 p ∈ d2 ∧ mor_app f (pi1 p) = mor_app g (pi2 p).

Lemma pi1_dom {d1 d2 c} (f : mor d1 c) (g : mor d2 c) :
  pi1[pullback f g] ⊆ d1.
Proof.
  intros _ [p pPB]; subst.
  firstorder.
Qed.

Lemma pi1_inverse_image_bounded {d1 d2 c} (f : mor d1 c) (g : mor d2 c) :
  inverse_image_bounded (pullback f g) d1 pi1.
Proof.
  unfold inverse_image_bounded.
  intros e1 e1d1 [E1 E1boundse1].

  assert (∃ M, ∀(p ∈ pullback f g), pi1 p ∈ e1 → p ≤ M).
  2: {
    destruct H as [M H].
    exists M.
    intros _ [? ? ?]; apply H; assumption.
  }

  unfold pullback; unfold In at 1.

  set (fii := proj2 (proj2_sig f)); unfold inverse_image_bounded in fii.
  set (gii := proj2 (proj2_sig g)); unfold inverse_image_bounded in gii.
  unfold bounded in fii.

  assert (∀ (A ⊆ c), bounded A → ∃ N, ∀ (d ∈ d1), proj1_sig f d ∈ A → n ≤ N).
  rewrite preimage_equiv in fii.

  bounded (preimage X f Y) ↔ ∃ N, ∀ x ∈ X, f x ∈ Y → x ≤ N
Admitted.

  fold bounded.
  rewrite preimage_equiv.
  set (H1 := proj2_sig f); unfold inverse_image_bounded in H1.
  set (H2 := proj2_sig g); unfold inverse_image_bounded in H2.
  (*
     Equiv: need M : ℕ, st. p ≤ M if π₁(p) ∈ A , p ∈ pullback f g
                                    p ≅ (n, m), n ∈ A ∧ m ∈ 

     A ⊆ d1 is a bounded subset
     so by 
   *)
Admitted.

Lemma pi1_preimage_bounded {d1 d2 c} (f : mor d1 c) (g : mor d2 c) :
  ∀(n0 ∈ d1),
  bounded (preimage (pullback f g) pi1 (Singleton nat n0)).
Proof.
  intros n0 n0ind1.
  (* set (S := preimage (pullback f g) pi1 (Singleton nat n)). *)
  (* destruct f as [f [fdom fii]]; destruct g as [g [gdom gii]]. *)
  (* unfold inverse_image_bounded in fii, gii. *)

  (* A := π₁⁻¹(n0) *)
  set (A := λ p, pi1 p = n0 ∧ pi2 p ∈ d2 ∧ mor_app f (pi1 p) = mor_app g (pi2 p)).
  assert (A ⊆ pullback f g).
  {
    intros a aA.
    unfold pullback, In.
    unfold A, In in aA; simpl.
    destruct aA as [H1 [H2 H3]].
    split; [rewrite H1|split]; assumption.
  }
  assert (∀(a ∈ A), pi1 a = n0).
  {
    intros a aA.
    destruct aA; assumption.
  }

  set (gii := proj2_sig g); simpl in gii.
  unfold inverse_image_bounded in gii.

  set @bounded_subset.

  (* apply @bounded_subset with (A := preimage A pi1 (Singleton nat n0)). *)

  eexists.
  intros p ppre.
  destruct ppre as [p pPB pi1pn0].
  inversion pi1pn0; clear pi1pn0.
  destruct pPB as [pi1n0d1 [pi2n0d2 Eq]]; unfold mor_app, proj1_sig in Eq.
  destruct (Cantor.of_nat p) as [n m] eqn:E.
  assert (Cantor.to_nat (Cantor.of_nat p) = Cantor.to_nat (n, m)). { f_equal; assumption. }
  rewrite Cantor.cancel_to_of in H0.
  unfold pi1, pi2 in *.
  (* simpl in pi1n0d1, pi2n0d2, Eq, H. *)
  rewrite E in Eq; simpl in Eq.
  rewrite E in H; simpl in H.
  rewrite E in pi1n0d1, pi2n0d2; simpl in pi1n0d1, pi2n0d2.
  subst.
  clear n0ind1 E.

  set (gii f[d1] fdom).

  Cantor.to_nat
  simpl.
  clear E.

  unfold pi1, pi2 in pi1n0d1, pi2n0d2, Eq.

  inversion pi1pn0.
  simpl in *.
  rewrite Cantor.cancel_to_of in H.
  rewrite H.
Qed.

Lemma pi1_preimage {d1 d2 c} (f : mor d1 c) (g : mor d2 c) : inverse_image_bounded (pullback f g) d1 pi1.
Proof.
  intros e1 e1subd2 e1Bounded.
  destruct e1Bounded as [E1 e1BoundedE1].
  rename A into e1.
Qed.
Lemma pi1_preimage {d1 d2 c} (f : mor d1 c) (g : mor d2 c) : ∀(e1 ⊆ d1), bounded e1 → bounded (preimage (pullback f g) pi1 e1).

(* Definition inverse_image_bounded' (d c : obj) (f : nat -> nat) : Prop := *)
(*   ∀(N ∈ c), ∃(M ∈ d), ∀(m ∈ d), m > M → f m ≥ N. *)

(* 1. Choose an element of the domain N. We consider the bounded set { n ∈ c | n ≤ N }
 * 2. *)

Definition mor (d c : obj) : Type :=
  { f : nat → nat | f[d] ⊆ c ∧ inverse_image_bounded d c f }.

Definition mor_app {d c} (f : mor d c) : nat → nat := proj1_sig f.

Coercion mor_app : mor >-> Funclass.

Definition mor_eq {d c} (f g : mor d c) : Prop :=
  ∃ N, ∀(n ≥ N), n ∈ d → f n = g n.

Definition pullback {d1 d2 c} (f : mor d1 c) (g : mor d2 c) : Ensemble nat :=
  λ p,
    let '(n, m) := Cantor.of_nat p in
    n ∈ d1 ∧ m ∈ d2 ∧ f n = g m.

Definition pi1 p := fst (Cantor.of_nat p).
Definition pi2 p := snd (Cantor.of_nat p).

Lemma pi1_dom {d1 d2 c} (f : mor d1 c) (g : mor d2 c) :
  pi1[pullback f g] ⊆ d1.
Proof.
  intros _ [y H1]; subst.
  unfold pullback, In in H1; unfold pi1.
  destruct (Cantor.of_nat y); firstorder.
Qed.

Lemma pi2_dom {d1 d2 c} (f : mor d1 c) (g : mor d2 c) :
  pi2[pullback f g] ⊆ d2.
Proof.
  intros _ [y H1]; subst.
  unfold pullback, In in H1; unfold pi2.
  destruct (Cantor.of_nat y); firstorder.
Qed.

(* π₁ : pullback f g → d₁ *)
(* π₂ : pullback f g → d₂ *)

Lemma pi1_inv_img {d1 d2 c} (f : mor d1 c) (g : mor d2 c) :
  inverse_image_bounded (pullback f g) d1 pi1.
Proof.
  set (Dom := pi1_dom f g).
  destruct f as [f [H1 H2]].
  destruct g as [g [H3 H4]].
  unfold inverse_image_bounded in H2, H4; unfold inverse_image_bounded.
  intros N Nd1.
  set (fN := f N).
  assert (fNc : fN ∈ c).
  {
    apply H1.
    apply Im_intro with (x := N); trivial.
  }
  destruct (H4 fN fNc) as [M2 [M2d2 H5]].
  eexists (Cantor.to_nat (pair N M2)); split.
  - unfold pullback, In.
    rewrite Cantor.cancel_of_to.
    simpl.
    split; try split.
    + assumption. (* x1 ∈ d1 *)
    + assumption. (* x2 ∈ d2 *)
    + admit. (* f x1 = g x2 *)
  - intros m mPB mGt.
    set (Dom := pi1_dom f' g').

    unfold pullback, Included, In in Dom.

    unfold pullback, In in mPB.

    Im

    unfold pullback, In in mPB.
    destruct (of_nat m) as [x y] eqn:E.
    assert (Xpi1 : pi1 m = x).
    {
      unfold pi1; rewrite E; reflexivity.
    }
    assert (Xpi2 : pi2 m = y).
    {
      unfold pi2; rewrite E; reflexivity.
    }
    rewrite <- Xpi1 in mPB.
    rewrite <- Xpi2 in mPB.
    assert (x ∈ (λ p, let '(n, m) := of_nat p in d1 n ∧ d2 m ∧ f' n = g' m)).
    { admit. }
    set (Dom m).


  destruct (H2 fN fNc) as [M1 [M1d1 P1]].
  destruct (H4 fN fNc) as [M2 [M2d2 P2]].
  eexists (to_nat (pair N M2)).
  split.
  - unfold pullback, In.
    rewrite Cantor.cancel_of_to.
    unfold mor_app; simpl.
    split; [assumption | split]; [assumption |].


    unfold ge in P1, P2.
    (* f M1 = g M2 *)
    admit.
  - intros m H5 H6.
    unfold pullback in H5.
    unfold In at 1 in H5.
    unfold pi1.
    destruct (of_nat m).
    destruct H5 as [n0d1 [n1d2 H5]].
    inversion H5.
    unfold mor_app in H5; simpl in H5.
    Cantor
    simpl.




























(****************************************************************************)

(* Non-standard natural numbers *)
Definition ns_nat : Type := nat -> nat.

(* Ability to lift a relation on `nat` to a relation on `ns_nat`.
   The relation holds the non-standard naturals so long as there are
   finitely many exceptions, and those exceptions are members of `c`. *)
Inductive finite_exceptions (R : Relation nat) (c : Ensemble nat) f g : Prop :=
  Exceptions_intro (X : Ensemble nat) :
    Approximant nat c X ->
    (forall n, ~ R (f n) (g n) -> In nat X n) ->
    finite_exceptions R c f g.

Lemma exceptions_refl R :
  Reflexive nat R ->
  forall c, Reflexive ns_nat (finite_exceptions R c).
Proof.
  intros refl c x.
  apply Exceptions_intro with (X := Empty_set nat).
  - apply Defn_of_Approximant.
    + apply Empty_is_finite.
    + apply Included_Empty.
  - intros n H.
    pose (refl (x n)); contradiction.
Qed.

(* c ⊢ x = y *)
Definition ns_eq := finite_exceptions Nat.eq.

(* c ⊢ ∀x[x = x] *)
Definition ns_eq_refl := exceptions_refl Nat.eq Nat.eq_refl.

(* c ⊢ ∀x∀y[x = y → y = x] *)
Lemma ns_eq_sym c : Symmetric ns_nat (ns_eq c).
Proof.
  intros x y [X Approx except].
  apply Exceptions_intro with (X := X); try assumption.
  intros n H.
  apply except.
  intros C.
  pose (Nat.eq_sym C); contradiction.
Qed.

(* c ⊢ ∀x∀y∀z[x = y ∧ y = z → x = z] *)
Lemma ns_eq_trans c : Transitive ns_nat (ns_eq c).
Proof.
  intros x y z [X1 [? ?] except1] [X2 [? ?] except2].
  apply Exceptions_intro with (X := Union nat X1 X2).
  - apply Defn_of_Approximant.
    + apply Union_preserves_Finite; assumption.
    + apply Union_minimal; assumption.
  - intros n Ne.
    destruct (Nat.eq_dec (x n) (y n)) as [E | Ne2].
    + rewrite E in Ne.
      apply Union_intror, (except2 n Ne).
    + apply Union_introl, (except1 n Ne2).
Qed.

(* c ⊢ x ≤ y *)
Definition ns_le := finite_exceptions Nat.le.

(* c ⊢ ∀x[x ≤ x] *)
Definition ns_le_refl := exceptions_refl Nat.le Nat.le_refl.

(* c ⊢ ∀x∀y[x ≤ y ∧ y ≤ x → x = y] *)
Lemma ns_le_antisym c x y : ns_le c x y -> ns_le c y x -> ns_eq c x y.
Proof.
  intros [X1 [? ?] except1] [X2 [? ?] except2].
  apply Exceptions_intro with (X := Union nat X1 X2).
  - apply Defn_of_Approximant.
    + apply Union_preserves_Finite; assumption.
    + apply Union_minimal; assumption.
  - intros n Ne.
    destruct (Nat.compare_spec (x n) (y n)).
    + exfalso; apply Ne; assumption.
    + apply Union_intror, except2, Nat.nle_gt.
      assumption.
    + apply Union_introl, except1, Nat.nle_gt.
      assumption.
Qed.

(* c ⊢ ∀x∀y∀z[x ≤ y ∧ y ≤ z → x ≤ z] *)
Lemma ns_le_trans c : Transitive ns_nat (ns_le c).
Proof.
  intros x y z [X1 [? ?] except1] [X2 [? ?] except2].
  apply Exceptions_intro with (X := Union nat X1 X2).
  - apply Defn_of_Approximant.
    + apply Union_preserves_Finite; assumption.
    + apply Union_minimal; assumption.
  - intros n Ne.
    destruct (le_dec (x n) (y n)) as [E | Ne2].
    + rewrite E in Ne.
      apply Union_intror, (except2 n Ne).
    + apply Union_introl, (except1 n Ne2).
Qed.

(* *)

(* 0 is a term *)
Definition ns_zero : ns_nat := fun _ => O.

(* s(f) is a term *)
Definition ns_succ (f : ns_nat) : ns_nat :=
  fun n => S (f n).

(* c ⊢ ∀x[s(x) ≠ 0] *)
Lemma ns_succ_not_zero c f : ~ ns_eq c (ns_succ f) ns_zero.
Proof.
  intros [X [XFin XinC] except].
  assert (X = Integers).
  {
    apply Extensionality_Ensembles.
    split.
    - intros x H; constructor.
    - intros x H; apply except; intros Contra; inversion Contra.
  }
  apply Integers_infinite.
  rewrite <- H.
  assumption.
Qed.

(* c ⊢ ∀x∀y[x = y → s(x) = s(y)] *)
Lemma ns_succ_morphism c f g : ns_eq c f g -> ns_eq c (ns_succ f) (ns_succ g).
Proof.
  intros [X ? except].
  apply Exceptions_intro with (X := X).
  - assumption.
  - intros n SuccNe.
    apply except, Nat.succ_inj_wd_neg.
    assumption.
Qed.

(* c ⊢ ∀x∀y[s(x) = s(y) → x = y] *)
Lemma ns_succ_inj c f g : ns_eq c (ns_succ f) (ns_succ g) -> ns_eq c f g.
Proof.
  intros [X Approx except].
  apply Exceptions_intro with (X := X).
  - assumption.
  - intros n Ne.
    apply except, Nat.succ_inj_wd_neg.
    assumption.
Qed.

(* c ⊢ St(f) *)
Definition St (c : Ensemble nat) (f : ns_nat) : Prop :=
  Finite nat (Im nat nat c f).

(* Embedding of `nat` into `ns_nat` *)
Definition from_nat : nat -> ns_nat := fun n _ => n.

(* `from_nat` is injective *)
Lemma from_nat_injective c n m : ns_eq c (from_nat n) (from_nat m) -> n = m.
Proof.
  intros [X [XFin XInc] except].
  destruct (Nat.eq_dec n m) as [| Ne]; [ assumption | ].
  exfalso.
  assert (X = Integers).
  {
    apply Extensionality_Ensembles; split.
    - constructor.
    - do 2 intro; apply except; intro; contradiction.
  }
  apply Integers_infinite.
  rewrite <- H.
  assumption.
Qed.

(* `from_nat` preserves 0 *)
Lemma from_nat_zero c : ns_eq c ns_zero (from_nat O).
Proof. apply ns_eq_refl. Qed.

(* `from_nat` preserves successor *)
Lemma from_nat_succ c n : ns_eq c (ns_succ (from_nat n)) (from_nat (S n)).
Proof. apply ns_eq_refl. Qed.

Lemma nat_standard_succ n : ns_succ (from_nat n) = from_nat (S n).
Proof.
  induction n; [ | rewrite <- IHn ]; reflexivity.
Qed.

Lemma nat_standard c n : Inhabited nat c -> St c (from_nat n).
Proof.
  intros Inh.
  unfold St.
  replace (Im nat nat c (from_nat n)) with (Add nat (Empty_set nat) n).
  - constructor.
    + constructor.
    + apply Noone_in_empty.
  - apply Extensionality_Ensembles; split.
    + intros x H.
      inversion H; inversion H0; subst.
      destruct Inh as [y Inh].
      apply Im_intro with (x := y); trivial.
    + intros x H.
      destruct H; subst.
      do 2 constructor.
Qed.

(* c ⊢ f ≤ g *)
Inductive ns_leq (c : Ensemble nat) (f g : ns_nat) : Type := 
  Leq_exceptions (X : Ensemble nat) :
    Approximant nat c X ->
    (forall n, f n > g n -> In nat X n) ->
    ns_leq c f g.
  Finite _ (fun n => In nat c n /\ f n > g n).

Lemma ns_leq_refl c f : ns_leq c f f.
Proof.
  unfold ns_leq.
  replace (fun n => In nat c n /\ f n > f n) with (Empty_set nat).
  - apply Empty_is_finite.
  - apply Extensionality_Ensembles; split.
    + intros x H; inversion H.
    + intros x H; inversion H.
      pose (Nat.lt_irrefl (f x)).
      contradiction.
Qed.

Lemma ns_leq_antisym c f g : ns_leq c f g -> ns_leq c g f -> ns_equiv c f g.
Proof.
  intros Lfg Lgf.
  unfold ns_leq in Lfg, Lgf.

  apply Equiv_exceptions with (X := Union nat Lfg Lgf).
  ns_equiv
  constructor.
  2: {

  }
Qed.

  Antisymmetric

(* Definition Inf (c : Ensemble nat) (f : ns_nat) : Type := *)
