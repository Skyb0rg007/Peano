
Require Import Coq.Lists.List.

Inductive term : Type :=
  | Var : nat -> term
  | Zero : term
  | Succ : term -> term
  | Plus : term -> term -> term
  | Mult : term -> term -> term.

Inductive form : Type :=
  | Forall : form -> form
  | Exists : form -> form
  | Conj : form -> form -> form
  | Disj : form -> form -> form
  | Impl : form -> form -> form
  | False : form
  | Eq : term -> term -> form.

Declare Scope PA_syntax.
Delimit Scope PA_syntax with PA.
Notation "'∀' φ" := (Forall φ) (at level 50) : PA_syntax.
Notation "'∃' φ" := (Exists φ) (at level 50) : PA_syntax.
Notation "φ '∧' ψ" := (Conj φ ψ) (at level 41) : PA_syntax.
Notation "φ '∨' ψ" := (Disj φ ψ) (at level 42) : PA_syntax.
Notation "φ '→' ψ" := (Impl φ ψ) (at level 43, right associativity) : PA_syntax.
Notation "'⊥'" := (False) : PA_syntax.
Notation "'¬' φ" := (Impl φ False) (at level 42) : PA_syntax.
Notation "t1 '==' t2" := (Eq t1 t2) (at level 40) : PA_syntax.
Notation "'$' x" := (Var x) (at level 3, format "$ x") : PA_syntax.
Notation "x '⊕' y" := (Plus x y) (at level 39) : PA_syntax.
Notation "x '⊗' y" := (Mult x y) (at level 38) : PA_syntax.
Notation "'S' '(' x ')'" := (Succ x) (format "S ( x )") : PA_syntax.
Notation "'0'" := (Zero) : PA_syntax.

Open Scope PA_syntax.

Reserved Notation "t '[' s ']'" (at level 7, left associativity, format "t [ s ]").
Reserved Notation "f '`[' s ']'" (at level 7, left associativity, format "f `[ s ]").

Fixpoint subst_term (σ : nat -> term) (t : term) : term :=
  match t with
  | $ n => σ n
  | 0 => 0
  | S(x) => S(x`[σ])
  | a ⊕ b => a`[σ] ⊕ b`[σ]
  | a ⊗ b => a`[σ] ⊗ b`[σ]
  end
where "t '`[' s ']'" := (subst_term s t).

Definition lift_term : term -> term :=
  subst_term (fun v => $ (S v)).

(* Adds a term for $0, shifting the other substitutions *)
Definition scons {A} (t : A) (σ : nat -> A) (n : nat) : A :=
  match n with
  | O => t
  | S m => σ m
  end.

Definition up (σ : nat -> term) : nat -> term :=
  scons (Var O) (fun n => (σ n)`[fun v => $ (S v)]).

Fixpoint subst_form (σ : nat -> term) (phi : form) : form :=
  match phi with
  | ∀ φ => ∀ φ[up σ]
  | ∃ φ => ∃ φ[up σ]
  | φ₁ ∧ φ₂ => φ₁[σ] ∧ φ₂[σ]
  | φ₁ ∨ φ₂ => φ₁[σ] ∨ φ₂[σ]
  | φ₁ → φ₂ => φ₁[σ] → φ₂[σ]
  | ⊥ => ⊥
  | x == y => x`[σ] == y`[σ]
  end
where "f '[' s ']'" := (subst_form s f).

Definition lift : form -> form :=
  subst_form (fun v => $ (S v)).

Notation "phi '[' '/' t ']'" :=
  (subst_form (scons t Var) phi) (at level 7, left associativity).

(* ∀x, x == x *)
Definition ax_eq_refl : form :=
  ∀ $0 == $0.

(* ∀x,y, x == y → y == x *)
Definition ax_eq_sym : form :=
  ∀∀ $1 == $0 → $0 == $1.

(* ∀x,y,z, x == y ∧ y == z → x == z *)
Definition ax_eq_trans : form :=
  ∀∀∀ $2 == $1 ∧ $1 == $0 → $2 == $0.

(* ∀x,y, x == y → S(x) == S(y) *)
Definition ax_cong_succ : form :=
  ∀∀ $1 == $0 → S($1) == S($0).

(* ∀x,y,z,w, x == y ∧ z == w → x + z == y + w *)
Definition ax_cong_plus : form :=
  ∀∀∀∀ $3 == $2 ∧ $1 == $0 → $3 ⊕ $1 == $2 ⊕ $0.

(* ∀x,y,z,w, x == y ∧ z == w → x + z == y + w *)
Definition ax_cong_mult : form :=
  ∀∀∀∀ $3 == $2 ∧ $1 == $0 → $3 ⊗ $1 == $2 ⊗ $0.

(* ∀x, 0 ≠ S(x) *)
Definition ax_zero_succ : form :=
  ∀ ¬(0 == S($0)).

(* ∀x,y, (S(x) == S(y)) → x == y *)
Definition ax_succ_inj : form :=
  ∀∀ (S($1) == S($0)) → $1 == $0.

(* ∀x, x + 0 == x *)
Definition ax_plus_zero : form :=
  ∀ ($0 ⊕ 0 == $0).

(* ∀x,y, x + S(y) == S(x + y) *)
Definition ax_plus_succ : form :=
  ∀∀ ($1 ⊕ S($0) == S($1 ⊕ $0)).

(* ∀x, x⋅0 == 0 *)
Definition ax_mult_zero : form :=
  ∀ ($0 ⊗ 0 == 0).

(* ∀x,y, x⋅S(y) == x⋅y + x *)
Definition ax_mult_succ : form :=
  ∀∀ ($1 ⊗ S($0) == $1 ⊗ $0 ⊕ $1).

(* φ(0) ∧ ∀x, [φ(x) → φ(S(x))] → ∀x, φ(x) *)
Definition ax_induction (φ : form) : form :=
  φ[/0] ∧ (∀ φ → φ[scons (S($0)) (fun n => Var (S n))]) →
  ∀ φ.

Inductive axiom : form -> Type :=
  | EqRefl : axiom ax_eq_refl
  | EqSym : axiom ax_eq_sym
  | EqTrans : axiom ax_eq_trans
  | EqCongSucc : axiom ax_cong_succ
  | EqCongPlus : axiom ax_cong_plus
  | EqCongMult : axiom ax_cong_mult
  | ZeroSucc : axiom ax_zero_succ
  | SuccInj : axiom ax_succ_inj
  | PlusZero : axiom ax_plus_zero
  | PlusSucc : axiom ax_plus_succ
  | MultZero : axiom ax_mult_zero
  | MultSucc : axiom ax_mult_succ
  | Induction φ : axiom (ax_induction φ).

Reserved Notation "Γ '⊢' φ" (at level 61).
Inductive proof : list form -> form -> Type :=
  | Context {Γ φ} : List.In φ Γ -> Γ ⊢ φ
  | PAAxiom {Γ φ} : axiom φ -> Γ ⊢ φ
  | ImplIntro {Γ φ ψ} : (φ :: Γ) ⊢ ψ -> Γ ⊢ φ → ψ
  | ImplElim {Γ φ ψ} : Γ ⊢ φ → ψ -> Γ ⊢ φ -> Γ ⊢ ψ
  | ForallIntro {Γ φ} : List.map lift Γ ⊢ φ -> Γ ⊢ ∀ φ
  | ForallElim {Γ φ} t : Γ ⊢ ∀ φ -> Γ ⊢ φ[/t]
  | ExistsIntro {Γ φ} t : Γ ⊢ φ[/t] -> Γ ⊢ ∃ φ
  | ExistsElim {Γ φ ψ} : Γ ⊢ ∃ φ -> φ :: List.map lift Γ ⊢ lift ψ -> Γ ⊢ ψ
  | FalseElim {Γ φ} : Γ ⊢ ⊥ -> Γ ⊢ φ
  | ConjIntro {Γ φ ψ} : Γ ⊢ φ -> Γ ⊢ ψ -> Γ ⊢ φ ∧ ψ
  | ConjElim1 {Γ φ ψ} : Γ ⊢ φ ∧ ψ -> Γ ⊢ φ
  | ConjElim2 {Γ φ ψ} : Γ ⊢ φ ∧ ψ -> Γ ⊢ ψ
  | DisjIntro1 {Γ φ ψ} : Γ ⊢ φ -> Γ ⊢ φ ∨ ψ
  | DisjIntro2 {Γ φ ψ} : Γ ⊢ ψ -> Γ ⊢ φ ∨ ψ
  | DisjElim {Γ φ ψ θ} : Γ ⊢ φ ∨ ψ -> φ :: Γ ⊢ θ -> ψ :: Γ ⊢ θ -> Γ ⊢ θ
where "Γ ⊢ φ" := (proof Γ φ) : PA_syntax.

Notation "'⊢' φ" := (proof List.nil φ) (at level 61) : PA_syntax.

Module TarskiModel.

  Variable domain : Type.
  Variable zero : domain.
  Variable succ : domain -> domain.
  Variable add : domain -> domain -> domain.
  Variable mul : domain -> domain -> domain.

  Fixpoint eval (ρ : nat -> domain) (t : term) : domain :=
    match t with
    | $n => ρ n
    | 0 => zero
    | S(t) => succ (eval ρ t)
    | t₁ ⊕ t₂ => add (eval ρ t₁) (eval ρ t₂)
    | t₁ ⊗ t₂ => mul (eval ρ t₁) (eval ρ t₂)
    end.

  Fixpoint satisfies (ρ : nat -> domain) (φ : form) : Prop :=
    match φ with
    | ∀ φ => forall d, satisfies (scons d ρ) φ
    | ∃ φ => exists d, satisfies (scons d ρ) φ
    | φ ∧ ψ => satisfies ρ φ /\ satisfies ρ ψ
    | φ ∨ ψ => satisfies ρ φ \/ satisfies ρ ψ
    | φ → ψ => satisfies ρ φ -> satisfies ρ ψ
    | ⊥ => Logic.False
    | t₁ == t₂ => eval ρ t₁ = eval ρ t₂
    end.

  Definition valid φ := forall ρ, satisfies ρ φ.
  Definition valid_ctx Γ φ := forall ρ, List.Forall (satisfies ρ) Γ -> satisfies ρ φ.
  Definition satisfiable φ := exists ρ, satisfies ρ φ.

End TarskiModel.

Module KripkeModel.

  (* Interpretation *)
  Variable domain : Type.
  Variable zero : domain.
  Variable succ : domain -> domain.
  Variable add : domain -> domain -> domain.
  Variable mul : domain -> domain -> domain.

  (* Reachability *)
  Variable nodes : Type.
  Variable reachable : nodes -> nodes -> Prop.
  Variable reachable_refl : forall u, reachable u u.
  Variable reachable_trans : forall u v w, reachable u v -> reachable v w -> reachable u w.

  (* Predicates *)
  Variable zeroP : nodes -> Prop.
  Variable succP : nodes -> domain -> Prop.
  Variable addP : nodes -> domain -> domain -> Prop.
  Variable mulP : nodes -> domain -> domain -> Prop.

  (* Monotonic *)
  Variable zeroMonoP : forall u v, reachable u v -> zeroP u -> zeroP v.
  Variable succMonoP : forall u v x, reachable u v -> succP u x -> succP v x.
  Variable addMonoP : forall u v x y, reachable u v -> addP u x y -> addP v x y.
  Variable mulMonoP : forall u v x y, reachable u v -> mulP u x y -> mulP v x y.

  Fixpoint eval (ρ : nat -> domain) (t : term) : domain :=
    match t with
    | $n => ρ n
    | 0 => zero
    | S(t) => succ (eval ρ t)
    | t₁ ⊕ t₂ => add (eval ρ t₁) (eval ρ t₂)
    | t₁ ⊗ t₂ => mul (eval ρ t₁) (eval ρ t₂)
    end.

  Fixpoint satisfies (u : nodes) (ρ : nat -> domain) (φ : form) : Prop :=
    match φ with
    | ∀ φ => forall d, satisfies u (scons d ρ) φ
    | ∃ φ => exists d, satisfies u (scons d ρ) φ
    | φ ∧ ψ => satisfies u ρ φ /\ satisfies u ρ ψ
    | φ ∨ ψ => satisfies u ρ φ \/ satisfies u ρ ψ
    | φ → ψ => forall v, reachable u v -> satisfies v ρ φ -> satisfies v ρ ψ
    | ⊥ => Logic.False
    | t₁ == t₂ => eval ρ t₁ = eval ρ t₂
    end.

End KripkeModel.

Fixpoint eval (ρ : nat -> nat) (t : term) : nat :=
  match t with
  | $n => ρ n
  | 0 => Nat.zero
  | S(t) => Nat.succ (eval ρ t)
  | t₁ ⊕ t₂ => Nat.add (eval ρ t₁) (eval ρ t₂)
  | t₁ ⊗ t₂ => Nat.mul (eval ρ t₁) (eval ρ t₂)
  end.

Fixpoint satisfies (ρ : nat -> nat) (φ : form) : Prop :=
  match φ with
  | ∀ φ => forall d : nat, satisfies (scons d ρ) φ
  | ∃ φ => exists d : nat, satisfies (scons d ρ) φ
  | φ ∧ ψ => satisfies ρ φ /\ satisfies ρ ψ
  | φ ∨ ψ => satisfies ρ φ \/ satisfies ρ ψ
  | φ → ψ => satisfies ρ φ -> satisfies ρ ψ
  | ⊥ => Logic.False
  | t₁ == t₂ => eval ρ t₁ = eval ρ t₂
  end.

Definition valid φ := forall ρ, satisfies ρ φ.
Definition valid_ctx Γ φ := forall ρ, List.Forall (satisfies ρ) Γ -> satisfies ρ φ.
Definition satisfiable φ := exists ρ, satisfies ρ φ.

Lemma eval_ext ρ ξ φ : (forall x, ρ x = ξ x) -> eval ρ φ = eval ξ φ.
Proof. intros; induction φ; cbn; f_equal; easy. Qed.

Lemma eval_comp ρ ξ t : eval ρ t`[ξ] = eval (fun t => eval ρ (ξ t)) t.
Proof. induction t; cbn; f_equal; easy. Qed.

Lemma eval_lift ρ s t : eval (scons s ρ) (lift_term t) = eval ρ t.
Proof.
  unfold lift_term; rewrite eval_comp; apply eval_ext; reflexivity.
Qed.

Lemma satisfies_ext ρ ξ φ : (forall x, ρ x = ξ x) -> satisfies ρ φ <-> satisfies ξ φ.
Proof.
  generalize dependent ρ.
  generalize dependent ξ.
  induction φ; intros.
  - split; 
    intros H1 d; simpl in *; specialize (H1 d);
    eapply (IHφ _ _ _);
    eassumption;
    intros x; destruct x; simpl; easy.
  - split;
    intros [d H1]; simpl in *; exists d;
    eapply (IHφ _ _ _);
    eassumption.
  - split; intros [d H1]; simpl in *; split.
    + apply IHφ1 with (ρ := ρ); easy.
    + apply IHφ2 with (ρ := ρ); easy.
    + apply IHφ1 with (ρ := ξ); firstorder.
    + apply IHφ2 with (ρ := ξ); firstorder.
  - split; intros [H1|H1]; simpl in *.
    + left; eapply IHφ1; [symmetry; apply (H x) | assumption].
    + right; eapply IHφ2; [symmetry; apply (H x) | assumption].
    + left; eapply IHφ1; [apply H | assumption].
    + right; eapply IHφ2; [apply H | assumption].
  - split; intros H1 H2; simpl in *.
    eapply IHφ2; [symmetry; apply (H x) | apply H1 ];
    eapply IHφ1; eassumption.
    eapply IHφ2; [apply H | apply H1 ].
    eapply IHφ1; [symmetry; apply (H x)|assumption].
  - split; intro x; destruct x.
  - split; intro H1; simpl in *.
    + rewrite <- (eval_ext ρ ξ t H).
      rewrite <- (eval_ext ρ ξ t0 H).
      assumption.
    + rewrite -> (eval_ext ρ ξ t H).
      rewrite -> (eval_ext ρ ξ t0 H).
      assumption.
  Unshelve.
  all: intros x; destruct x; simpl; easy.
Qed.

Lemma satisfies_comp ρ ξ φ : satisfies ρ φ[ξ] <-> satisfies (fun x => eval ρ (ξ x)) φ.
Proof.
  generalize dependent ρ.
  generalize dependent ξ.
  induction φ; intros ξ ρ; cbn; f_equal; try easy; simpl in *.
  6: repeat rewrite eval_comp; reflexivity.
  3,4,5: rewrite IHφ1, IHφ2; reflexivity.
  2: {
    split; intros [d H1].
    - exists d.
      erewrite satisfies_ext.
      erewrite <- IHφ.
      apply H1.
      intros x; destruct x; simpl.
      + reflexivity.
      + rewrite eval_lift; reflexivity.
    - exists d.
      erewrite IHφ.
      erewrite satisfies_ext.
      apply H1.
      intros x; destruct x; simpl.
      + reflexivity.
      + rewrite eval_lift; reflexivity.
  }
  1: {
    split; intros H1 d.
    - erewrite satisfies_ext.
      rewrite <- IHφ.
      apply H1.
      intros x; destruct x.
      + reflexivity.
      + simpl; rewrite eval_lift; reflexivity.
    - erewrite IHφ.
      erewrite satisfies_ext.
      apply H1.
      intros x; destruct x.
      + reflexivity.
      + simpl; rewrite eval_lift; reflexivity.
  }
Qed.

Lemma axioms_valid φ : axiom φ -> valid φ.
Proof.
  unfold valid.
  intros A ρ; destruct A.
  - hnf; reflexivity.
  - repeat intro; symmetry; trivial.
  - intros ? y ? [? ?]; transitivity y; assumption.
  - repeat intro; simpl; f_equal; assumption.
  - intros ? ? ? ? [? ?]; simpl; f_equal; assumption.
  - intros ? ? ? ? [? ?]; simpl; f_equal; assumption.
  - intros ? H; inversion H.
  - intros ? ? H; inversion H; reflexivity.
  - hnf; apply PeanoNat.Nat.add_0_r.
  - repeat intro; apply PeanoNat.Nat.add_succ_r.
  - hnf; apply PeanoNat.Nat.mul_0_r.
  - repeat intro; apply PeanoNat.Nat.mul_succ_r.
  - simpl; intros [B IH] n.
    induction n.
    + rewrite satisfies_comp in B.
      rewrite satisfies_ext; [apply B|].
      intros x; destruct x; reflexivity.
    + set (H := IH n IHn).
      rewrite satisfies_ext, <- satisfies_comp.
      apply H.
      intros x; destruct x; try reflexivity.
Qed.

Lemma sound Γ φ : Γ ⊢ φ -> valid_ctx Γ φ.
Proof.
  induction 1; intros ρ HΓ.
  - rewrite Forall_forall in HΓ; now apply HΓ.
  - now apply axioms_valid.
  - intros Hφ.
    now apply IHproof, List.Forall_cons.
  - apply IHproof1; try assumption.
    now apply IHproof2.
  - simpl in *; intros d.
    apply IHproof, List.Forall_map, List.Forall_impl with (P := satisfies ρ).
    2: assumption.
    intros ψ Hψ.
    apply satisfies_comp, satisfies_ext with (ξ := ρ).
    2: assumption.
    reflexivity.
  - apply satisfies_comp.
    eapply satisfies_ext.
    2: apply IHproof; eassumption.
    intro x; destruct x; reflexivity.
  - exists (eval ρ t).
    eapply satisfies_ext.
    2: apply satisfies_comp, IHproof, HΓ.
    intros x; now destruct x.
  - destruct (IHproof1 ρ HΓ) as [d HD]; fold satisfies in HD.
    specialize (IHproof2 (scons d ρ)).
    unfold lift in IHproof2.
    erewrite satisfies_comp in IHproof2.
    apply IHproof2, List.Forall_cons.
    1: apply HD.
    eapply List.Forall_map, List.Forall_impl.
    2: eassumption.
    intros θ Hθ.
    eapply satisfies_comp, satisfies_ext.
    2: eassumption.
    reflexivity.
  - exfalso.
    apply IHproof with (ρ := ρ), HΓ.
  - split.
    + apply IHproof1, HΓ.
    + apply IHproof2, HΓ.
  - destruct (IHproof ρ HΓ); assumption.
  - destruct (IHproof ρ HΓ); assumption.
  - left; apply IHproof, HΓ.
  - right; apply IHproof, HΓ.
  - destruct (IHproof1 ρ HΓ); fold satisfies in *.
    + apply IHproof2, List.Forall_cons; assumption.
    + apply IHproof3, List.Forall_cons; assumption.
Qed.

Lemma consistent : ⊢ ⊥ -> Logic.False.
Proof.
  intros D.
  destruct (sound List.nil ⊥ D (fun n => n) (List.Forall_nil _)).
Qed.

(* ∃∞, ∀n, ∃m, ∞ = n + m *)
Definition non_standard : form := ∃ ∀ ∃ $2 == $1 ⊕ $0.

Lemma non_standard_unprovable : ⊢ non_standard -> Logic.False.
Proof.
  intros D.
  set (ρ (n : nat) := n).
  set (Γ := @List.nil form).
  set (HΓ := List.Forall_nil (satisfies ρ)).
  pose proof (sound _ _ D ρ HΓ) as H.
  destruct H as [inf H].
  specialize (H (S inf)).
  destruct H as [m H].
  simpl in H.
  rewrite PeanoNat.Nat.add_comm in H.
  now apply PeanoNat.Nat.succ_add_discr in H.
Qed.

Lemma non_standard_sound : non_standard :: List.nil ⊢ ⊥ -> Logic.False.
Proof.
Admitted.
(* Lemma sound Γ φ : Γ ⊢ φ -> valid_ctx Γ φ. *)

Definition one_plus_one : form := S(0) ⊕ S(0) == S(S(0)).

Lemma pr_one_plus_one : ⊢ one_plus_one.
Proof.
  pose proof (PAAxiom PlusSucc : ⊢ ax_plus_succ) as A1.
  pose proof (PAAxiom EqCongSucc : ⊢ ax_cong_succ) as A2.
  pose proof (PAAxiom EqTrans : ⊢ ax_eq_trans) as A3.
  pose proof (PAAxiom PlusZero : ⊢ ax_plus_zero) as A4.
  pose proof (ForallElim 0 (ForallElim S(0) A1)) as H1; simpl in *.
  pose proof (ImplElim (ForallElim S(0) (ForallElim (S(0) ⊕ 0) A2)) (ForallElim S(0) A4)) as H2; simpl in *.
  exact (ImplElim (ForallElim S(S(0)) (ForallElim S(S(0) ⊕ 0) (ForallElim (S(0) ⊕ S(0)) A3))) (ConjIntro H1 H2)).
Qed.

Lemma sat_one_plus_one : valid one_plus_one.
Proof. hnf; reflexivity. Qed.
