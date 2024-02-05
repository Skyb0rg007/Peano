Require Import Coq.Lists.List.

Module PA.
  Inductive var : Type := V : nat -> var.

  (* Terms of Peano Arithmetic *)
  Inductive term : Type :=
  | Var : var -> term
  | Zero : term
  | Succ : term -> term
  | Plus : term -> term -> term
  | Mult : term -> term -> term.

  Notation "'$' n" := (Var (V n)) (at level 35).
  Notation "'1+' n" := (Succ n) (at level 35).
  Notation "n '⊕' m" := (Plus n m) (at level 50).
  Notation "n '⊗' m" := (Mult n m) (at level 40).

  Fixpoint subst_term (s : var -> term) (t : term) : term :=
    match t with
    | Var v => s v
    | Zero => Zero
    | Succ t1 => Succ (subst_term s t1)
    | Plus t1 t2 => Plus (subst_term s t1) (subst_term s t2)
    | Mult t1 t2 => Mult (subst_term s t1) (subst_term s t2)
    end.

  Inductive formula : Type :=
  | False : formula
  | Impl : formula -> formula -> formula
  | Conj : formula -> formula -> formula
  | Disj : formula -> formula -> formula
  | Forall : formula -> formula
  | Exists : formula -> formula
  (* Predicates *)
  | Equal : term -> term -> formula.

  Notation "⊥" := (False).
  Notation "A → B" := (Impl A B) (at level 99, right associativity, B at level 200).
  Notation "A ∧ B" := (Conj A B) (at level 80, right associativity).
  Notation "A ∨ B" := (Disj A B) (at level 85, right associativity).
  Notation "∀ phi" := (Forall phi) (at level 50).
  Notation "∃ phi" := (Exists phi) (at level 50).
  Notation "t1 ≡ t2" := (Equal t1 t2) (at level 70, no associativity).
  Notation "¬ A" := (A → ⊥) (at level 75, right associativity).
  Notation "A ↔ B" := ((A → B) ∧ (B → A)) (at level 95, no associativity).
  Notation "t1 ≢ t2" := (¬ (t1 ≡ t2)) (at level 70, no associativity).

  Definition scons (x : term) (s : var -> term) : var -> term :=
    fun '(V n) =>
      match n with
      | O => x
      | S m => s (V m)
      end.

  Definition up (s : var -> term) : var -> term :=
    scons
      (Var (V O))
      (fun v => subst_term (fun '(V n) => Var (V (S n))) (s v)).

  Fixpoint subst_form (s : var -> term) (phi : formula) : formula :=
    match phi with
    | ⊥ => ⊥
    | phi1 → phi2 => (subst_form s phi1) → (subst_form s phi2)
    | phi1 ∧ phi2 => (subst_form s phi1) ∧ (subst_form s phi2)
    | phi1 ∨ phi2 => (subst_form s phi1) ∨ (subst_form s phi2)
    | ∀ phi1 => ∀ (subst_form (up s) phi1)
    | ∃ phi1 => ∃ (subst_form (up s) phi1)
    | t1 ≡ t2 => (subst_term s t1) ≡ (subst_term s t2)
    end.

  Definition shift := subst_form (fun '(V n) => Var (V (S n))).

  Definition subst phi t := subst_form (scons t Var) phi.

  Reserved Notation "G ⊢ phi" (at level 100).

  Inductive nd : list formula -> formula -> Type :=
    | Proj {Γ φ} : List.In φ Γ -> Γ ⊢ φ
    | FalseElim {Γ φ} : (Γ ⊢ ⊥) -> Γ ⊢ φ
    | ImplIntro {Γ φ ψ} : (φ :: Γ ⊢ ψ) -> Γ ⊢ φ → ψ
    | ImplElim {Γ φ ψ} : (Γ ⊢ φ → ψ) -> (Γ ⊢ φ) -> Γ ⊢ ψ
    | ConjIntro {Γ φ ψ} : (Γ ⊢ φ) -> (Γ ⊢ ψ) -> Γ ⊢ φ ∧ ψ
    | ConjElim1 {Γ φ ψ} : (Γ ⊢ φ ∧ ψ) -> Γ ⊢ φ
    | ConjElim2 {Γ φ ψ} : (Γ ⊢ φ ∧ ψ) -> Γ ⊢ ψ
    | DisjIntro1 {Γ φ ψ} : (Γ ⊢ φ) -> Γ ⊢ φ ∨ ψ
    | DisjIntro2 {Γ φ ψ} : (Γ ⊢ ψ) -> Γ ⊢ φ ∨ ψ
    | DisjElim {Γ φ ψ θ} : (Γ ⊢ φ ∨ ψ) -> (φ :: Γ ⊢ θ) -> (ψ :: Γ ⊢ θ) -> Γ ⊢ θ
    | ForallIntro {Γ φ} : (List.map shift Γ ⊢ φ) -> Γ ⊢ ∀ φ
    | ForallElim {Γ φ} t : (Γ ⊢ ∀ φ) -> Γ ⊢ subst φ t
    | ExistsIntro {Γ φ} t : (Γ ⊢ subst φ t) -> Γ ⊢ ∃ φ
    | ExistsElim {Γ φ ψ} : (Γ ⊢ ∃ φ) -> (φ :: List.map shift Γ ⊢ shift ψ) -> Γ ⊢ ψ

    (** Axioms **)
    (* Equality *)
    | EqRefl {Γ} : Γ ⊢ ∀ ($0 ≡ $0)
    | EqSym {Γ} : Γ ⊢ ∀∀ ($0 ≡ $1 → $1 ≡ $0)
    | EqTrans {Γ} : Γ ⊢ ∀∀∀ ($0 ≡ $1 ∧ $1 ≡ $2 → $0 ≡ $2)
    | SuccCong {Γ} : Γ ⊢ ∀∀ ($0 ≡ $1) → (1+ $0) ≡ (1+ $1)
    | PlusCong {Γ} : Γ ⊢ ∀∀∀∀ ($0 ≡ $1) → ($2 ≡ $3) → ($0 ⊕ $2 ≡ $1 ⊕ $3)
    | MultCong {Γ} : Γ ⊢ ∀∀∀∀ ($0 ≡ $1) → ($2 ≡ $3) → ($0 ⊗ $2 ≡ $1 ⊗ $3)
    (* Successor *)
    | ZeroNotSucc {Γ} : Γ ⊢ ∀ (Zero ≢ 1+ $0)
    | SuccInj {Γ} : Γ ⊢ ∀∀ ((1+ $0) ≡ (1+ $1) → $0 ≡ $1)
    (* Addition *)
    | PlusZero {Γ} : Γ ⊢ ∀ ($0 ⊕ Zero ≡ $0)
    | PlusSucc {Γ} : Γ ⊢ ∀∀ (($0 ⊕ 1+ $1) ≡ 1+ ($0 ⊕ $1))
    (* Multiplication *)
    | MultZero {Γ} : Γ ⊢ ∀ ($0 ⊗ Zero ≡ Zero)
    | MultSucc {Γ} : Γ ⊢ ∀∀ (($0 ⊗ 1+ $1) ≡ (($0 ⊗ $1) ⊕ $0))
    (* Induction *)
    | Induction {Γ} φ : Γ ⊢ ((subst φ Zero) ∧ (∀ φ → subst φ (1+ $0))) → ∀ φ
  where "G ⊢ phi" := (nd G phi).

  Notation "⊢ phi" := (nil ⊢ phi) (at level 50).

  Fixpoint interpret_term (Γ : list nat) (t : term) : nat :=
    match t with
    | Var (V n) => List.nth n Γ 0
    | Zero => 0
    | 1+ n => S (interpret_term Γ n)
    | n ⊕ m => interpret_term Γ n + interpret_term Γ m
    | n ⊗ m => interpret_term Γ n * interpret_term Γ m
    end.

  Fixpoint interpret_form (Γ : list nat) (f : formula) : Type :=
    match f with
    | False => Empty_set
    | A → B => interpret_form Γ A -> interpret_form Γ B
    | A ∧ B => interpret_form Γ A * interpret_form Γ B
    | A ∨ B => interpret_form Γ A + interpret_form Γ B
    | ∀ A => forall n : nat, interpret_form (n :: Γ) A
    | ∃ A => { n : nat & interpret_form (n :: Γ) A }
    | A ≡ B => interpret_term Γ A = interpret_term Γ B
    end.


  Lemma zero_lident : ⊢ ∀ (Zero ⊕ $0 ≡ $0).
  Proof.
    apply (ImplElim (Induction _)); unfold subst; simpl.
    apply ConjIntro.
    - exact (ForallElim Zero PlusZero).
    - exact (ImplIntro (ForallElim (1+ $0) (Proj (in_eq (∀ (Zero ⊕ $0 ≡ $0)) nil)))).
  Qed.

  Definition zero_lident' : ⊢ ∀ (Zero ⊕ $0 ≡ $0) :=
    ImplElim
      (Induction (Zero ⊕ $0 ≡ $0))
      (ConjIntro
        (ForallElim Zero PlusZero)
        (ImplIntro
          (ForallElim (1+ $0) (Proj (in_eq (∀ (Zero ⊕ $0 ≡ $0)) nil))))).

  Lemma plus_comm : ⊢ ∀∀ ($0 ⊕ $1 ≡ $1 ⊕ $0).
  Proof.
    apply ForallIntro; simpl.
    apply (ImplElim (Induction _)).
    unfold subst; simpl.
    apply ConjIntro.
    - 
      remember (@ForallElim nil _ (Zero ⊕ $0) (ForallElim ($0) (ForallElim ($0 ⊕ Zero) EqTrans))).
      remember ((ConjIntro (ForallElim ($0) zero_lident') (ImplElim (ForallElim ($0 ⊕ Zero) (ForallElim ($0) EqSym)) (ForallElim ($0) PlusZero)))) in n.
      exact (ImplElim n n0).
    - apply ImplIntro.
  Admitted.

  Definition mult_id : formula := ∀ ($0 ⊗ 1+ Zero ≡ $0).

  Lemma mult_id_proof : ⊢ ∀ ($0 ⊗ 1+ Zero ≡ $0).
  Proof.
    apply ForallIntro; simpl.
    (* remember (@MultSucc nil). *)
    remember (@ForallElim nil _ ($0) (ForallElim Zero MultSucc)).
    simpl in n; unfold subst in n; simpl in n.
    assert (⊢ (($0 ⊗ Zero ⊕ $0) ≡ (Zero ⊕ $0))).
    (* assert (mult_succ : Γ ⊢ axiom_mult_succ). *)
    (* { apply Proj. do 8 right. left. reflexivity. } *)
    unfold axiom_mult_succ in mult_succ.
    assert (PA_axioms ⊢ $0 ⊗ 1+ Zero ≡ $0 ⊗ Zero ⊕ $0).
    { exact (ForallElim ($0) (ForallElim Zero mult_succ)). }
    assert (PA_axioms ⊢ $0 ⊗ Zero ⊕ $0 ≡ Zero ⊕ $0).
    simpl.
    fold PA_axioms.
  Defined.

  Definition example1 : formula :=
    1+ Zero ⊕ 1+ Zero ≡ 1+ 1+ Zero.

  Compute (ForallElim Zero plus_succ).
  Compute (subst (∀ ($0 ⊕ 1+ ($1) ≡ 1+ ($0 ⊕ $1))) Zero).
  Compute (subst ($0 ⊕ 1+ Zero ≡ 1+ ($0 ⊕ Zero)) (1+ Zero)).

  Lemma proof1 : nd PA_axioms example1.
  Proof.
    assert (plus_succ : nd PA_axioms axiom_plus_succ).
    {
      apply Proj.
      do 6 right; left.
      reflexivity.
    }
    assert (nd PA_axioms (1+ Zero ⊕ 1+ Zero ≡ 1+ (1+ Zero))).
    {
      exact (ForallElim (1+ Zero) (ForallElim Zero plus_succ)).
    }

    (* S O + S O = S (S O). *)

    (* S O + O = S O *)

    (* S (S O + O) = S (S O) *)

    (* S O + S O = S (S O + O) *)

    constructor.

  Lemma even_or_odd : forall n, (exists m, m + m = n) \/ (exists m, S (m + m) = n).
  Proof.
    intro n.
    induction n.
    - left.
      exists O.
      reflexivity.
    - destruct IHn as [[m H] | [m H]].
      + right.
        exists m.
        f_equal.
        exact H.
      + left.
        exists (S m).
        rewrite <- plus_n_Sm.
        f_equal.
        simpl.
        exact H.
  Qed.

  Lemma consistent : ~ (nil ⊢ ⊥).
  Proof.
  Admitted.

  (* Fixpoint traverse_term (f : nat -> var -> term) (l : nat) (t : term) : term := *)
  (*   match t with *)
  (*   | Var x => f l x *)
  (*   | Zero => Zero *)
  (*   | Succ t1 => Succ (traverse_term f l t1) *)
  (*   | Plus t1 t2 => Plus (traverse_term f l t1) (traverse_term f l t2) *)
  (*   | Mult t1 t2 => Mult (traverse_term f l t1) (traverse_term f l t2) *)
  (*   end. *)

  (* Fixpoint traverse_form (f : nat -> var -> term) (l : nat) (t : formula) : formula := *)
  (*   match t with *)
  (*   | False => False *)
  (*   | Impl t1 t2 => Impl (traverse_form f l t1) (traverse_form f l t2) *)
  (*   | Conj t1 t2 => Conj (traverse_form f l t1) (traverse_form f l t2) *)
  (*   | Disj t1 t2 => Disj (traverse_form f l t1) (traverse_form f l t2) *)
  (*   | Forall t1 => Forall (traverse_form f (S l) t1) *)
  (*   | Exists t1 => Forall (traverse_form f (S l) t1) *)
  (*   | Equ t1 t2 => Equ (traverse_term f l t1) (traverse_term f l t2) *)
  (*   end. *)

  (* Definition lift_var : nat -> nat -> var -> var := *)
  (*   fun w k '(V x) => *)
  (*     if Nat.leb k x *)
  (*       then V (w + x) *)
  (*       else V x. *)

  (* Definition lift_term : nat -> nat -> term -> term := *)
  (*   fun w k t => *)
  (*     traverse_term (fun l x => Var (lift_var w (l + k) x)) 0 t. *)

  (* Definition lift_form : nat -> nat -> formula -> formula := *)
  (*   fun w k t => *)
  (*     traverse_form (fun l x => Var (lift_var w (l + k) x)) 0 t. *)

  (* Definition closed : nat -> formula -> Type := *)
  (*   fun k t => lift_form 1 k t = t. *)

  (* Definition subst_var : term -> var -> var -> term := *)
  (*   fun v '(V k) '(V x) => *)
  (*     match Nat.compare x k with *)
  (*     | Lt => Var (V x) *)
  (*     | Eq => v *)
  (*     | Gt => Var (V (x - 1)) *)
  (*     end. *)

  (* Definition ex1 : formula := *)
  (*   Forall (Exists (Equ (Var (V 0)) (Var (V 1)))). *)

  (* Compute (closed 0 ex1). *)

  (* Lemma lift_resp_var w k x : lift_term w k (Var x) = Var (lift_var w k x). *)
  (* Proof. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* Lemma lift_term_zero k t : lift_term 0 k t = t. *)
  (* Proof. *)
  (*   induction t; unfold lift_term, lift_var; simpl. *)
  (*   - destruct v as [n]; destruct (Nat.leb k n); reflexivity. *)
  (*   - reflexivity. *)
  (*   - f_equal; apply IHt. *)
  (*   - f_equal; [apply IHt1 | apply IHt2]. *)
  (*   - f_equal; [apply IHt1 | apply IHt2]. *)
  (* Qed. *)

  (* Lemma lift_form_zero k t : lift_form 0 k t = t. *)
  (* Proof. *)
  (*   induction t. *)
  (*   - reflexivity. *)
  (*   - unfold lift_form; simpl; f_equal; [apply IHt1 | apply IHt2]. *)
  (*   - unfold lift_form; simpl; f_equal; [apply IHt1 | apply IHt2]. *)
  (*   - unfold lift_form; simpl; f_equal; [apply IHt1 | apply IHt2]. *)
  (*   - unfold lift_form; simpl; f_equal. *)
  (*     unfold lift_form in IHt. *)
  (*     unfold traverse_form. *)
  (* Admitted. *)

  (* Lemma lift_term_injective w k t1 t2 : lift_term w k t1 = lift_term w k t2 -> t1 = t2. *)
  (* Proof. *)
  (* Admitted. *)

  (* Fixpoint subst_term (s : nat -> term) (t : term) : term := *)
  (*   match t with *)
  (*   | Var x => s x *)
  (*   | Zero => Zero *)
  (*   | Succ x => Succ (subst_term s x) *)
  (*   | Plus x y => Plus (subst_term s x) (subst_term s y) *)
  (*   | Mult x y => Mult (subst_term s x) (subst_term s y) *)
  (*   end. *)

  (* Definition up (s : nat -> term) : nat -> term := *)
  (*   fun n => *)
  (*     match n with *)
  (*     | O => Var 0 *)
  (*     | S m => subst_term (fun r => Var (S r)) (s m) *)
  (*     end. *)

  (* Fixpoint subst_formula (s : nat -> term) (t : formula) : formula := *)
  (*   match t with *)
  (*   | False => False *)
  (*   | Impl x y => Impl (subst_formula s x) (subst_formula s y) *)
  (*   | Conj x y => Conj (subst_formula s x) (subst_formula s y) *)
  (*   | Disj x y => Disj (subst_formula s x) (subst_formula s y) *)
  (*   | Forall x => Forall (subst_formula (up s) x) *)
  (*   | Exists x => Exists (subst_formula (up s) x) *)
  (*   | Eq x y => Eq (subst_term s x) (subst_term s y) *)
  (*   end. *)

  (* Definition shift : formula -> formula := *)
  (*   subst_formula (fun n => Var (S n)). *)

  (* Definition subst : formula -> term -> formula := *)
  (*   fun f t => *)
  (*     subst_formula (fun n => match n with O => t | S m => Var m end) f. *)

  (* Inductive nd : list formula -> formula -> Type := *)
  (* | ImplIntro {G x y} : nd (x :: G) y -> nd G (Impl x y) *)
  (* | ImplElim {G x y} : nd G (Impl x y) -> nd G x -> nd G y *)
  (* | ForallIntro {G x} : nd (map shift G) x -> nd G (Forall x) *)
  (* | ForallElim {G x t} : nd G (Forall x) -> nd G (subst x t) *)
  (* | ExistsIntro {G x t} : nd G (subst x t) -> nd G (Exists x) *)
  (* | ExistsElim {G x y} : nd G (Exists x) -> nd (x :: map shift G) (shift y) -> nd G y *)
  (* | ConjIntro {G x y} : nd G x -> nd G y -> nd G (Conj x y) *)
  (* | ConjElim1 {G x y} : nd G (Conj x y) -> nd G x *)
  (* | ConjElim2 {G x y} : nd G (Conj x y) -> nd G y *)
  (* | DisjIntro1 {G x y} : nd G x -> nd G (Disj x y) *)
  (* | DisjIntro2 {G x y} : nd G y -> nd G (Disj x y) *)
  (* | DisjElim {G x y z} : nd G (Disj x y) -> nd (x :: G) z -> nd (y :: G) z -> nd G z *)
  (* | CtxProj {G x} : nd (x :: G) x *)
  (* | CtxWeak {G x y} : nd G x -> nd (y :: G) x *)
  (* . *)

  (* Class interp (Dom : Type) := { *)
  (*   zero : Dom; *)
  (*   succ : Dom -> Dom; *)
  (*   plus : Dom -> Dom -> Dom; *)
  (*   mult : Dom -> Dom -> Dom; *)
  (*   equ : Dom -> Dom -> Prop; *)
  (* }. *)

  (* Fixpoint eval {Dom} `{interp Dom} (rho : nat -> Dom) (t : term) : Dom := *)
  (*   match t with *)
  (*   | Var s => rho s *)
  (*   | Zero => zero *)
  (*   | Succ t' => succ (eval rho t') *)
  (*   | Plus t1 t2 => plus (eval rho t1) (eval rho t2) *)
  (*   | Mult t1 t2 => mult (eval rho t1) (eval rho t2) *)
  (*   end. *)

  (* Fixpoint sat {Dom} `{interp Dom} (rho : nat -> Dom) (t : formula) : Set := *)
  (*   match t with *)
  (*   | False => Empty_set *)
  (*   | Impl x y => sat rho x -> sat rho y *)
  (*   | Conj x y => and (sat rho x) (sat rho y) *)
  (*   | Disj x y => or (sat rho x) (sat rho y) *)
  (*   | Forall x => forall d : Dom, sat () *)
  (*   | Exists x => Exists (subst_formula (up s) x) *)
  (*   | Eq x y => Eq (subst_term s x) (subst_term s y) *)
  (*   | Eq t1 t2 => eq (eval rho t1) (eval rho t2) *)
  (*   end. *)
End PA.
