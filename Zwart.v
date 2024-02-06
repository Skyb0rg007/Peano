Require Import Coq.Arith.Cantor.
(* Require Import Coq.Logic.FunctionalExtensionality. *)
(* Require Import Coq.Logic.PropExtensionality. *)
Require Import Coq.Sets.Ensembles.
(* Require Import Coq.Sets.Finite_sets. *)
Require Import Coq.Sets.Image.
(* Require Import Coq.Sets.Infinite_sets. *)
(* Require Import Coq.Sets.Integers. *)
Require Import Lia.

Arguments Add {_} _ _ _ : assert.
Arguments Empty_set {_} _ : assert.
Arguments Finite {_} _ : assert.
Arguments Im {_ _} _ _ _ : assert.
Arguments In {_} _ _ : assert.
Arguments Included {_} _ _ : assert.
Arguments Inhabited {_} _ : assert.
Arguments Intersection {_} _ _ _ : assert.
Arguments Same_set {_} _ _ : assert.
Arguments Singleton {_} _ _ : assert.
Arguments Subtract {_} _ _ _ : assert.
Arguments Union {_} _ _ _ : assert.

(* Objects: All subsets of the natural numbers
   XXX: Currently implemented using (nat → Prop),
        could this work using (nat → bool)?
        ie. all computable subsets of ℕ *)
Definition obj := Ensemble nat.

(* Given f : d → c, its inverse image is bounded if:
   ∀N∈c, ∃M∈d, ∀m∈d, m > M ⇒ f m > N

   NOTE: this differs from the paper, since otherwise transitivity doesn't hold
   I think Zwart just mixed up > and ≥, but maybe I'm wrong.
 *)
Definition inverse_images_bounded d c (f : nat -> nat) : Prop :=
  forall N, In c N -> exists M, In d M /\ forall m, In d m -> m > M -> f m > N.

Definition bounded (s : Ensemble nat) : Prop :=
  exists N, forall n, In s n -> n <= N.

Definition unbounded (s : Ensemble nat) : Prop :=
  forall N, exists n, In s n /\ n > N.

Definition preimage d c (f : nat -> nat) : Ensemble nat :=
  fun n => In d n /\ In c (f n).

Lemma bounded_not_unbounded (s : Ensemble nat) : bounded s -> ~ unbounded s.
Proof.
  intros [N Nbound] UB.
  destruct (UB N) as [n [sn nN]].
  pose proof (Nbound n sn).
  apply Nat.lt_nge in nN.
  contradiction.
Qed.

Lemma finite_bounded (s : Ensemble nat) : Finite s -> bounded s.
Proof.
  intros fin.
  induction fin as [|s sfin [N Nbound] n ndisj].
  - exists O.
    intros ? H.
    destruct H.
  - exists (Nat.max n N).
    intros m Hm.
    inversion Hm; subst.
    + apply Nat.le_trans with (m := N).
      * apply Nbound; assumption.
      * apply Nat.le_max_r.
    + inversion H; subst.
      apply Nat.le_max_l.
Qed.

Lemma bounded_decidable_finite (s : Ensemble nat) :
  (forall n, In s n \/ ~ In s n) -> bounded s -> Finite s.
Proof.
  intros dec [N Nbound].
  generalize dependent s.
  induction N; intros s dec Nbound.
  - destruct (dec 0).
    + replace s with (Singleton 0).
      apply Singleton_is_finite.
      apply Extensionality_Ensembles.
      split.
      * intros x sx; inversion sx; assumption.
      * intros x sx; pose proof (Nbound x sx) as H1; inversion H1; constructor.
    + replace s with (@Empty_set nat).
      apply Empty_is_finite.
      apply Extensionality_Ensembles.
      split.
      * do 2 intro; contradiction.
      * intros x sx; pose proof (Nbound x sx) as H1; inversion H1; subst; contradiction.
  - destruct (dec (S N)).
    + replace s with (Add (Subtract s (S N)) (S N)).
      apply Union_is_finite.
      apply IHN.
      * intros n; destruct (dec n); [destruct (Nat.eq_dec n (S N))|].
        right; intros C; inversion C; subst; apply C; constructor.
        left; split; [assumption|]; intros C; inversion C; subst; contradiction.
        right; intros C; inversion C; contradiction.
      * intros n [sn nN].
        assert (NE : n <> S N) by (intros C; subst; apply nN; constructor).
        pose proof (Nbound n sn) as LE.
        inversion LE; subst; [contradiction|assumption].
      * intros H1; inversion H1; apply H2; constructor.
      * apply Extensionality_Ensembles; split.
        -- do 2 intro.
           inversion H0; subst.
           inversion H1; assumption.
           inversion H1; assumption.
        -- intros x H0.
           destruct (Nat.eq_dec x (S N)); subst.
           apply Union_intror; constructor.
           apply Union_introl.
           split; [assumption|].
           intro C; inversion C; subst; contradiction.
    + apply IHN; [assumption|].
      intros n sn.
      destruct (Nat.eq_dec n (S N)).
      subst; contradiction.
      pose proof (Nbound n sn).
      inversion H0; [contradiction|assumption].
Qed.

(* f : d → c
   For any nonempty bounded subset S ⊆ c, f⁻¹(S) is bounded *)
Definition inverse_images_bounded' d c (f : nat -> nat) : Prop :=
  forall S, Included S c -> Inhabited S -> bounded S ->
    bounded (preimage d S f).

(* Lemma iib_rewrite d c f : *)
(*   Included (Im d f) c -> *)
(*   Inhabited d -> *)
(*   inverse_images_bounded' d c f -> *)
(*   forall N, exists M, forall m, In d m -> f m < N -> m < M. *)
(* Proof. *)
(*   intros dom [x xd] iib N. *)
(*   unfold inverse_images_bounded' in iib. *)
(*   pose proof (dom (f x) (Im_intro nat nat d f x xd (f x) eq_refl)). *)
(*   pose proof (iib (Im d f) dom (Inhabited_intro nat (Im d f) (f x) (Im_intro _ _ _ _ _ xd _ eq_refl))). *)
(* Qed. *)

Lemma iib_from d c f : Inhabited d -> inverse_images_bounded' d c f -> inverse_images_bounded d c f.
Proof.
  intros [q qd] iib N cN.
  unfold inverse_images_bounded, inverse_images_bounded' in *.
  assert (SNc : Included (Singleton N) c).
  {
    intros x H; inversion H; subst; assumption.
  }
  assert (SNb : bounded (Singleton N)).
  {
    exists N.
    intros n H; inversion H; constructor.
  }
Admitted.

Lemma iib_to d c f : inverse_images_bounded d c f -> inverse_images_bounded' d c f.
Proof.
  intros iib S Sc [q qS] [N Nbounds].
  unfold inverse_images_bounded in iib.
  destruct (iib q (Sc q qS)) as [M [dM Mbounds]].
  unfold preimage.
  eexists M.
  intros n [? ?].
  destruct (Nat.le_gt_cases n M); try assumption.
  exfalso.
  unfold gt in Mbounds.
  set (Mbounds n H H1).
  set (Nbounds (f n) H0).
  set (Nbounds q qS).
Admitted.

(* Morphisms: A morphism between two objects d,c ∈ P(ℕ) is
 *  an equivalence class of functions f : d → c such that:
 *     ∀ N ∈ c, ∃ M ∈ d, ∀ m ∈ d [ m > M → f m > N ]
 * (inverse images of bounded sets are bounded)
 * Note: this is changed from the text, which has "f m ≥ N". I believe that was a typo.
 *)
Definition mor (d c : Ensemble nat) : Type :=
  { f : nat -> nat | Included (Im d f) c /\ inverse_images_bounded d c f }.

(* Two morphisms are considered equivalent if:
 *     ∃ N, ∀ n ≥ N [ n ∈ d → f(n) = g(n) ]
 * (f and g differ only on a bounded set)
 *)
Definition mor_equiv {d c} (f g : mor d c) : Prop :=
  exists N, forall n, n >= N -> In d n -> proj1_sig f n = proj1_sig g n.

(** mor_equiv forms an equivalence class (reflexive, symmetric, transitive) **)

Lemma mor_equiv_refl {d c} (f : mor d c) : mor_equiv f f.
Proof.
  exists 0; reflexivity.
Qed.

Lemma mor_equiv_sym {d c} (f g : mor d c) : mor_equiv f g -> mor_equiv g f.
Proof.
  intros [N E].
  exists N.
  symmetry.
  apply E; assumption.
Qed.

Lemma mor_equiv_trans {d c} (f g h : mor d c) :
  mor_equiv f g -> mor_equiv g h -> mor_equiv f h.
Proof.
  intros [N E1] [M E2].
  exists (Nat.max N M).
  intros n nNM dn.
  rewrite (E1 n (Nat.max_lub_l N M n nNM) dn).
  apply (E2 n (Nat.max_lub_r N M n nNM) dn).
Qed.

Lemma id_iib {c} : inverse_images_bounded c c (fun n : nat => n).
Proof.
  intros N ?.
  exists N.
  split; trivial.
Qed.

Lemma id_dom {c} : Included (Im c (fun n : nat => n)) c.
Proof.
  intros ? H.
  destruct H.
  subst; assumption.
Qed.

(* Identity morphisms *)
Definition id c : mor c c := exist _ (fun n : nat => n) (conj id_dom id_iib).

Lemma comp_dom {d c b} (f g : nat -> nat) :
  Included (Im d f) c ->
  Included (Im c g) b ->
  Included (Im d (Basics.compose g f)) b.
Proof.
  intros fdom gdom ? [? ?]; subst.
  apply gdom.
  econstructor; [apply fdom|reflexivity].
  econstructor; [apply H|reflexivity].
Qed.

Lemma comp_iib {d c b} (f g : nat -> nat) :
  Included (Im d f) c ->
  Included (Im c g) b ->
  inverse_images_bounded d c f ->
  inverse_images_bounded c b g ->
  inverse_images_bounded d b (Basics.compose g f).
Proof.
  unfold inverse_images_bounded in *.
  intros fdom gdom fiib giib N bN.
  destruct (giib N bN) as [M [cM H1]].
  destruct (fiib M cM) as [L [dL H2]].
  exists L.
  split; [assumption|].
  intros m dm mL.
  unfold Basics.compose.
  apply H1.
  - apply fdom.
    econstructor; [eassumption|reflexivity].
  - apply H2; assumption.
Qed.

(* Composition of morphisms *)
Definition comp {d c b} (f : mor d c) (g : mor c b) : mor d b :=
  let '(exist _ f' (conj fdom fiib)) := f in
  let '(exist _ g' (conj gdom giib)) := g in
  let dom := comp_dom f' g' fdom gdom in
  let iib := comp_iib f' g' fdom gdom fiib giib in
  exist _ (Basics.compose g' f') (conj dom iib).

(** Category laws **)

(* ∀f, id∘f = f *)
Lemma comp_id_left {d c} (f : mor d c) :
  mor_equiv (comp (id d) f) f.
Proof.
  destruct f as [? [? ?]].
  exists 0.
  reflexivity.
Qed.

(* ∀f, f∘id = f *)
Lemma comp_id_right {d c} (f : mor d c) :
  mor_equiv f (comp (id d) f).
Proof.
  destruct f as [? [? ?]].
  exists 0.
  reflexivity.
Qed.

(* ∀fgh, f∘(g∘h) = (f∘g)∘h *)
Lemma comp_assoc {d c b a} (f : mor d c) (g : mor c b) (h : mor b a) :
  mor_equiv (comp f (comp g h)) (comp (comp f g) h).
Proof.
  destruct f as [? [? ?]].
  destruct g as [? [? ?]].
  destruct h as [? [? ?]].
  exists 0.
  reflexivity.
Qed.

(* Covering families: A family of morphisms S is covering c iff there are
 *  d₁, ‥, dₖ ∈ P(ℕ) and [fᵢ] : dᵢ → c ∈ S such that for all M₁,‥,Mₖ:
 *      ∃ N, ∀ n ≥ N, ∃ i ≤ k, ∃ m ∈ dᵢ [ n ∈ c → (m ≥ Mᵢ ∧ fᵢ(m) = n) ]
 * (the elements of c that are not included in the union of the images
 *  form a bounded set, and the described cofinite requirement holds)
 *)
(* TODO: Define covering families *)

(* Proposition 4.0.1. All pullbacks exist in P(ℕ). *)
Section Pullbacks.
  Context {d1 d2 c : obj}.
  Context (f : mor d1 c) (g : mor d2 c).

  (* Use Cantor's pairing function to code ℕ × ℕ ≃ ℕ *)

  (* pullback = { (n, m) | n ∈ d1, m ∈ d2, f n = g m } *)
  Inductive pullback : obj :=
    Pullback_intro p n m :
      In d1 n ->
      In d2 m ->
      proj1_sig f n = proj1_sig g m ->
      p = Cantor.to_nat (n, m) ->
      In pullback p.

  (* π₁ : pullback → d1 *)
  Definition pi1_fun p := fst (Cantor.of_nat p).

  (* π₁ : pullback → d2 *)
  Definition pi2_fun p := snd (Cantor.of_nat p).

  Lemma pi1_dom : Included (Im pullback pi1_fun) d1.
  Proof.
    unfold pi1_fun.
    intros ? pPB.
    destruct pPB as [p pPB q H3]; subst.
    replace p with (Cantor.to_nat (Cantor.of_nat p)) in pPB
      by apply Cantor.cancel_to_of.
    set (p' := Cantor.of_nat p); fold p' in pPB.
    destruct p' as [n m].
    simpl.
    clear p.
    inversion pPB; subst; clear pPB.
    apply Cantor.to_nat_inj in H2.
    inversion H2; subst; clear H2.
    assumption.
  Qed.

  Lemma pi2_dom : Included (Im pullback pi2_fun) d2.
  Proof.
    unfold pi2_fun.
    intros ? pPB.
    destruct pPB as [p pPB q H3]; subst.
    replace p with (Cantor.to_nat (Cantor.of_nat p)) in pPB
      by apply Cantor.cancel_to_of.
    set (p' := Cantor.of_nat p); fold p' in pPB.
    destruct p' as [n m].
    simpl.
    clear p.
    inversion pPB; subst; clear pPB.
    apply Cantor.to_nat_inj in H2.
    inversion H2; subst; clear H2.
    assumption.
  Qed.

  Lemma cantor_strict_monotonic_l x1 x2 y : Cantor.to_nat (x1, y) < Cantor.to_nat (x2, y) -> x1 < x2.
  Proof.
    pose proof (to_nat_spec x1 y).
    pose proof (to_nat_spec x2 y).
    nia.
  Qed.

  Lemma cantor_strict_monotonic_r x y1 y2 : Cantor.to_nat (x, y1) < Cantor.to_nat (x, y2) -> y1 < y2.
  Proof.
    pose proof (to_nat_spec x y1).
    pose proof (to_nat_spec x y2).
    nia.
  Qed.

  Lemma cantor_strict_monotonic_spec x1 y1 x2 y2 :
    Cantor.to_nat (x1, y1) <= Cantor.to_nat (x2, y2) ->
    {x1 <= x2} + {y1 <= y2}.
  Proof.
    intros H.
    destruct (Compare_dec.le_gt_dec x1 x2) as [xLt | xGt]; [left; assumption|].
    destruct (Compare_dec.le_gt_dec y1 y2) as [yLt | yGt]; [right; assumption|].
    pose proof (to_nat_spec x1 y1).
    pose proof (to_nat_spec x2 y2).
    nia.
  Qed.

  Lemma cantor_maximum (n m : nat) : { '(N, M) & forall N' M', Cantor.to_nat (N', M') >= Cantor.to_nat (N, M) -> N' > n /\ M' > m }.
  Proof.
    eexists (1 + n * n * m * m, 1 + n * n * m * m).
    intros N' M' H.
    unfold gt, ge in H.

    pose proof (to_nat_spec N' M').
    pose proof (to_nat_spec (1 + n * n * m * m) (1 + n * n * m * m)).
    (* split. *)
    (* - nia. *)
    (* set (Cantor.to_nat_non_decreasing). *)
    (* set (Nat.le_trans _ _ _ (Cantor.to_nat_non_decreasing _ _) H). *)
    (* set (Cantor.to_nat_non_decreasing N' M'). *)
    (* nia. *)

    (* Cantor *)
    (* unfold to_nat in l0. *)
    (* simpl in l0. *)
  Admitted.

  Lemma pi1_iib : inverse_images_bounded pullback d1 pi1_fun.
  Proof.
    intros n0 d1n0.
    assert (m : nat) by admit.
    assert (d2m : In d2 m) by admit.
    assert (fngm : proj1_sig f n0 = proj1_sig g m) by admit.
    exists (Cantor.to_nat (n0, m)).
    split.
    - econstructor; try eassumption; reflexivity.
    - intros x xPB xGt.
      inversion xPB; subst; clear xPB;
        rename m0 into m';
        rename H into d1n;
        rename H0 into d2m';
        rename H1 into fngm'.
      unfold pi1_fun.
      rewrite Cantor.cancel_of_to; simpl.
    (* destruct f as [f' [fdom fiib]] eqn:Ef. *)
    (* destruct g as [g' [gdom giib]] eqn:Eg. *)
    (* unfold inverse_images_bounded in fiib, giib. *)
    (* set (fN := proj1_sig f N). *)
    (* assert (cfN : In c fN). *)
    (* { *)
    (*   apply (proj1 (proj2_sig f)), Im_intro with (x := N); *)
    (*   trivial. *)
    (* } *)
    (* destruct (proj2 (proj2_sig f) fN cfN) as [M1 [d1M1 H1]]. *)
    (* destruct (proj2 (proj2_sig g) fN cfN) as [M2 [d2M2 H2]]. *)
    (* assert (proj1_sig f M1 = proj1_sig g M2). *)
    (* { *)
    (*   admit. *)
    (* } *)
    (* set (M := Cantor.to_nat (M1, M2)). *)
    (* assert (forall m, In pullback m -> m > M -> pi1_fun m > N). *)

    (* exists M. *)
    (* split. *)
    (* - econstructor. *)
  Admitted.

End Pullbacks.
