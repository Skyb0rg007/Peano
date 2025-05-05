
(* Sets *)
Definition Ensemble (A : Type) := A -> Prop.

Definition Full_set {A : Type} : Ensemble A := fun _ => True.

Definition Empty_set {A : Type} : Ensemble A := fun _ => False.

Definition Intersection {A} (P Q : Ensemble A) : Ensemble A :=
  fun x => P x /\ Q x.

Definition Included {A} (P Q : Ensemble A) : Prop :=
  forall x, P x -> Q x.

Definition Inhabited {A} (P : Ensemble A) :=
  exists x, P x.

Definition Same_set {A} (P Q : Ensemble A) : Prop :=
  Included P Q /\ Included Q P.

(* Filters *)
Class Filter {A : Type} (F : Ensemble (Ensemble A)) := {
  filter_true : F Full_set;
  filter_and : forall P Q, F P -> F Q -> F (Intersection P Q);
  filter_imp : forall P Q, Included P Q -> F P -> F Q;
}.

Class ProperFilter {A} (F : (A -> Prop) -> Prop) := {
  filter_ex : forall P, F P -> Inhabited P;
  filter_filter :: Filter F;
}.

Lemma filter_respects {A} {F : Ensemble (Ensemble A)} {FF : Filter F} :
  forall P Q, Same_set P Q -> F P <-> F Q.
Proof.
  intros P Q [PQ QP].
  split; apply filter_imp; assumption.
Qed.

Lemma filter_forall {A F} {FF : Filter F} (P : A -> Prop) :
  (forall x, P x) -> F P.
Proof.
  intros H.
  apply filter_imp with Full_set.
  - do 2 intro; apply H.
  - apply filter_true.
Qed.

Lemma filter_not_empty {A} {F : Ensemble (Ensemble A)} {PF : ProperFilter F} : ~ F Empty_set.
Proof.
  intros FE.
  destruct (filter_ex Empty_set FE) as [? H].
  destruct H.
Qed.

Lemma filter_const {A} {F : Ensemble (Ensemble A)} {FF : ProperFilter F} :
  forall P, F (fun _ => P) -> P.
Proof.
  intros P H.
  destruct (filter_ex (fun _ => P) H); assumption.
Qed.

Definition filter_le {A} (F G : Ensemble (Ensemble A)) : Prop :=
  Included G F.

Lemma filter_le_refl {A} (F : Ensemble (Ensemble A)) : filter_le F F.
Proof.
  hnf; trivial.
Qed.

Lemma filter_le_trans {A} (F G H : Ensemble (Ensemble A)) :
  filter_le F G -> filter_le G H -> filter_le F H.
Proof.
  firstorder.
Qed.

Definition filtermap {A B} (f : A -> B) (F : Ensemble (Ensemble A)) : Ensemble (Ensemble B) :=
  fun P => F (fun x => P (f x)).

Global Instance filtermap_filter {A B} (f : A -> B) F (FF : Filter F) : Filter (filtermap f F).
Proof.
  unfold filtermap.
  constructor.
  - apply filter_forall; constructor.
  - intros P Q FPf FQf.
    set (Pf := fun x => P (f x)); fold Pf in FPf.
    set (Qf := fun x => Q (f x)); fold Qf in FQf.
    apply filter_imp with (Intersection Pf Qf).
    + hnf; intros; destruct H; constructor; assumption.
    + apply filter_and; assumption.
  - intros P Q PQ FPf.
    set (Pf := fun x => P (f x)); fold Pf in FPf.
    apply filter_imp with Pf.
    + hnf; intros; apply PQ; assumption.
    + assumption.
Qed.

Global Instance filtermap_proper_filter {A B} (f : A -> B) F (PF : ProperFilter F) : ProperFilter (filtermap f F).
Proof.
  constructor.
  - intros P FP.
    unfold filtermap in FP.
    destruct (filter_ex (fun x => P (f x)) FP) as [x H].
    exists (f x); assumption.
  - apply filtermap_filter, filter_filter.
Qed.

Definition universe {A} (F : Ensemble (Ensemble A)) : Ensemble A :=
  fun x => exists S, F S /\ S x.

Definition improper {A} (X : Ensemble A) : Ensemble (Ensemble A) :=
  fun P => Included X P.

Global Instance improper_filter {A} (X : Ensemble A) : Filter (improper X).
Proof.
  constructor.
  - constructor.
  - intros P Q XP XQ x xX.
    constructor; [apply XP|apply XQ]; assumption.
  - intros P Q PQ XP x xX.
    apply PQ, XP, xX.
Qed.

Global Instance improper_proper_filter {A} (X : Ensemble A) :
  Inhabited X -> ProperFilter (improper X).
Proof.
  constructor; [firstorder | apply improper_filter].
Qed.

Definition subset {A} (F : Ensemble (Ensemble A)) (dom : Ensemble A) :=
  fun P : Ensemble {x | dom x} => F (fun x => forall H : dom x, P (exist _ x H)).

Global Instance subset_filter {A} F (dom : Ensemble A) (FF : Filter F) : Filter (subset F dom).
Proof.
  constructor; unfold subset.
  - apply filter_imp with (P := Full_set).
    + constructor.
    + apply filter_true.
  - intros P Q subP subQ; hnf.
    set (f x := forall H, P (exist _ x H)); fold f in subP.
    set (g x := forall H, Q (exist _ x H)); fold g in subQ.
    apply filter_imp with (P := Intersection f g).
    + intros x [xf xg] H1.
      constructor; [apply xf | apply xg].
    + apply filter_and; assumption.
  - intros P Q PQ.
    apply filter_imp.
    firstorder.
Qed.

Global Instance subset_proper_filter {A} F (dom : Ensemble A) (PF : ProperFilter F) :
  (forall P, F P -> Inhabited (Intersection dom P))
  -> ProperFilter (subset F dom).
Proof.
  intros Inh.
  constructor.
  - intros P subP.
    destruct (Inh _ subP) as [x H1].
    destruct H1 as [H1 H2].
    exists (exist _ x H1).
    apply H2.
  - apply subset_filter, filter_filter.
Qed.

