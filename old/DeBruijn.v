
Class Traverse (V T : Type) :=
  traverse : (nat -> nat -> V) -> nat -> T -> T.

Module Type Syntax.

  Axiom term : Type.
  Axiom var : nat -> term.

  Axiom traverse : (nat -> nat -> term) -> nat -> term -> term.

  Axiom traverse_injective :
    forall f,
    (forall x1 x2 l, f l x1 = f l x2 -> x1 = x2) ->
    forall t1 t2 l,
    traverse f l t1 = traverse f l t2 ->
    t1 = t2.

  Axiom traverse_relative :
    forall f g p t l,
    (forall l x, f (l + p) x = g l x) ->
    traverse f (l + p) t = traverse g l t.

  Axiom traverse_functorial :
    forall f g t l,
    traverse g l (traverse f l t) = traverse (fun l x => traverse g l (f l x)) l t.

  Axiom traverse_id :
    forall l t,
    traverse (fun _ x => var x) l t = t.

  Axiom traverse_var :
    forall f l x,
    traverse f l (var x) = f l x.

End Syntax.

Module DeBruijn(S : Syntax).

  Definition lift : nat -> nat -> S.term -> S.term :=
    fun w k x =>
      if Nat.leb k x then w + x else x.

      Nat.le_gt_dec

End DeBruijn.
