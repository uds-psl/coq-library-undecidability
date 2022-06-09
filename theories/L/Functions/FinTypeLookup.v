From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LFinType LProd LBool.
From Undecidability.L.Datatypes.List Require Import List_enc.

Section Lookup.
  Variable X Y : Type.
  Variable eqbX : X -> X -> bool.
  Context {HX : registered X}.
  Context {H1eqbX : eqbClass eqbX} {H2eqbX : computable eqbX}.

  Fixpoint lookup (x:X) (A:list (X*Y)) d: Y :=
    match A with
      [] => d
    | (key,Lproc)::A =>
      if eqb x key then Lproc else lookup x A d
    end.

  Global Instance term_lookup `{registered Y} :
    computable (lookup).
  Proof using HX H1eqbX H2eqbX.
    unfold lookup. unfold eqb.
    extract.
  Qed.

End Lookup.

Section funTable.

  Variable X : finType.
  Variable Y : Type.
  Variable f : X -> Y.

  Definition funTable :=
    map (fun x => (x,f x)) (elem X).

  Variable (eqbX : X -> X -> bool).
  Context {HeqbX : eqbClass eqbX}.

  Lemma lookup_funTable x d:
    lookup x funTable d = f x.
  Proof.
    unfold funTable.
    specialize (elem_spec x).
    generalize (elem X) as l.
    induction l;cbn;intros Hel.
    -tauto.
    -destruct (eqb_spec x a).
     +congruence.
     +destruct Hel. 1:congruence.
      eauto.
  Qed.

End funTable.
