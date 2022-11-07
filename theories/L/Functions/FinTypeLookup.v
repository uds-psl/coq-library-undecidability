From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L.Datatypes Require Import LFinType LBool LProd Lists.
From Undecidability.L.Functions Require Import EqBool.

Section Lookup.
  Variable X Y : Type.
  Context {eqbX : X -> X -> bool}.
  Context `{eqbClass X eqbX}.

  Fixpoint lookup (x:X) (A:list (X*Y)) d: Y :=
    match A with
      [] => d
    | (key,Lproc)::A =>
      if eqb x key then Lproc else lookup x A d
    end.

  Context `{encodable X} `{@eqbComp X _ eqbX _}.

  Global Instance term_lookup `{encodable Y}:
    computable (lookup).
  Proof using H1.
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
  Context `{eqbClass X eqbX}.

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
