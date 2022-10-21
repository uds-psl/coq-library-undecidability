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

  Context `{encodable X} `{@eqbCompT X _ eqbX _}.

  Definition lookupTime (x:nat) (l:list (X*Y)):=
    fold_right (fun '(a,b) res => eqbTime (X:=X) x (size (enc (a:X))) + res +24) 4 l.

  Global Instance term_lookup `{encodable Y}:
    computableTime' (lookup) (fun x _ => (5, fun l _ => (1, fun d _ => (lookupTime (size (enc x)) l,tt)))).
  Proof.
  unfold lookup. unfold eqb.
  extract. unfold lookupTime. solverec.
  Qed.

  Lemma lookupTime_leq x (l:list (X*Y)):
    lookupTime x l <= length l * (x* c__eqbComp X + 24) + 4.
  Proof.
    induction l as [ | [a b] l].
    -cbn. lia.
    -unfold lookupTime. cbn [fold_right]. fold (lookupTime x l).
     rewrite eqbTime_le_l.
     setoid_rewrite IHl. cbn [length].
     ring_simplify. unfold eqb. lia.
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
