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

  Context `{registered X} `{@eqbCompT X _ eqbX _}.

  Definition lookupTime (x:nat) (l:list (X*Y)):=
    fold_right (fun '(a,b) res => eqbTime (X:=X) x (size (enc (a:X))) + res +24) 4 l.

  Global Instance term_lookup `{registered Y}:
    computableTime' (lookup) (fun x _ => (5, fun l _ => (1, fun d _ => (lookupTime (size (enc x)) l,tt)))).
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

Lemma lookup_sound' (A: Type) (B: Type) eqbA `{eqbClass (X:=A) eqbA} (L : list (prod A B)) a b def :
  (forall a' b1 b2, (a',b1) el L -> (a',b2) el L -> b1=b2) -> ( (a,b) el L \/ ((forall b', ~ (a,b') el L) /\ b = def) ) -> lookup a L def = b.
Proof.
  intros H1 H2.
  induction L as [ |[a' b'] L]. now intuition.
  cbn.
  destruct (eqb_spec a a').
  -subst a. destruct H2.
   2:now exfalso.
   eapply H1. all:easy.
  -apply IHL. all:intros.
   +eapply H1. all:eauto.
   +destruct H2 as [[]|]. all:easy.
Qed.

Lemma lookup_complete (A: Type) (B: Type) eqbA `{eqbClass (X:=A) eqbA} (L : list (prod A B)) a def :
  {(a,lookup a L def) el L } + {~(exists b, (a,b) el L) /\ lookup a L def  = def}.
Proof.
  induction L as [ |[a' b'] L].
  -cbn. right. firstorder.
  -cbn.  destruct (eqb_spec a a').
   1:{ do 2 left. congruence. }
   destruct IHL as [|[? eq]];[left|right].
   +eauto.
   +split. 2:easy.
    now intros (?&[]). 
Qed.
