Require Import Lia List PeanoNat Permutation.
Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".
Set Default Proof Using "Type".

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

(* induction/recursion principle wrt. a decreasing measure f *)
(* example: elim /(measure_rect length) : l. *)
Lemma measure_rect {X : Type} (f : X -> nat) (P : X -> Type) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  exact: (well_founded_induction_type (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.

Lemma prod_nat_nat_eq_dec (x y : nat * nat) : {x = y} + {x <> y}.
Proof. by do ? decide equality. Qed.

Lemma eq_or_inf {X: Type} : (forall (x y: X), {x = y} + {x <> y}) ->
  forall (x y: X) P, (x = y) \/ P -> (x = y) + P.
Proof.
  move=> H x y P. case: (H x y).
  - move=> ??. by left.
  - move=> ??. right. tauto.
Qed.

Lemma iter_plus {X} (f : X -> X) (x : X) n m : Nat.iter (n + m) f x = Nat.iter m f (Nat.iter n f x).
Proof.
  elim: m; first by rewrite Nat.add_0_r.
  move=> m /= <-. by have ->: n + S m = S n + m by lia.
Qed.

Lemma Exists_sig {X : Type} P (HP : (forall x, {P x} + {~ P x})) (L : list X) :
  Exists P L -> { x | In x L /\ P x}.
Proof.
  elim: L. { by move=> /Exists_nil. }
  move=> x L IH /Exists_cons H.
  have [/IH|?] := Exists_dec P L HP.
  - move=> [y [? ?]]. exists y. by split; [right|].
  - exists x. by split; [left|tauto].
Qed.

Lemma list_sum_map_le {X: Type} f g (L: list X) :
  (forall x, f x <= g x) ->
  list_sum (map f L) <= list_sum (map g L).
Proof.
  move=> Hfg. elim: L; first done.
  move=> x L IH /=. have := Hfg x. lia.
Qed.

Lemma list_sum_map_lt {X: Type} {f g} {L: list X} {x} :
  (forall x, f x <= g x) ->
  In x L -> f x < g x ->
  list_sum (map f L) < list_sum (map g L).
Proof.
  move=> Hfg + H'fg. elim: L; first done.
  move=> y L IH /= [->|].
  - have := list_sum_map_le f g L Hfg. lia.
  - move=> /IH. have := Hfg y. lia.
Qed.

Lemma oiter_None {X : Type} (f : X -> option X) k : Nat.iter k (obind f) None = None.
Proof. elim: k; [done | by move=> /= ? ->]. Qed.

Lemma obind_oiter {X : Type} (f : X -> option X) k x : 
  obind f (Nat.iter k (obind f) (Some x)) = Nat.iter k (obind f) (f x).
Proof. elim: k; [done|by move=> k /= ->]. Qed.

Lemma NoDup_map_ext {X Y : Type} (f : X -> Y) (l : list X) :
  (forall x1, In x1 l -> forall x2, In x2 l -> f x1 = f x2 -> x1 = x2) -> NoDup l -> NoDup (map f l).
Proof.
  elim: l. { move=> *. by constructor. }
  move=> x l IH /= H /NoDup_cons_iff [Hxl] /IH {}IH. constructor.
  - move=> /in_map_iff [x'] [/H] ? Hx'l. have ? : x' = x by tauto.
    subst x'. exact: (Hxl Hx'l).
  - apply: IH. move=> x1 Hx1l x2 Hx2l /H. tauto.
Qed.

Lemma nth_error_seq {i start len} :
  i < len -> nth_error (seq start len) i = Some (start + i).
Proof.
  elim: len i start; first by lia.
  move=> len IH [|i] start.
  { move=> ?. congr Some. lia. }
  move=> ?. rewrite /= IH; first by lia.
  congr Some. lia.
Qed.

(* variant of the pigeonhole principle *)
Lemma pigeonhole {X : Type} (L L' : list X) :
  incl L L' -> length L' < length L -> not (NoDup L).
Proof.
  move=> ?? HL. suff: length L = length L' by lia.
  apply /Permutation_length /NoDup_Permutation_bis; by [|lia].
Qed.

Section DiscreteList.

Context {X : Type} (X_eq_dec : forall (x y : X), {x = y} + {x <> y}).

Lemma not_NoDup_consE {x} {l: list X} : (not (NoDup (x :: l))) -> In x l \/ not (NoDup l).
Proof using X_eq_dec.
  have [?|?] := In_dec X_eq_dec x l.
  { move=> ?. by left. }
  move=> Hxl. right => Hl. apply: Hxl.
  by constructor.
Qed.

Lemma not_NoDupE {l : list X} : not (NoDup l) -> 
  exists '(i, j), i < j < length l /\ nth_error l i = nth_error l j.
Proof using X_eq_dec.
  elim: l. { move=> H. exfalso. apply: H. by constructor. }
  move=> x l IH.
  move=> /not_NoDup_consE [|].
  - move=> /(@In_nth_error X) [j] Hj.
    have ? : not (length l <= j).
    { move=> /nth_error_None. by rewrite Hj. }
    exists (0, S j) => /=. split; [lia|done].
  - move=> /IH [[i j]] [? ?].
    exists (S i, S j) => /=. split; [lia|done].
Qed.

Lemma not_inclE (L L' : list X) : (not (incl L L')) -> { x | In x L /\ not (In x L')}.
Proof using X_eq_dec.
  elim: L. { move=> H. exfalso. by apply: H. }
  move=> x L IH /=.
  have [|?] := In_dec X_eq_dec x L'.
  - move=> ? HxLL'. have /IH [y [? ?]] : ~ incl L L'.
    { move=> H. apply: HxLL'. by move=> y /= [<-|/H]. }
    exists y. tauto.
  - move=> _. exists x. tauto.
Qed.

(* explicit duplicates in a mapped sequence *)
Lemma dup_seq (f : nat -> X) start len :
  not (NoDup (map f (seq start len))) ->
  exists '(i, j), f i = f j /\ (start <= i /\ i < j /\ j < start+len).
Proof using X_eq_dec.
  move=> /not_NoDupE [[i j]]. rewrite map_length seq_length.
  move=> [? H]. exists (start+i, start+j). split; last lia.
  move: H. rewrite ?nth_error_map ?nth_error_seq; [lia|lia|].
  by move=> [].
Qed.

End DiscreteList.
