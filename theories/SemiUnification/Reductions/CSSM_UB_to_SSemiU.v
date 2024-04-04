(* 
  Author(s):
    Andrej Dudenhefner (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

(* 
  Reduction from:
    Uniform Boundedness of Confluent Simple Stack Machines (CSSM_UB)
  to:
    Simple Semi-unification (SSemiU)
*)

Require Import List PeanoNat Lia.
Import ListNotations.
Require Import Relations.Relation_Operators Relations.Operators_Properties.

(* uniform boundedness of confluent simple stack machines *)
From Undecidability.StackMachines Require Import SSM.
From Undecidability.StackMachines.Util Require Import CSSM_facts.

(* simple semi-unification *)
Require Import Undecidability.SemiUnification.SemiU. 
From Undecidability.SemiUnification.Util Require Import Enumerable.

Require Import ssreflect ssrfun ssrbool.

Set Default Goal Selector "!".

Module Argument.

(* inject configuration into nat *)
Definition embed : config -> nat := to_nat.
Definition unembed : nat -> config := of_nat.
Definition embedP {X: config} : (unembed (embed X) = X) := enumP.

(* step relation to semi-unification constraints *)
Definition SM_to_SUcs (M: ssm) : list constraint := 
  map (fun '(x, y, a, b, d) => 
    if d then ((a, embed ([], [], x)), (embed ([], [], y), b)) (* ax -> yb *)
    else ((b, embed ([], [], y)), (embed ([], [], x), a)) (* xa -> by *)
    ) M.

Lemma arr_eqI {s t: bool -> term} : (forall (a: bool), s a = t a) -> 
  arr (s false) (s true) = arr (t false) (t true).
Proof. move=> H. by rewrite ? H. Qed.

Section SM.

Context {M : ssm}.
Variable confluent_M : confluent M.

Notation equiv := (@equiv M).
Notation equiv_dec := (@equiv_dec M).
Notation narrow_dec := (@narrow_dec M).
Notation bounded' := (@bounded' M).

(* bounded (by i) search for normal form of X *)
Fixpoint nf_aux (i: nat) (X: config) : config :=
  match i with
  | 0 => X
  | S i => if equiv_dec (unembed i) X then nf_aux i (unembed i) else nf_aux i X
  end.

(* normal form, minimal (wrt. embed) Y such that equiv X Y *)
Definition nf (X: config) : config := nf_aux (embed X) X.

(* X is equivalent to its normal form *)
Lemma nf_equiv (X: config) : equiv X (nf X).
Proof using confluent_M.
  rewrite /nf. move: (embed X) => i. elim: i X.
  { move=> X /=. by apply: equiv_refl. }
  move=> i IH X /=.
  case: (equiv_dec (unembed i) X).
  { move=> /equiv_sym H /=. apply: (equiv_trans confluent_M H). by apply: IH. }
  move=> /= _. by apply: IH.
Qed.

Lemma nf_equiv_eq_ind (X Y: config) (j: nat) : equiv X Y -> embed X < j -> nf_aux j Y = nf_aux (embed X) X.
Proof using confluent_M.
  elim: j X Y; first by lia.
  move=> i IH X Y HXY HXi /=.
  case: (equiv_dec (unembed i) Y)=> /=.
  { move=> /equiv_sym HYi.
    have [/[dup] [/(f_equal unembed) + ->] | ?]: (embed X = i \/ embed X < i) by lia.
    - rewrite embedP. by move=> ->.
    - apply: IH; [ apply: equiv_trans; by eassumption | done]. }
  move=> HiY. have [/(f_equal unembed) | ?]: (embed X = i \/ embed X < i) by lia.
  - rewrite embedP. move=> ?. by subst X.
  - by apply: IH.
Qed.

(* normal forms of equivalent configurations are equal *)
Lemma nf_equiv_eq (X Y: config) : equiv X Y -> nf X = nf Y.
Proof using confluent_M.
  have: (embed X = embed Y \/ embed X < embed Y \/ embed Y < embed X) by lia.
  case; [|case].
  - move /(f_equal unembed). rewrite ? embedP. by move=> ->.
  - move=> + H. move /nf_equiv_eq_ind. by move /(_ _ H).
  - move=> + /equiv_sym H. move /nf_equiv_eq_ind. by move /(_ _ H).
Qed.

(* n is 1 + bound - length X.2 *)
Fixpoint ζ (n: nat) (X: config) : term := 
  match n with
  | 0 => atom (embed (nf X))
  | S n => 
      match X with
      | (A, B, x) => 
        if narrow_dec (A, B, x) then arr (ζ n (A, B++[false], x)) (ζ n (A, B++[true], x)) 
        else atom (embed (nf X))
      end
  end.

Definition ψ (a: bool) (n: nat) (i: nat): term := 
  match unembed i with
  | (A, B, x) => ζ (n - length B) (A++[a], B, x)
  end.

Lemma ζ_nilP {n: nat} {x: state} : ζ (S n) ([], [], x) = arr (ζ n ([], [false], x)) (ζ n ([], [true], x)).
Proof. 
  move=> /=. case: (narrow_dec ([], [], x)); first done.
  move=> H. exfalso. apply: H. exists x, []. by apply: equiv_refl.
Qed. 

Lemma ζ_0P {X: config} : ζ 0 X = atom (embed (nf X)).
Proof. done. Qed.

Lemma ζ_SnP {n: nat} {x: state} {A B: stack} : ζ (S n) (A, B, x) = 
  if narrow_dec (A, B, x) then 
    arr (ζ n (A, B++[false], x)) (ζ n (A, B++[true], x)) 
  else atom (embed (nf (A, B, x))).
Proof. done. Qed.

Lemma SM_to_SUcsP {x y: state} {a b: symbol} : In (a, x, (y, b)) (SM_to_SUcs M) -> exists x' y', 
  x = (embed ([], [], x')) /\ y = (embed ([], [], y')) /\
  equiv ([a], [], x') ([], [b], y').
Proof.
  rewrite /SM_to_SUcs in_map_iff. move=> [[[[[x' y'] a'] b'] d]]. case: d.
  - case. case=> <- <- <- <- H.
    exists x', y'. constructor; first done. constructor; first done.
    exists ([], [b'], y'). constructor; [apply: rt_step; by apply: step_l | by apply: rt_refl].
  - case. case=> <- <- <- <- H.
    exists y', x'. constructor; first done. constructor; first done.
    exists ([b'], [], y'). constructor; [by apply: rt_refl | apply: rt_step; by apply: step_r].
Qed.

Lemma ζ_equivP {n: nat} {x x': state} {A B A' B': stack} : bounded' n -> equiv (A, B, x) (A', B', x') -> 
  ζ (S n - length B) (A, B, x) = ζ (S n - length B') (A', B', x').
Proof using confluent_M.
  move /(extend_bounded' confluent_M) => Hn. move Hm: (S n - length B)=> m.
  elim: m A B A' B' Hm.
  - move=> A B A' B' HnB Hxx'.
    have [-> | HnB']: (S n - length B' = 0 \/ S n - length B' = (S (n - length B'))) by lia.
    { rewrite ? ζ_0P. do 2 f_equal. by apply: nf_equiv_eq. }
    rewrite HnB' ζ_0P ζ_SnP.
    case: (narrow_dec (A', B', x')) => /=; first last.
    { move=> _. do 2 f_equal. by apply: nf_equiv_eq. }
    move /equiv_sym in Hxx'.
    move /(narrow_equiv confluent_M Hxx') /Hn => /=. by lia.
  - move=> m IH A B A' B' Hm Hxx'.
    have [HnB' | ->]: (S n - length B' = 0 \/ S n - length B' = S (n - length B')) by lia.
    { rewrite HnB' ζ_0P ζ_SnP.
      case: (narrow_dec (A, B, x)) => /=; first last.
      - move=> _. do 2 f_equal. by apply: nf_equiv_eq.
      - move /(narrow_equiv confluent_M Hxx') /Hn => /=. by lia. }
    rewrite ?ζ_SnP.
    case: (narrow_dec (A, B, x)); case: (narrow_dec (A', B', x'))=> /=.
    + move=> _ _. apply: (arr_eqI (s := fun=> ζ _ _) (t := fun=> ζ _ _)).
      move=> b. have -> : n - length B' = S n - length (B' ++ [b]) by (rewrite length_app /length; lia).
      apply: IH; [ rewrite length_app /length -/(length _); by lia | by apply: equiv_appR].
    + by move=> + /(narrow_equiv confluent_M Hxx').
    + by move=> /(narrow_equiv confluent_M ((iffLR equiv_sym) Hxx')).
    + move=> _ _. do 2 f_equal. by apply: nf_equiv_eq.
Qed.

Lemma ψP {a: bool} {n: nat} {X: config} : ψ a n (embed X) = 
  match X with
  | (A, B, x) => ζ (n - length B) (A++[a], B, x)
  end.
Proof. by rewrite /ψ embedP. Qed.

Lemma ψζP {n: nat} {x: state} {A B: stack} {a: bool} : bounded' n -> 
  ζ (S n - length B) (A ++ [a], B, x) = substitute (ψ a (S n)) (ζ (S n - length B) (A, B, x)).
Proof using confluent_M.
  move=> Hn. move Hm: (S n - length B)=> m.
  elim: m x A B Hm.
  - move=> x A B Hm. rewrite ? ζ_0P /= ψP.
    move HAxB: (nf (A, B, x)) => [[A' B'] x'].
    have [-> | ?]: S n - length B' = 0 \/ S n - length B' > 0 by lia.
    { rewrite ζ_0P. f_equal. f_equal. 
      apply: nf_equiv_eq. apply: equiv_appL. rewrite -HAxB. by apply: nf_equiv. }
    have Hxx': equiv (A' ++ [a], B', x') (A ++ [a], B, x).
    { apply: equiv_appL. rewrite equiv_sym -HAxB. by apply: nf_equiv. }
    by rewrite (ζ_equivP Hn Hxx') Hm ζ_0P.
  - move=> m IH x A B Hm.
    rewrite ? ζ_SnP. case: (narrow_dec (A, B, x)).
    (* AxB is narrow *)
    + move=> /= /(narrow_appL (a := a)) => ?. case: (narrow_dec (A ++ [a], B, x)); last done.
      move=> _ /=. apply: (arr_eqI (s := fun => ζ _ _) (t := fun => substitute _ _)).
      move=> b. apply: IH. rewrite length_app /length -/(length _). by lia.
    + move=> _ /=. rewrite -(ζ_SnP (A := A ++ [a])).
      rewrite ψP. move HAxB: (nf (A, B, x)) => [[A' B'] x'].
      rewrite -Hm.
      have Hxx': equiv (A ++ [a], B, x) (A' ++ [a], B', x').
      { apply: equiv_appL. rewrite -HAxB. by apply: nf_equiv. }
      by rewrite (ζ_equivP Hn Hxx').
Qed.

End SM.

Lemma itebP {X: Type} {P: bool -> X} {b: bool} : (if b then P true else P false) = P b.
Proof. by case: b. Qed.

(* if M is uniformly bounded, 
  then the constructed simple semi-unification instance has a solution *)
Lemma soundness {M: cssm} : CSSM_UB M -> SSemiU (SM_to_SUcs (proj1_sig M)).
Proof.
  Opaque ζ ψ.
  case: M=> M confluent_M.
  rewrite /CSSM_UB /SSemiU. move /(boundedP confluent_M) => /= [n HnM].
  exists (fun i => @ζ M (S n) (unembed i)), (@ψ M false (S n)), (@ψ M true (S n)).
  move=> [[a x]] => [[y b]] /=. move /SM_to_SUcsP => [x' [y' [-> [->]]]] /equiv_sym Hxy.
  rewrite ?embedP ζ_nilP (itebP (P := fun _ => ζ _ _)).
  have /= := ζ_equivP confluent_M HnM Hxy. have ->: n - 0 = n by lia.
  move=> ->. rewrite (itebP (P := fun=> ψ _ _)).
  by apply: (ψζP _ HnM (A := []) (B := [])).
Qed.

(* reduction completeness *)

Fixpoint term_depth_bound (t: term) : nat :=
  match t with
  | atom _ => 1
  | arr s t => 1 + (term_depth_bound s) + (term_depth_bound t)
  end.

Fixpoint depth_bound (φ: valuation) (xs: list state) : nat :=
  match xs with
  | [] => 1
  | x :: xs => 1 + term_depth_bound (φ x) + depth_bound φ xs
  end.

Lemma depth_boundP {φ: valuation} {x: state} {xs: list state} : In x xs -> term_depth_bound (φ x) <= depth_bound φ xs.
Proof.
  elim: xs; first done.
  move=> y xs IH /= [-> | /IH]; by lia.
Qed.

Fixpoint descend (t: term) (B: stack) {struct B} : option term :=
  match B with
  | [] => Some t
  | b :: B => 
    match t with
    | atom _ => None
    | arr s t => descend (if b then t else s) B
    end
  end.

Fixpoint ascend (ψ0 ψ1: valuation) (t: term) (A: stack) : term :=
  match A with
  | [] => t
  | a :: A => ascend ψ0 ψ1 (substitute (if a then ψ1 else ψ0) t) A
  end.

Lemma ascend_arr {ψ0 ψ1: valuation} {s t: term} {A: stack} : 
  ascend ψ0 ψ1 (arr s t) A = arr (ascend ψ0 ψ1 s A) (ascend ψ0 ψ1 t A).
Proof.
  elim: A s t; first done.
  move=> a A IH s t /=. by rewrite IH.
Qed.

(* interpret φ ψ0 ψ1 of s|p|q is πp (ψs (φ p)) *)
Definition interpret (φ ψ0 ψ1: valuation) (X: config) : option term :=
  match X with 
  | (A, B, x) => descend (ascend ψ0 ψ1 (φ (embed ([], [], x))) A) B
  end.

(* reachabile configurations have the same interpretation  *)
Lemma interpretP {M: ssm} {X Y: config} {φ ψ0 ψ1: valuation} : 
  Forall (models φ ψ0 ψ1) (SM_to_SUcs M) -> reachable M X Y -> interpret φ ψ0 ψ1 X = interpret φ ψ0 ψ1 Y.
Proof.
  move=> HM. elim; [| done | by move=> > ? ->].
  move=> {}X {}Y [|] x y a b A B.
  - move: HM. rewrite /SM_to_SUcs Forall_map Forall_forall => HM. 
    move /HM. rewrite /models /interpret.
    case: (φ (embed ([], [], y))); first done.
    move: a b => [|] [|] ? ? -> /=; by rewrite ascend_arr.
  - move: HM. rewrite /SM_to_SUcs Forall_map Forall_forall => HM. 
    move /HM. rewrite /models /interpret.
    case: (φ (embed ([], [], x))); first done.
    move: a b => [|] [|] ? ? -> /=; by rewrite ascend_arr.
Qed.

Lemma descendP {s t: term} {B: list symbol} : descend s B = Some t -> length B <= term_depth_bound s.
Proof.
  elim: B s t; first by (move=> /= *; lia).
  move=> b B IH [ /= | > /IH]; [done | case: b => /=; by lia].
Qed.

(* if the constructed simple semi-unification instance has a solution, 
  then M is uniformly bounded *)
Lemma completeness {M: cssm}: SSemiU (SM_to_SUcs (proj1_sig M)) -> CSSM_UB M.
Proof.
  case: M=> M confluent_M /=.
  move=> [φ [ψ0 [ψ1]]]. rewrite -Forall_forall => Hφ.
  pose f x := embed (([], [], x) : config).
  apply: (bounded_of_bounded' confluent_M (n := depth_bound φ (map f (enum_states M)))).
  move=> /= Z x y A B Hx Hy.
  case: (In_dec _ y (enum_states M)); first by decide equality.
  { move=> /(in_map f) /depth_boundP => /(_ φ) Hfy.
    move: Hy => /(interpretP Hφ). move: Hx => /(interpretP Hφ) <- /= /descendP.
    rewrite -/(f y). move: (length B) => ?. by lia. }
  move: (Hy) Hx => /enum_states_reachable [<- /enum_states_reachable | ]; last by by move=> [+].
  case; last by move=> [+].
  case=> *. subst=> /=. by lia.
Qed.

End Argument.

Require Import Undecidability.Synthetic.Definitions.

(* many-one reduction from uniform boundedness of confluent simple stack machines (CSSM_UB)
  to simple semi-unification (SSemiU) *)
Theorem reduction : CSSM_UB ⪯ SSemiU.
Proof.
  exists (fun dM => Argument.SM_to_SUcs (proj1_sig dM)).
  intros [M HM]. constructor.
  - exact Argument.soundness.
  - exact Argument.completeness.
Qed.
