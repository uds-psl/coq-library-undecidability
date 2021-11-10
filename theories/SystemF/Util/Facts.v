Require Import List Lia.
Import ListNotations.

Require Import ssreflect ssrbool ssrfun.

Set Default Proof Using "Type".
Set Default Goal Selector "!".

(* Generic facts *)

(* duplicates argument *)
Fact copy {A : Type} : A -> A * A.
Proof. done. Qed.

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

Lemma iter_plus {X: Type} {f: X -> X} {x: X} {n m: nat} : Nat.iter n f (Nat.iter m f x) = Nat.iter (n + m) f x.
Proof. elim: n; [done | by move=> n /= ->]. Qed.

Fact iter_last {X: Type} {f: X -> X} {n x} : Nat.iter n f (f x) = Nat.iter (1+n) f x.
Proof. elim: n x; [done | by move=> n /= + x => ->]. Qed.

(* induction/recursion principle wrt. a decreasing measure f *)
(* example: elim /(measure_rect length) : l. *)
Lemma measure_rect {X : Type} (f : X -> nat) (P : X -> Type) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  exact: (well_founded_induction_type (Wf_nat.well_founded_lt_compat X f _ (fun _ _ => id)) P).
Qed.

(* List facts *)
Lemma Forall_appI {X: Type} {P : X -> Prop} {A B}: Forall P A -> Forall P B -> Forall P (A ++ B).
Proof. move=> ? ?. apply /Forall_app. by constructor. Qed.

Lemma incl_nth_error {X: Type} {Gamma Gamma': list X} : 
  incl Gamma Gamma' -> exists ξ, forall x, nth_error Gamma x = nth_error Gamma' (ξ x).
Proof.
  elim: Gamma Gamma'.
  - move=> Gamma' _. exists (fun x => length Gamma').
    move=> [|x] /=; apply /esym; by apply /nth_error_None.
  - move=> x Gamma IH Gamma'. move=> /Forall_forall /Forall_cons_iff.
    move=> [/(@In_nth_error _ _ _) [nx] Hnx /Forall_forall /IH] [ξ Hξ].
    exists (fun y => if y is S y then ξ y else nx). by case.
Qed.

Lemma Forall_seqP {P : nat -> Prop} {m n: nat} : 
  Forall P (seq m n) <-> (forall i, m <= i < m + n -> P i).
Proof. rewrite Forall_forall. constructor; move=> H ? ?; apply H; by apply /in_seq. Qed.

Lemma Forall2_consE {X Y: Type} {R: X -> Y -> Prop} {x y l1 l2} : 
  Forall2 R (x :: l1) (y :: l2) -> R x y /\ Forall2 R l1 l2.
Proof. move=> H. by inversion H. Qed.

Lemma Forall2_length_eq {X Y: Type} {R: X -> Y -> Prop} {l1 l2} : 
  Forall2 R l1 l2 -> length l1 = length l2.
Proof.
  elim: l1 l2.
  - move=> [| ? ?] H; first done. by inversion H.
  - move=> ? ? IH [| ? ?] /= H; inversion H. congr S. by apply: IH.
Qed.

Lemma in_app_l {X: Type} {x: X} {l1 l2: list X} : In x l1 -> In x (l1 ++ l2).
Proof. move=> ?. apply /in_app_iff. by left. Qed.

Lemma in_app_r {X: Type} {x: X} {l1 l2: list X} : In x l2 -> In x (l1 ++ l2).
Proof. move=> ?. apply /in_app_iff. by right. Qed.

(* construct choice function for a list over nat *)
Lemma list_choice {P : nat -> nat -> Prop} {l: list nat} : Forall (fun i : nat => exists n : nat, P i n) l ->
  exists φ, Forall (fun i : nat => P i (φ i)) l.
Proof.
  elim: l; first by exists id.
  move=> k l IH /Forall_cons_iff [[n Hkn]] /IH [φ Hφ].
  exists (fun i => if PeanoNat.Nat.eq_dec i k then n else φ i).
  constructor; first by case: (PeanoNat.Nat.eq_dec k k).
  apply: Forall_impl Hφ => i Hi.
  case: (PeanoNat.Nat.eq_dec i k); [by move=> /= ->|done].
Qed.

Lemma map_id' {X: Type} {f: X -> X} {l: list X} : (forall x, f x = x) -> map f l = l.
Proof. move=> ?. rewrite -[RHS]map_id. by apply: map_ext => ?. Qed.

Lemma is_trueP {b1 b2: bool} : (is_true b1 <-> is_true b2) <-> b1 = b2.
Proof.
  case: b1; case: b2; rewrite /is_true; firstorder done.
Qed.
