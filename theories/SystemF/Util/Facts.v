Require Import List Lia.
Import ListNotations.

Require Import ssreflect ssrbool ssrfun.

Set Default Goal Selector "!".

(* Generic facts *)

(* transforms a goal (A -> B) -> C into goals A and B -> C *)
Lemma unnest : forall (A B C : Type), A -> (B -> C) -> (A -> B) -> C.
Proof. auto. Qed.

Lemma iter_plus {X: Type} {f: X -> X} {x: X} {n m: nat} : Nat.iter n f (Nat.iter m f x) = Nat.iter (n + m) f x.
Proof. elim: n; [done | by move=> n /= ->]. Qed.

Fact iter_last {X: Type} {f: X -> X} {n x} : Nat.iter n f (f x) = Nat.iter (1+n) f x.
Proof. elim: n x; [done | by move=> n /= + x => ->]. Qed.

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
