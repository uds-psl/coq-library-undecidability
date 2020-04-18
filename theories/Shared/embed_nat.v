Require Import PeanoNat.

(* bijection from nat * nat to nat *)
Definition embed '(x, y) : nat := 
  y + (nat_rec _ 0 (fun i m => (S i) + m) (y + x)).

(* bijection from nat to nat * nat *)
Definition unembed (n : nat) : nat * nat := 
  nat_rec _ (0, 0) (fun _ '(x, y) => match x with S x => (x, S y) | _ => (S y, 0) end) n.

Lemma embedP {xy: nat * nat} : unembed (embed xy) = xy.
Proof.
  assert (forall n, embed xy = n -> unembed n = xy).
    intro n. revert xy. induction n as [|n IH].
      intros [[|?] [|?]]; intro H; inversion H; reflexivity.
    intros [x [|y]]; simpl.
      case x as [|x]; simpl; intro H.
        inversion H.
      rewrite (IH (0, x)); [reflexivity|].
      inversion H; simpl. rewrite Nat.add_0_r. reflexivity.
    intro H. rewrite (IH (S x, y)); [reflexivity|]. 
    inversion H. simpl. rewrite Nat.add_succ_r. reflexivity.
  apply H. reflexivity.
Qed.

Lemma unembedP {n: nat} : embed (unembed n) = n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  simpl. revert IH. case (unembed n). intros x y.
  case x as [|x]; intro Hx; rewrite <- Hx; simpl.
    rewrite Nat.add_0_r. reflexivity.
  rewrite ?Nat.add_succ_r. simpl. rewrite ?Nat.add_succ_r. reflexivity. 
Qed.
Arguments embed : simpl never.


Module EmbedNatNotations.
  Notation "⟨ a , b ⟩" := (embed (a, b)) (at level 0).
End EmbedNatNotations.
