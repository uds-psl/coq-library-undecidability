Require Import Undecidability.Shared.Libs.PSL.Base Lia.

(* Sum *)

Fixpoint sumn (A:list nat) :=
  match A with
    [] => 0
  | a::A => a + sumn A
  end.

Lemma sumn_app A B : sumn (A++B) = sumn A + sumn B.
Proof.
  induction A;cbn;lia.
Qed.

Global Hint Rewrite sumn_app : list. 

Lemma length_concat X (A : list (list X)) :
  length (concat A) = sumn (map (@length _) A).
Proof.
  induction A;cbn. reflexivity. autorewrite with list in *. lia.
Qed.

Lemma sumn_rev A :
  sumn A = sumn (rev A).
Proof.
  enough (H:forall B, sumn A + sumn B = sumn (rev A++B)).
  {specialize (H []). cbn in H. autorewrite with list in H. cbn in H. lia. }
  induction A as [|a A];intros B. reflexivity.
  cbn in *. specialize (IHA (a::B)). autorewrite with list in *. cbn in *. lia.
Qed.

Lemma sumn_map_add X f g (l:list X) :
  sumn (map (fun x => f x + g x) l) = sumn (map f l) + sumn (map g l).
Proof.
  induction l;cbn;nia.
Qed.
Lemma sumn_map_mult_c_r X f c (l:list X) :
  sumn (map (fun x => f x *c) l) = sumn (map f l)*c.
Proof.
  induction l;cbn;nia.
Qed.
Lemma sumn_map_c X c (l:list X) :
  sumn (map (fun _ => c) l) = length l * c.
Proof.
  induction l;cbn;nia.
Qed.

Lemma sumn_le_in n xs: n el xs -> n <= sumn xs.
Proof.
  induction xs. easy. intros [ | ]. now cbn;nia.
  cbn;etransitivity. apply IHxs. easy. nia.
Qed.

Lemma sumn_concat xs: sumn (concat xs) = sumn (map sumn xs).
Proof.
  induction xs;cbn. easy. etransitivity. apply sumn_app. nia.
Qed.

Lemma sumn_repeat c n: sumn (repeat c n) = c * n.
Proof.
  induction n;cbn. all:nia.
Qed.

