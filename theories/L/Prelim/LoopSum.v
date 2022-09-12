From Undecidability.L.Prelim Require Import ARS MoreBase.
  
Definition loopSum {X} {Y} :=
  fix loopSum n (f:X -> X + Y) (x:X) {struct n}:=
  match n with
    0 => None
  | S n => match f x with
          | inl x' => loopSum n f x'
          | inr y => Some y
          end
  end.

Arguments loopSum _ _ !_.

Definition loopSum_mono X Y f x y n n':
  n <= n' -> @loopSum X Y n f x = Some y -> loopSum n' f x = Some y.
Proof.
  induction n in n',x|-*;intros H. now inversion 1.
  -inv H. easy. cbn. destruct _. 2:easy. apply IHn. lia. 
Qed.

Lemma loopSum_sound_rel X Y {R:X->X->Prop} k n x y (f: X -> X + Y):
  (forall x y, R x y -> f x = inl y) ->
  pow R k x y ->
  loopSum (k+n) f x = loopSum n f y.
Proof.
  intros H1 R1.
  induction k in R1,x|-*.
  -inv R1. reflexivity.
  -change (S k) with (1+k) in R1. eapply pow_add in R1 as (x'&R2&R1).
   eapply rcomp_1 in R2. apply H1 in R2. cbn.
   rewrite R2. now apply IHk.
Qed.

Lemma loopSum_rel_correct2 X Y {R:X->X->Prop} k x y (f: X -> X + Y):
  (forall x, match f x with
        | inl y => R x y
        | inr _ => terminal R x
        end)->
  loopSum k f x = Some y ->
  exists i x', i < k /\ loopSum k f x = loopSum (k-i) f x'
          /\ pow R i x x'
          /\ terminal R x'
          /\ f x' = inr y.
Proof.
  intros H1 Heq.
  induction k in Heq,x|-*. now inv Heq.
  cbn in Heq.
  specialize (H1 x).
  destruct (f x) eqn:eqf.
  -eapply IHk in Heq as (i&x'&?&?&?&?&?).
   eexists (1 + i),x'.
   repeat eapply conj.
   +lia.
   +cbn. rewrite eqf. easy.
   +eapply pow_add;do 2 esplit.
    eapply rcomp_1 with (R:=R). all:eassumption.
   +easy.
   +easy.
  -inv Heq.
   exists 0,x.
   repeat eapply conj.
   all:solve [easy|lia].
Qed.

Definition optionFToSum {X} f (x:X) : X + X :=
  match f x with
    None => inr x
  | Some y => inl y
  end.  
