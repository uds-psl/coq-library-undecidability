(* 
  Autor(s):
    Andrej Dudenhefner (1) 
    Johannes Hostert (1) 
  Affiliation(s):
    (1) Saarland University, Saarbrücken, Germany
*)

Require Import List.
From Undecidability.DiophantineConstraints Require Import H10UPC.

Definition c2_full (x:nat) : {y:nat | x * S x = y+y}.
Proof. 
  induction x as [|x [y' IH]].
  - exists 0. lia.
  - exists (y'+x+1). nia.
Defined.

Definition c2 (x:nat) := match (c2_full x) with exist _ y _ => y end.

Definition c2_descr (x:nat) : x * S x = c2 x + c2 x.
Proof.
unfold c2. now destruct (c2_full x).
Qed. 

Definition h10upc_sem_direct (c : h10upc) :=
  match c with 
    | ((x, y), (z1, z2)) => 
        1 + x + y = z1 /\ y * (1 + y) = z2 + z2
  end.

Lemma h10upc_inv (a b c d : nat) : h10upc_sem_direct ((a,S b),(c,d)) -> 
         {c':nat & {d':nat & h10upc_sem_direct ((a,b),(c',d')) 
                             /\ S c' = c /\ d' + b + 1 = d}}.
Proof.
intros [Hl Hr].
exists (a + S b). exists (c2 b).
repeat split.
- lia.
- apply c2_descr.
- lia.
- enough (2*(c2 b + b + 1) = d+d) by nia. rewrite <- Hr.
  cbn. rewrite Nat.mul_comm. cbn. symmetry.
  pose (c2_descr b) as Hb. nia.
Qed.

Lemma h10_rel_irref (p:nat*nat) : ~ (h10upc_sem_direct (p,p)).
Proof.
intros H. destruct p as [a b]. cbn in H. lia.
Qed.

Definition highest_var (x:h10upc) := match x with ((a,b),(c,d)) => Nat.max a (Nat.max b (Nat.max c d)) end.
Lemma highest_var_descr (x:h10upc) : let hv := highest_var x in match x with ((a,b),(c,d)) => a <= hv /\ b <= hv /\ c <= hv /\ d <= hv end.
Proof.
destruct x as [[a b] [c d]]. cbn. repeat split; lia.
Qed.

Fixpoint highest_var_list (x:list h10upc) := match x with nil => 0 | x::xr => Nat.max (highest_var x) (highest_var_list xr) end.
Lemma highest_var_list_descr (x:list h10upc) (h:h10upc) : In h x ->  highest_var h <= highest_var_list x.
Proof.
induction x as [|hh x IH].
- intros [].
- intros [hhh|hx].
  + cbn. rewrite hhh. lia.
  + cbn. specialize (IH hx). lia.
Qed.

Fixpoint highest_num (env: nat -> nat) (n:nat) : nat := match n with 0 => env 0 | S n => Nat.max (env (S n)) (highest_num env n) end.
Lemma highest_num_descr (env:nat -> nat) (n:nat) (m:nat) : m <= n -> env m <= highest_num env n.
Proof.
induction n as [|n IH].
- intros Hm. assert (m=0) as Hm0. 1:lia. cbn. rewrite Hm0. lia.
- intros HmSn. cbn. destruct (Nat.eq_dec (S n) m) as [Heq|Hneq].
  + rewrite <- Heq. lia.
  + assert (m <= n) as Hmn. 1:lia. specialize (IH Hmn). lia.
Qed.