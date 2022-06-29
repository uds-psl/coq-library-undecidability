From Undecidability.L.Tactics Require Import LTactics GenEncode.
From Undecidability.L Require Import Functions.EqBool.
From Undecidability.L.Datatypes Require Import LBool LNat LOptions LProd.
From Undecidability.L Require Import UpToC.

(* ** Encoding of lists *)

From Undecidability.L.Datatypes.List Require List_enc.
Include List_enc.

From Undecidability.L.Datatypes.List Require Export List_basics List_eqb List_extra List_fold List_in List_nat.


Definition c__listsizeCons := 5.
Definition c__listsizeNil := 4.
Lemma size_list X `{encodable X} (l:list X):
  size (enc l) = sumn (map (fun x => size (enc x) + c__listsizeCons) l)+ c__listsizeNil.
Proof.
  unfold enc at 1;cbn. unfold c__listsizeCons, c__listsizeNil. 
  induction l.
  -easy.
  -cbn [size]. solverec.
Qed.
 

Lemma size_list_cons (X : Type) (H : encodable X) x (l : list X):
  size (enc (x::l)) = size (enc x) + size (enc l) + c__listsizeCons.
Proof.
  rewrite !size_list. cbn. lia.
Qed.

Lemma size_rev X {_:encodable X} (xs : list X): L_facts.size (enc (rev xs)) = L_facts.size (enc xs).
Proof.
  rewrite !size_list,map_rev,<- sumn_rev. easy.
Qed.

Lemma size_list_In X {R__X  :encodable X} (x:X) xs:
  x el xs -> L_facts.size (enc x) <= L_facts.size (enc xs).
Proof.
  intro H. rewrite !size_list,sumn_map_add. rewrite <- (sumn_le_in (in_map _ _ _ H)) at 1. nia.
Qed.

Lemma size_list_enc_r {X} `{encodable X} (l:list X):
  length l <= size (enc l).
Proof.
  rewrite size_list. induction l;cbn. all: unfold c__listsizeNil, c__listsizeCons in *; lia.
Qed.



(*Section list_prod.*)

  (*Context {X Y : Type}.*)
  (*Context {HX : encodable X} {HY : encodable Y}.*)
  
  (*Global Instance term_list_prod : computable (@list_prod X Y).*)
  (*Proof.*)
    (*unfold list_prod.*)
    (*change (computable*)
              (*(fix list_prod (l : list X) (l' : list Y) {struct l} : list (X * Y) :=*)
                 (*match l with*)
                 (*| [] => []*)
                 (*| x :: t => map (pair x) l' ++ list_prod t l'*)
                 (*end)).*)
    (*extract.*)
  (*Qed.*)

(*End list_prod.*)