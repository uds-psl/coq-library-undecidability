From Undecidability.L.Tactics Require Import LTactics.
From Undecidability.L Require Import UpToC.
From Undecidability.L.Datatypes Require Export List_enc LBool.

Section forallb. 
  Variable (X : Type).
  Context (H : encodable X).

  Definition c__forallb := 15. 
  Definition forallb_time (fT : X -> nat) (l : list X) := sumn (map (fun elm => fT elm + c__forallb) l) + c__forallb. 

  Global Instance term_forallb : computableTime' (@forallb X) (fun f fT => (1, fun l _ => (forallb_time (callTime fT) l, tt))). 
  Proof.
    extract.
    solverec. 
    all: unfold forallb_time, c__forallb; solverec. 
  Qed. 

  Global Instance term_forallb_notime : computable (@forallb X) . 
  Proof.
    extract.
  Defined.

  Lemma forallb_time_eq f (l:list X):
    forallb_time f l = sumn (map f l) + length l * c__forallb + c__forallb.
  Proof.
    induction l as [ | x l IH];cbn -[c__forallb]. lia. unfold forallb_time in IH. nia.
  Qed.

  Lemma forallb_time_const c (l:list X):
    forallb_time (fun _ =>  c) l = length l * (c+c__forallb) + c__forallb.
  Proof.
    induction l as [ | x l IH];cbn -[c__forallb]. lia. unfold forallb_time in IH; nia.
  Qed.
End forallb.


  Section foldl_time.
  Context {X Y : Type}.
  Context {H : encodable X}.
  Context {F : encodable Y}.

  Definition c__fold_left := 15. 
  Definition c__fold_left2 := 5.
  Fixpoint fold_left_time (f : X -> Y -> X) (t__f : X -> Y -> nat) (l : list Y) (acc : X) :=
  (match l with
      | [] =>c__fold_left 
      | (l :: ls) => t__f acc l + c__fold_left + fold_left_time f t__f ls (f acc l)
      end ).

  Global Instance term_fold_left :
    computableTime' (@fold_left X Y) (fun f fT => (c__fold_left2, fun l _ => (c__fold_left2, fun acc _ => (fold_left_time f (callTime2 fT) l acc, tt)))). 
  Proof.
    extract. 
    solverec. all: unfold c__fold_left, c__fold_left2; solverec. 
  Qed. 
End foldl_time.

  Section foldr_time.
  Context {X Y: Type}.
  Context {H:encodable X}.
  Context {H0: encodable Y}.

  Definition c__fold_right := 15.
  Fixpoint fold_right_time (f : Y -> X -> X) (tf : Y -> X -> nat) (l : list Y) (acc : X) :=
      match l with [] => c__fold_right
              | l::ls => tf l (fold_right f acc ls) + c__fold_right + fold_right_time f tf ls acc
      end. 
  Global Instance term_fold_right : computableTime' (@fold_right X Y) (fun f fT => (1, fun acc _ => (1, fun l _ => (fold_right_time f (callTime2 fT) l acc + c__fold_right, tt)))).
  Proof.
    extract. solverec. all: unfold fold_right, c__fold_right; solverec.  
  Qed. 
End foldr_time.