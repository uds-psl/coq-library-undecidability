From Undecidability Require Import TM.Prelim TM.Relations.
From Undecidability.LAM Require Import LM_heap_def.

Require Import FunInd.

Fixpoint sum (A:list nat) :=
  match A with
    [] => 0
  | a::A => a + sum A
  end.

Lemma sum_app A B : sum (A++B) = sum A + sum B.
Proof.
  induction A;cbn;omega.
Qed.

Hint Rewrite sum_app : list. 

Definition sizeT t := 
    match t with
      varT n => 1 + n
    |  _ => 1
    end.  

Definition sizeP (P:Pro) := 1 + sum (map sizeT P).
Hint Unfold sizeP.   

Section Analysis.


  (*Variable s : term.*)
 (* Hypothesis cs : closed s.*)
  Variable T V : list HClos.
  Variable H: list HEntr.

  Lemma jumpTarget_eq c c0 c1 c2: jumpTarget 0 c0 c = Some (c1,c2) -> c1++[retT]++c2=c0++c.
  Proof.
    generalize 0 as k. 
    induction c as [ |[]] in c1,c2,c0|-*;cbn. congruence.
    all:intros ? H'.
    4:destruct k;[inv H';congruence| ].
    all:apply IHc in H'. 
    all:autorewrite with list in *.
    all:now cbn in *. 
  Qed.

(*
  Lemma tailRecursion_incl c alpha T': tailRecursion c alpha T' <<= c!alpha::T'.
  Proof.
    destruct c as [|[]];cbn. all:eauto.
  Qed.

  Lemma tailRecursion_length c alpha T': | tailRecursion c alpha T'| <= 1+ length T'.
  Proof.
    destruct c as [|[]];cbn. all:eauto.
  Qed.
*)
  
  Variable i : nat.

  Variable P0 : Pro.
  Hypothesis R: pow step i ([(0,P0)],[],[None]) (T,V,H).

  Lemma size_clos P a : ((a,P) el (T++V) -> sizeP P <= sizeP P0 /\ a <= length H)
                        /\ (forall beta, Some ((a,P),beta) el H -> sizeP P <= sizeP P0 /\ a <= length H /\ beta <= length H).
  Proof.
    unfold sizeP.
    induction i in T,V,H,R,P,a|-*.
    -inv R. split.
     +intros [[= <- <-]|[]].
      eauto using Nat.le_0_l.
     +intros ? [H|[]]. inv H.
    -(*apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
     specialize (IHn _ _ _ R1).
     eapply rcomp_1 in R2.
     split.
     +intros Hel.
      apply in_app_or in Hel.
      inv R2.
      *apply jumpTarget_eq in H2.  cbn in H2;inv H2.
       destruct Hel as [H1|[[= <- <-] | ]].
       apply tailRecursion_incl in H1 as [[= <- <-]|].
       
       all:repeat (autorewrite with list in *;cbn in * ).
       1:specialize (proj1 (IHn _ a0) ltac:(eauto)).
       3:specialize (proj1 (IHn _ a0) ltac:(eauto)).
       
       1,3:repeat (autorewrite with list in *;cbn in * ).
       1,2:omega.

       1:specialize (proj1 (IHn P a) ltac:(eauto)).
       2:specialize (proj1 (IHn P a) ltac:(eauto)).

       all:omega.

      *inv H2.
       destruct Hel as [[[= <- <-] | ]|].
       2:apply tailRecursion_incl in H as [[= <- <-]|].
       all:repeat ((try setoid_rewrite in_app_iff in IHn);cbn in IHn).
       1:specialize (proj1(IHn Q _) ltac:(eauto)).
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.

       1:specialize (proj1(IHn _ a0) ltac:(eauto)).
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.

       1:specialize (proj1(IHn P a) ltac:(eauto)).
       1:autorewrite with list in IHn.
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.

       1:specialize (proj1(IHn P a) ltac:(eauto)).
       1:autorewrite with list in IHn.
       1:repeat (autorewrite with list in *;cbn in * ).
       1:try now omega.
      *destruct Hel as [|[-> | ]].
       apply tailRecursion_incl in H0 as [[= <- <-]|].

       all:repeat ((try setoid_rewrite in_app_iff in IHn);cbn in IHn).
       1:specialize (proj1(IHn _ a0) ltac:(eauto)).
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.

       1:specialize (proj1(IHn _ a) ltac:(eauto)).
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.

       1:apply lookup_el in H2 as (?&?).
       1:specialize (proj2 (IHn _ a) _ ltac:(eauto)).
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.

       1:specialize (proj1(IHn _ a) ltac:(eauto)).
       1:repeat (autorewrite with list in *;cbn in * ).
       1:now omega.
     +intros ? Hel. inv R2.
      1,3:now apply IHn.
      inv H2.
      apply in_app_or in Hel.
      edestruct Hel as [|[[= -> ->]|[]]].
      1:specialize (proj2(IHn _ a) _ ltac:(eauto)).
      all:autorewrite with list;cbn.
      now omega.
      1:specialize (proj1(IHn _ a) ltac:(eauto)).
      1:specialize (proj1(IHn _ beta) ltac:(eauto)).
      omega.*)
  Admitted.

  Lemma length_H : length H <= 1+i.
  Proof.
    induction i in T,V,H,R|-*.
    -inv R. cbn;omega.
    -replace (S n) with (n + 1) in R by omega.
     (*
     apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
     specialize (IHn _ _ _ R1).
     eapply rcomp_1 in R2.
     inv R2.
     1,3:now omega.
     inv H2. autorewrite with list. cbn. omega.*)
  Admitted.

  Lemma length_TV : length T + length V <= 1+i.
  Proof.
    induction i in T,V,H,R|-*.
    -inv R. cbn;omega.
    -replace (S n) with (n + 1) in R by omega.
     (*apply pow_add in R. destruct R as [[[T' V'] H'] [R1 R2]].
     specialize (IHn _ _ _ R1).
     eapply rcomp_1 in R2.
     inv R2.
     all:cbn in *.
     specialize (tailRecursion_length P' a T0). omega.
     1,2:specialize (tailRecursion_length P a T0).
     1,2:omega.*)
  Admitted.
  
(* Damit: länge eines zustandes beschränkt durch (i+i)*(3*(i+1)+2*|s|)*)
  

End Analysis.
