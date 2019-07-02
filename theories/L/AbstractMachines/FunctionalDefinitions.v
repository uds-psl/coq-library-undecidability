From Undecidability.L Require Import L Programs.
From Undecidability.L.AbstractMachines Require AbstractHeapMachineDef AbstractSubstMachine.
Import AbstractHeapMachineDef.clos_notation.

(** ** Functional definitions of the abstract machines *)

Section SubstMachine.
  Import AbstractSubstMachine.

     (** *** TODO: Size-aware space machine  *)

   Fixpoint substP_keepTrack' m sizeQ P k revQ (akk : Pro) (curSize : N) {struct P} : option Pro:=
    match P with
    | [] => Some (rev akk)
    | t :: P0 =>
      let '(d,Q',k) :=
          match t with
            varT k' => if k' =? k then (sizeQ,None,Some k)
                      else (N.of_nat (sizeT (varT k')),Some t,Some k)
          | appT => (1%N,Some t,Some k)
          | lamT => (1%N,Some t,Some (1 + k))
          | retT => (1%N,Some t,if (k =? 0) then None else (Some (k-1)))
          end
      in
      let curSize : N := (d + curSize)%N in
      if (curSize <=? m)%N
      then let akk := match Q' with
                        None => revQ++akk
                      | Some t => t::akk
                      end
           in
           match k with
             Some k => substP_keepTrack'  m sizeQ P0 k revQ akk curSize
           | None => Some (rev akk)
           end
      else None
          end.

   Lemma substP_keepTrack'_sound m sizeQ P k Q akk curSize R :
     substP_keepTrack' m sizeQ P k (rev Q) akk curSize = Some R ->
     R = rev akk ++ substP P k Q.
   Proof.
     induction P as [|? ? IH]in m,k,akk,R,curSize |-*.
     -cbn. intros [= ->]. eauto using app_nil_r.
     -cbn. all:repeat (let eq := fresh "eq" in destruct _ eqn:eq;try congruence);intros H.
      all:try inv eq.
      all:try (eapply IH in H). all:cbn in *. all:autorewrite with list in *. all:cbn in *.
      all:pose minus_n_O.
      all:try congruence.
   Qed.

   Local Ltac rev_smpl := repeat (cbn [List.app rev sumn map sizeT] in *;repeat autorewrite with list in * ).
                                  
   Lemma substP_keepTrack'_keepsTrack m P k Q akk curSize:
     (curSize + N.of_nat (sizeP (substP P k Q)) <= m)%N
     -> substP_keepTrack' m (N.of_nat (sumn (map sizeT Q))) P k (rev Q) akk curSize
       = Some (rev akk++substP P k Q).
   Proof.
     all:unfold sizeP in *.
     intros H2.
     induction P as [|? ? IH]in H2,m,k,akk,curSize |-*.
     all:cbn - [N.of_nat]in *.
     1:now cbn;rewrite app_nil_r.
     all:repeat (let eq := fresh "eq" in destruct _ eqn:eq;try congruence).
     all:repeat rewrite N.leb_le in *.
     all:repeat rewrite N.leb_gt in *.
     all:repeat rewrite Nat.eqb_eq in *.
     all:repeat rewrite Nat.eqb_neq in *.


     all:try inv eq.
     all:idtac;rev_smpl.
     all:try rewrite <- !minus_n_O in *.
     1-6:rewrite IH;[rev_smpl;try reflexivity| rev_smpl;try Lia.lia].
     all:try easy.
     all:exfalso. 
     all:rewrite !Nnat.Nat2N.inj_add in *.
     all:rewrite !Nnat.Nat2N.inj_succ in *.
     all:change (N.of_nat 0)%N with 0%N in *.
     all:try rewrite <- !N.add_1_l in *.
     all:try Lia.lia.
   Qed.
   
   Definition substP_keepTrack (m:N) curSize P k Q : option Pro:=
     substP_keepTrack' m (N.of_nat (sumn (map sizeT Q))) P k (rev Q) [] curSize.

   Lemma substP_keepTrack_correct m curSize P k Q :
     (N.of_nat (sizeP (substP P k Q)) + curSize <= m)%N
     -> substP_keepTrack m curSize P k Q = Some (substP P k Q).
   Proof.
     intro.
     unfold substP_keepTrack.
     rewrite substP_keepTrack'_keepsTrack.
     -reflexivity.
     -Lia.lia.
   Qed.   
   
   (*** Todo: track size of T,V*)

   Definition sizeTN (t : Tok) : N :=
     match t with
       varT k => 1 + N.of_nat k
     | _ => 1
     end.
   
   Fixpoint sumNmap' {X} (f: X -> N) A akk :=
     match A with
       [] => akk
     | a::A => sumNmap' f A (f a + akk)%N
     end.

   Definition sumNmap {X} (f: X -> _) A := sumNmap' f A 0%N.

   Definition sizePN P := sumNmap sizeTN P.

   Inductive substStepResult : Set :=
    EnoughSpace (x:list Pro * list Pro)
   | SpaceBoundReached.
   
   Definition substStep m '(T,V) : option substStepResult:=
     match T,V with
       (lamT::P)::T,_ => 
       match jumpTarget 0 [] P with
         Some (Q,P') => Some (EnoughSpace (tc P' T, Q :: V))
       | _ => None
       end
     | (appT :: P) :: T, Q :: R :: V =>
       let T:= tc P T in
       let curSize := (sumNmap sizePN T + sumNmap sizePN V)%N in
       match substP_keepTrack m curSize R 0 (lamT :: Q ++ [retT]) with
       | Some R' => Some (EnoughSpace (R' :: tc P T, V))
       | None => Some SpaceBoundReached
       end
     | _,_ => None
     end.
  
End SubstMachine.

Section HeapMachine.
  
  Import AbstractHeapMachineDef.
  Definition heapStep '(T,V,H) : option (list task * list clos * list heapEntry) :=
    match T with
    | closT (lam s, a) :: T =>
      Some (T, (s,a)::V, H)
    | appT :: T =>
      match V with
        g :: (s, b) :: V =>
        let '(H',c) := put H (heapEntryC g b) in
        Some (closT (s, c) :: T, V, H')
      | _ => None
      end
    | closT (var x, a) :: T =>
      match lookup H a x with
      | Some g => Some (T, g :: V, H)
      | _ => None
      end
    | closT (app s t, a) :: T =>
      Some (closT (s, a) :: closT (t, a) :: appT :: T, V,H)
    | [] => None
    end.


  
  Tactic Notation "destruct" "*" "eqn" :=
    let E := fresh "eq" in destruct * eqn:E.
  
  Lemma heapStep_sound: computesRel heapStep AbstractHeapMachineDef.step.
  Proof.
    intros x. unfold heapStep.
    repeat (destruct * eqn;subst;
            try match goal with
                  H : Some _ = Some _ |- _ => inv H
                | H : (_,_) = (_,_) |- _ => inv H
                | H : _ :: _ = _ :: _ |- _ => inv H
                | H : closT _ = closT _ |- _ => inv H
                | H : lam _ = lam _ |- _ => inv H

                end;
            eauto using AbstractHeapMachineDef.step).
    all:intros ? R'. all:inv R'. all:congruence.
  Qed.

End HeapMachine.
  

