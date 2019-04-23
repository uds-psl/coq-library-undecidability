From Undecidability.L Require Import L.
From Undecidability.L.AbstractMachines Require Import Programs AbstractHeapMachine AbstractSubstMachine.

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
                      else (N.of_nat (sizeT (varT k')),Some (varT k'),Some k)
          | appT => (1%N,Some appT,Some k)
          | lamT => (1%N,Some lamT,Some (1 + k))
          | retT => (1%N,Some retT,if (k =? 0) then None else (Some (k-1)))
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
  
  Import AbstractHeapMachine.
  Definition heapStep '(T,V,H) :=
    match T,V with
      (lamT :: P ,a) :: T, _ =>
      match jumpTarget 0 [] P with
        Some (Q,P') => Some ((P', a) :: T, (Q, a) :: V, H)
      | _ => None
      end
    | (appT :: P, a) :: T, g :: (Q, b) :: V =>
      let '(H',c) := put H (heapEntryC g b) in
      Some ((Q, c) :: (P, a) :: T, V, H')
    | (varT x :: P, a) :: T, _ =>
      match lookup H a x with
      | Some g => Some ((P, a) :: T, g :: V, H)
      | _ => None
      end
    | ([], a) :: T, _ => Some (T, V, H)
    | _,_ => None
    end.

End HeapMachine.
  

