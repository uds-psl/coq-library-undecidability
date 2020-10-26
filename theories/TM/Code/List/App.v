From Undecidability Require Import ProgrammingTools.
From Undecidability Require Import CaseNat CaseList CaseSum. (* [TM.Code.CaseSum] contains [Constr_Some] and [Constr_None]. *)

Local Arguments skipn { A } !n !l.
Local Arguments plus : simpl never.
Local Arguments mult : simpl never.

 
Local Arguments Encode_list : simpl never.
Local Arguments Encode_nat : simpl never.

Set Default Proof Using "Type".


From Undecidability Require Import TM.Basic.Mono TM.Code.Copy.



Lemma pair_eq (A B : Type) (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) ->
  a1 = a2 /\ b1 = b2.
Proof. intros H. now inv H. Qed.


Section ListStuff.
  Variable X : Type.

  (* TODO: -> base *)
  Lemma app_or_nil (xs : list X) :
    xs = nil \/ exists ys y, xs = ys ++ [y].
  Proof.
    induction xs as [ | x xs IH]; cbn in *.
    - now left.
    - destruct IH as [ -> | (ys&y&->) ].
      + right. exists nil, x. cbn. reflexivity.
      + right. exists (x :: ys), y. cbn. reflexivity.
  Qed.

  (* TODO: -> base *)
  Lemma map_removelast (A B : Type) (f : A -> B) (l : list A) :
    map f (removelast l) = removelast (map f l).
  Proof.
    induction l as [ | a l IH]; cbn in *; auto.
    destruct l as [ | a' l]; cbn in *; auto.
    f_equal. auto.
  Qed.

  (* TODO: -> base *)
  Corollary removelast_app_singleton (xs : list X) (x : X) :
    removelast (xs ++ [x]) = xs.
  Proof. destruct xs. reflexivity. rewrite removelast_app. cbn. rewrite app_nil_r. reflexivity. congruence. Qed.

  (* TODO: -> base *)
  Corollary removelast_cons (xs : list X) (x : X) :
    xs <> nil ->
    removelast (x :: xs) = x :: removelast xs.
  Proof. intros. change (x :: xs) with ([x] ++ xs). now rewrite removelast_app. Qed.


  (* TODO: -> base *)
  Corollary removelast_length (xs : list X) :
    length (removelast xs) = length xs - 1.
  Proof.
    destruct (app_or_nil xs) as [ -> | (x&xs'&->)].
    - cbn. reflexivity.
    - rewrite removelast_app_singleton. rewrite app_length. cbn. lia.
  Qed.

End ListStuff.


(** ** Append *)

(** I simply copy memory instead of using constructors/deconstructors. The former approach is maybe easier, but I want to use fewer internal tapes. *)
Section Append.

  Variable (sigX : finType) (X : Type) (cX : codable sigX X).
  Hypothesis (defX: inhabitedC sigX).

  Notation sigList := (FinType (EqType (sigList sigX))) (only parsing).

  Let stop : sigList^+ -> bool :=
    fun x => match x with
          | inl (START) => true (* halt at the start symbol *)
          | _ => false
          end.

  Definition App'_size {sigX X : Type} {cX : codable sigX X} (xs : list X) (s1 : nat) := s1 - (size (Encode_list cX) xs - 1).

  Definition App'_Rel : Rel (tapes sigList^+ 2) (unit * tapes sigList^+ 2) :=
    ignoreParam (fun tin tout =>
                   forall (xs ys : list X) (s0 s1 : nat),
                     tin[@Fin0] ≃(;s0) xs ->
                     tin[@Fin1] ≃(;s1) ys ->
                     tout[@Fin0] ≃(;s0) xs /\
                     tout[@Fin1] ≃(;App'_size xs s1) xs ++ ys).


  Definition App' : pTM sigList^+ unit 2 :=
    LiftTapes (MoveRight _;; Move Lmove;; Move Lmove) [|Fin0|];;
    CopySymbols_L stop.

  Lemma App'_Realise : App' ⊨ App'_Rel.
  Proof.
    eapply Realise_monotone.
    { unfold App'. TM_Correct.
      - apply MoveRight_Realise with (X := list X).
    }
    {
      intros tin ((), tout) H. cbn. intros xs ys s0 s1 HEncXs HEncYs.
      destruct HEncXs as (ls1&HEncXs&Hs0), HEncYs as (ls2&HEncYs&Hs1). TMSimp; clear_trivial_eqs.
      rename H into HMoveRight; rename H0 into HCopy.
      modpon HMoveRight. repeat econstructor. destruct HMoveRight as (ls3&HEncXs'). TMSimp.
      unfold App'_size in *.

      pose proof app_or_nil xs as [ -> | (xs'&x&->) ]; cbn in *; auto.
      - rewrite CopySymbols_L_Fun_equation in HCopy; cbn in *. inv HCopy; TMSimp. repeat econstructor.
        + lia.
        + rewrite Encode_list_hasSize. cbn. lia.
      - cbv [Encode_list] in *; cbn in *.
        rewrite encode_list_app in HCopy. cbn in *.
        rewrite !map_rev, !map_map, <- map_rev in HCopy.

        rewrite rev_app_distr in HCopy. rewrite <- tl_rev in HCopy. rewrite map_app, <- !app_assoc in HCopy.
        rewrite <- tl_map in HCopy. rewrite map_rev in HCopy. cbn in *. rewrite <- app_assoc in HCopy. cbn in *.
        rewrite !List.map_app, !List.map_map in HCopy. rewrite rev_app_distr in HCopy. cbn in *.
        rewrite map_rev, tl_rev in HCopy.

        rewrite app_comm_cons, app_assoc in HCopy. rewrite CopySymbols_L_correct_moveleft in HCopy; cbn in *; auto.
        + rewrite rev_app_distr, rev_involutive, <- app_assoc in HCopy. inv HCopy; TMSimp.
          * rewrite <- app_assoc. cbn. repeat econstructor.
            -- f_equal. cbn. rewrite encode_list_app. rewrite map_map, map_app, <- app_assoc.
               cbn.
               f_equal.
               ++ now rewrite rev_involutive, map_removelast.
               ++ f_equal. now rewrite map_app, List.map_map, <- app_assoc.
            -- lia.
            -- f_equal. cbn. rewrite rev_involutive, <- !app_assoc, !map_map. rewrite !encode_list_app. rewrite map_app, <- app_assoc.
               rewrite <- map_removelast. f_equal. cbn [encode_list].
               rewrite removelast_cons by (intros (?&?) % appendNil; congruence).
               cbn. f_equal.
               rewrite !map_app, <- !app_assoc.
               rewrite !removelast_app by congruence.
               now rewrite !map_app, <- !app_assoc, !map_map.
            -- simpl_list. rewrite encode_list_app. rewrite skipn_length. cbn. simpl_list. rewrite removelast_length. cbn. simpl_list. simpl_list. rewrite removelast_length. cbn. lia.
        + cbn.
          intros ? [ (?&<-&?) % in_rev % in_map_iff | H' % in_rev ] % in_app_iff. cbn. auto. cbn in *.
          rewrite rev_involutive, <- map_removelast in H'.
          apply in_app_iff in H' as [ (?&<-&?) % in_map_iff | [ <- | [] ] ]. all: auto.
    }
  Qed.



  Definition App'_steps {sigX X : Type} {cX : codable sigX X} (xs : list X) :=
    29 + 12 * size _ xs.

  Definition App'_T : tRel sigList^+ 2 :=
    fun tin k => exists (xs ys : list X), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ ys /\ App'_steps xs <= k.

  Lemma App'_Terminates : projT1 App' ↓ App'_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold App'. TM_Correct. (* This is a bit strange, because [App'] is a sequence of two sequences. *)
      - apply MoveRight_Realise with (X := list X).
      - apply MoveRight_Realise with (X := list X).
      - apply MoveRight_Terminates with (X := list X).
    }
    {
      intros tin k (xs&ys&HEncXS&HEncYs&Hk). unfold App'_steps in *.
      exists (12+4*size _ xs), (16+8*size _ xs). repeat split; cbn; try lia.
      exists (8+4*size _ xs), 3. repeat split; cbn; try lia. eauto.
      intros tmid1 () H. modpon H.
      exists 1, 1. repeat split; try lia. eauto.
      intros tmid (). intros H; TMSimp; clear_trivial_eqs. modpon H.
      destruct H as (ls&HEncXs); TMSimp.
      cbv [Encode_list]; cbn in *.

      destruct (app_or_nil xs) as [-> | (xs'&x&->)]; cbn in *.
      { (* [xs = nil] *)
        rewrite CopySymbols_L_steps_equation. cbn. lia.
      }
      { (* [xs = xs' ++ [x]] *)
        rewrite encode_list_app.
        rewrite map_rev, map_map, <- map_rev.
        rewrite rev_app_distr. cbn. rewrite <- app_assoc, rev_app_distr, <- app_assoc. cbn.
        rewrite CopySymbols_L_steps_moveleft; cbn; auto.
        rewrite map_length, !app_length, rev_length. cbn. rewrite map_length, rev_length, !app_length, !map_length. cbn.
        rewrite removelast_length. lia.
      }
    }
  Qed.


  Definition App : pTM sigList^+ unit 3 :=
    LiftTapes (CopyValue _) [|Fin1; Fin2|];;
    LiftTapes (App') [|Fin0; Fin2|].


  (*
  Lemma App_Computes : App ⊨ Computes2_Rel (@app X).
  Proof.
    eapply Realise_monotone.
    { unfold App. TM_Correct.
      - apply CopyValue_Realise with (X := list X).
      - apply App'_Realise.
    }
    {
      intros tin ((), tout) H. cbn. intros xs ys HEncXs HEncYs HOut _.
      TMSimp. rename H into HCopy; rename H0 into HComp.
      modpon HCopy. modpon HComp.
      repeat split; auto.
      - intros i; destruct_fin i.
    }
  Qed.
*)


  Definition App_steps {sigX X : Type} {cX : codable sigX X} (xs ys : list X) :=
    55 + 12 * size _ xs + 12 * size _ ys.


  Definition App_T : tRel sigList^+ 3 :=
    fun tin k => exists (xs ys : list X), tin[@Fin0] ≃ xs /\ tin[@Fin1] ≃ ys /\ isVoid tin[@Fin2] /\ App_steps xs ys <= k.

    
  Lemma App_Terminates : projT1 App ↓ App_T.
  Proof.
    eapply TerminatesIn_monotone.
    { unfold App. TM_Correct.
      - apply App'_Terminates.
    }
    {
      intros tin k (xs&ys&HEncXs&HEnYs&HRigh2&Hk).
      exists (25 + 12 * size _ ys), (App'_steps xs). repeat split; cbn; eauto.
      unfold App'_steps, App_steps in *. lia.
      intros tmid () (HApp'&HInjApp'); TMSimp.
      specialize (HApp' ys).
      modpon HApp'.
      hnf. cbn. do 2 eexists. repeat split; eauto.
    }
  Qed.

End Append.


Arguments App'_steps {sigX X cX} : simpl never.
Arguments App'_size {sigX X cX} : simpl never.

From Undecidability.L.Complexity Require Import UpToC.

Section App_nice.
  Variable (sigX X : Type) (cX : codable sigX X).

  Local Arguments size {sig X cX}.

  Lemma App'_steps_nice :
    App'_steps <=c size.
  Proof.
    eexists (29+12). intros xs. unfold App'_steps.
    rewrite Encode_list_hasSize. 
    specialize (Encode_list_hasSize_ge1 _ xs). nia.
  Qed.

End App_nice.