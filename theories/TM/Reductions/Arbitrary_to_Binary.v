Require Export Undecidability.TM.Compound.TMTac.
Require Export Undecidability.TM.Basic.Mono Undecidability.TM.Compound.Multi.
Require Import Undecidability.TM.Combinators.Combinators.

Set Default Goal Selector "!".

Section fix_Sigma.

  Variable n : nat.

  Definition encode_sym (s : Fin.t n) : list bool :=
    let i := proj1_sig (Fin.to_nat s) in
    repeat false i ++ repeat true (n - i).

  Lemma encode_sym_inj s1 s2 : encode_sym s1 = encode_sym s2 -> s1 = s2.
  Proof.
    unfold encode_sym. intros H.
    eapply Fin.to_nat_inj. revert H.
    generalize (proj1_sig (Fin.to_nat s1)) (proj1_sig (Fin.to_nat s2)).
    intros n0. clear s1 s2. revert n. induction n0 as [|n0 IH].
    - now intros [|n] [|n1].
    - intros [|n] [|n1]; [easy| |easy|].
      + cbn. now intros [= ->%(IH 0)].
      + cbn. now intros [= ->%IH].
  Qed.
  
  Lemma length_encode_sym (s : Fin.t n) :
    length (encode_sym s) = n.
  Proof.
    unfold encode_sym. destruct Fin.to_nat as [i Hi].
    cbn. rewrite length_app, !repeat_length. lia.
  Qed.

  Fixpoint encode_string (s : list (Fin.t n)) :=
    match s with
    | [] => []
    | i :: l => false :: encode_sym i ++ true :: encode_string l
    end.

  Lemma encode_string_app s1 s2 :
    encode_string (s1 ++ s2) = encode_string s1 ++ encode_string s2.
  Proof. 
    induction s1; cbn.
    - reflexivity.
    - rewrite <-app_assoc. cbn. now rewrite IHs1.
  Qed. 
    
  Definition encode_tape (t : tape (Fin.t n)) :=
    match t with
    | niltape => niltape
    | midtape ls c_i rs => midtape (rev (encode_string (rev ls))) false (encode_sym c_i ++ true :: encode_string rs)
    | leftof c_i rs => leftof false (encode_sym c_i ++ true :: encode_string rs)
    | rightof c_i ls => rightof true (rev (encode_sym c_i) ++ false :: rev(encode_string (rev (ls))))
    end.

End fix_Sigma. 

Fixpoint ReadB (n : nat) : pTM (FinType (EqType bool)) (option (Fin.t n)) 1.
Proof.
  destruct n as [ | n ].
  - exact (Return Nop None).
  - refine (Switch ReadChar (fun o : option bool =>
                              match o with None => Return Nop None | Some _ =>
                                Move Rmove ;; Switch ReadChar (fun o : option bool  => 
                                match o with
                                | None => Return (Move Lmove) None
                                | Some true => Return (Move Lmove) (Some Fin.F1)
                                | Some false => Switch (ReadB n) (fun o => Return (Move Lmove) 
                                                                            (match o with
                                                                             | None => None
                                                                             | Some i => Some (Fin.R 1 i)
                                                                             end))
                                end)
                              end)).
Defined. (* because definition *)
  
Definition ReadB_rel' d n : Vector.t (tape bool) 1 -> option (Fin.t (d + n)) * Vector.t (tape bool) 1 -> Prop :=   
  fun t '(l, t') =>
    forall t_sig : tape (Fin.t n), t = [| encode_tape t_sig |] -> t' = t /\ forall s, current t_sig = Some s -> l = Some (Fin.R d s).

#[local] Hint Extern 0 => eassumption : TMdb.

Fixpoint ReadB_canonical n :
  {Rel | ReadB n ⊨ Rel}.
Proof.
  destruct n; cbn.
  - eexists. now auto with nocore TMdb.
  - eexists. eapply Switch_Realise. { now auto with nocore TMdb. }
    cbn in *. intros [ | ].
    + instantiate (1 := fun o => match o with None => _ | Some _ => _ end).
      eapply Seq_Realise. { now auto with nocore TMdb. }
      eapply Switch_Realise. { now auto with nocore TMdb. }
      cbn in *. intros [[] | ].
      * instantiate (1 := fun o => match o with None => _ | Some true => _ | Some false => _ end). cbn in *.
      now auto with nocore TMdb.
      * eapply Switch_Realise.
        -- eapply (proj2_sig (ReadB_canonical n)).
        -- instantiate (1 := fun o => match o with None => _ | Some _ => _ end).
           intros []; now auto with nocore TMdb.
      * now auto with nocore TMdb.
    + now auto with nocore TMdb. 
Defined. (* because definition *)

Lemma ReadB_Realise n :
  ReadB n ⊨ fun t '(l, t') => forall t_sig : tape (Fin.t n), t = [| encode_tape t_sig |] -> t' = t /\ l = current t_sig.
Proof.
  eapply Realise_monotone. { exact (proj2_sig (ReadB_canonical n)). }
  pose (Rel := (fun n (t : Vector.t _ 1) '(l, t') => 
  match t with 
  | [| midtape ls _ rs |] => forall rs' (c_i : Fin.t n), rs = encode_sym c_i ++ rs' ->
        t' = t /\ l = Some c_i  
  | _ => t' = t /\ l = None
  end) : forall n, Vector.t (tape bool) 1 -> option (Fin.t n) * Vector.t (tape bool) 1 -> Prop).
  transitivity (Rel n).
  - induction n.
    + subst Rel. cbn. intros tp (l, t') (-> & [ _ ->]).
      eapply Vector.caseS' with (v := tp). clear tp. intros t nl.
      eapply Vector.case0 with (v := nl). clear nl. destruct t; eauto.
      intros rs' c_i ->. inv c_i.
    + intros t (l, t') (? & tright & (-> & ->) & H).
      rewrite (destruct_tape t) in *. cbn in *.
      destruct (Vector.hd t); cbn in *.
      * now destruct H as (-> & [] & ->).
      * now destruct H as (-> & [] & ->).
      * now destruct H as (-> & [] & ->).
      * intros rs' c_i ->.
        destruct H as ([] & tps & ? & ? & tps' & [-> ->] & H0).
        rewrite (destruct_tape tps) in *. cbn in *.
        rename l0 into ls.
        revert H0. rewrite H. clear H.
        rewrite (destruct_tape t').
        eapply Fin.caseS' with (p := c_i); clear c_i.
        -- cbn. now intros (-> & [] & <-).
        -- intros c_i. change (Fin.FS c_i) with (Fin.R 1 c_i) in *.
           unfold encode_sym. cbn in *. 
           pose proof (Fin.R_sanity 1 c_i) as E. cbn in E.
           rewrite E. clear E. cbn.
           intros (o & tout & ? & ?). eapply IHn in H. cbn in H.
           destruct (H _ _ eq_refl) as [-> ->]. cbn in *.
           now destruct H0 as (-> & [] & <-).
  - intros t (l, t'). unfold Rel. intros H.
    intros t_sig ->. destruct t_sig; cbn in *; eauto.
Qed.

Definition isTotal {Σ} {L} {n} (M : pTM Σ L n) := exists c, projT1 M ↓ fun t k => c <= k.

Lemma ReadB_total n :
  isTotal (ReadB n).
Proof. 
  induction n. 
  - cbn. exists 0. eapply TerminatesIn_monotone. { now auto with nocore TMdb. }
    intros ? ? H. exact H.
  - destruct IHn as [c IH].
    eexists. eapply TerminatesIn_monotone. { cbn.
    eapply Switch_TerminatesIn; [now auto with nocore TMdb..|].
    intros []. { instantiate (1 := fun f => if f then _ else _). cbn.
    instantiate (1 := ltac:(clear f; refine _)).
    eapply Seq_TerminatesIn; [now auto with nocore TMdb..|].
    eapply Switch_TerminatesIn; [now auto with nocore TMdb..|].
    intros []. { instantiate (1 := fun f => match f with Some true => _ | Some false => _ | None => _ end). cbn.
    destruct b0 as [ | ].
    + cbn. instantiate (1 := ltac:(clear f b0; refine _)).
      now auto with nocore TMdb.
    + instantiate (1 := ltac:(clear f b0; refine _)).
      eapply Switch_TerminatesIn. { eapply ReadB_Realise. } { eassumption. }
      intros []. { cbn. 
      instantiate (1 := fun f => if f then _ else _). cbn. now auto with nocore TMdb. }
      now auto with nocore TMdb. }
    cbn. instantiate (1 := ltac:(clear f; refine _)).  now auto with nocore TMdb. }
    cbn. instantiate (1 := ltac:(clear f; refine _)).  now auto with nocore TMdb. }
    cbn. intros ? ? ?. exists 1. eexists. split.
      { lia. } split. 2:{ intros. TMSimp.
      destruct (current _).
      * exists 1. eexists. split. { lia. } split. 2:{ intros. TMSimp.
        exists 1. eexists. split. { lia. } split. 2:{ intros. TMSimp.
        destruct current. { destruct b0. { instantiate (1 := S _). lia. }
        exists c. eexists. split. { lia. } split. 2:{ intros. destruct yout; apply Nat.le_refl. }
        apply Nat.le_refl. }
        lia. }
        apply Nat.le_refl. }
        apply Nat.le_refl. 
      * lia. } eapply H.
Qed.

Require Import Undecidability.TM.Compound.WriteString.

Fixpoint MoveM {Σ : finType} (D : move) (n : nat) : pTM Σ unit 1 :=
  match n with 
  | 0 => Nop
  | S n => MoveM D n ;; Move D
  end.

Definition TestLeftof {Σ : finType} : pTM Σ bool 1 :=
  Switch ReadChar (fun s1 => match s1 with Some _ => Return Nop false | None => Move Rmove ;; Switch ReadChar (fun s2 => match s2 with None => Return Nop false | Some _ => Return (Move Lmove) true end) end).

Lemma TestLeftof_Realise {Σ : finType} : 
  @TestLeftof Σ ⊨ fun t '(b, t') => t = t' /\ match t with [| leftof _ _ |] => b = true | _ => b = false end.
Proof.
  eapply Realise_monotone.
  { unfold TestLeftof. apply Switch_Realise; [now auto with nocore TMdb|].
    instantiate (1 := fun x => if x then _ else _).
    intros [].
    - now auto with nocore TMdb.
    - apply Switch_Realise; [now auto with nocore TMdb|].
      intros ?. instantiate (1 := fun x => _).
      apply Switch_Realise; [now auto with nocore TMdb|].
      instantiate (1 := fun x => if x then _ else _).
      intros []; now auto with nocore TMdb. }
  intros t (b, t') ?. TMSimp. rename t_0 into t.
  destruct t; cbn in *; TMSimp; eauto.
Qed.

#[local] Hint Extern 1 (TestLeftof ⊨ _) => eapply TestLeftof_Realise : TMdb.

Definition MoveL_rel {Σ : finType} D (n : nat) : Vector.t (tape Σ) 1 -> unit * Vector.t (tape Σ) 1 -> Prop := 
  fun t '(_, t') => t' = Vector.map (Nat.iter n (fun t => @tape_move Σ t D)) t.

Lemma MoveM_Realise {Σ : finType} D (n : nat) :
  @MoveM Σ D n ⊨ MoveL_rel D n.
Proof.
  induction n; unfold MoveL_rel; cbn.
  - eapply Realise_monotone. { now auto with nocore TMdb. }
    intros t ([], t') ->.
    rewrite (destruct_tape t). reflexivity.
  - eapply Realise_monotone. { eapply Seq_Realise. { eassumption. }
    { now auto with nocore TMdb. } }
    intros t ([], t') ?; cbn in *. TMSimp. reflexivity.
Qed.

#[local] Hint Extern 1 (MoveM _ _ ⊨ _) => eapply MoveM_Realise : TMdb.

Definition WriteB (n : nat) (c : option (Fin.t n)) : pTM (FinType (EqType bool)) unit 1 :=
  match c with
  | None => Nop
  | Some c => 
    Switch TestLeftof (fun b => if b then WriteString Lmove (rev (false :: encode_sym c ++ [true])) else
      WriteString Rmove (false :: encode_sym c ++ [true]) ;; MoveM Lmove (S n))
  end.

Lemma Nat_iter_S' {A} (f : A -> A) (a : A) n :
  Nat.iter (S n) f a = f (Nat.iter n f a).
Proof.
  reflexivity.
Qed.

Lemma Nat_iter_S {A} (f : A -> A) (a : A) n :
   Nat.iter (S n) f a = Nat.iter n f (f a).
Proof.
  induction n in a |- *; cbn.
  - reflexivity.
  - unfold Nat.iter in IHn. now rewrite <- IHn.
Qed.

Lemma Nat_iter_id {A} (a : A) n :
   Nat.iter n (fun a : A => a) a = a.
Proof.
  induction n in a |- *; cbn.
  - reflexivity.
  - unfold Nat.iter in IHn. now rewrite <- IHn.
Qed.

Lemma WriteString_MoveBack {Σ : finType} (x : Σ) l :
  (WriteString Rmove (x :: l) ;; MoveM Lmove (|l|)) ⊨ fun t '(_, t') => t' = Vector.map (fun t => midtape (left t) x (l ++ skipn (|l|) (right t))) t.
Proof.
  eapply Realise_monotone. { now auto with nocore TMdb. }
  intros t ([], t') ([] & t1 & ? & ?). TMSimp. f_equal. rename t_0 into t.
  induction l in x, t |- *.
  - reflexivity.
  - cbn [length plus]. rewrite Nat_iter_S'.
    rewrite WriteString_Fun_eq. setoid_rewrite IHl. clear. 
    destruct t; cbn.
    + now rewrite skipn_nil.
    + reflexivity.
    + now rewrite skipn_nil. 
    + unfold tape_move_left'. unfold tape_move_right'. cbn. destruct l1; cbn.
      * now rewrite skipn_nil.
      * reflexivity.
Qed.


Lemma WriteB_Realise (n : nat) (c : option (Fin.t n)) :
  WriteB c ⊨ fun t '(_, t') => forall t_sig, t = [| encode_tape t_sig |] -> t' = [| encode_tape (wr c t_sig) |].
Proof.
  destruct c as [c | ].
  - eapply Realise_monotone. { unfold WriteB. eapply Switch_Realise. {
    eapply TestLeftof_Realise. } intros []. { instantiate (1 := fun b => if b then _ else _).
    cbn. eapply RealiseIn_Realise, WriteString_Sem. }
    pose proof (@WriteString_MoveBack (finType_CS bool) false (encode_sym c ++ [true])). cbn in H.
    replace (|encode_sym c ++ [true]|) with (S n) in H. 2:rewrite length_app, length_encode_sym; cbn; lia. cbn.
    eapply H. }
    intros t ([], t') ? ? ->. TMSimp. f_equal.
    destruct t_sig eqn:E; cbn - [skipn].
    + cbn in *. TMSimp. now rewrite app_nil_r.
    + cbn in *. TMSimp. generalize (encode_sym t ++ true :: encode_string l). clear. intros.
      replace (encode_sym c ++ true :: false :: l) with ((encode_sym c ++ [true]) ++ false :: l).
      { generalize (encode_sym c ++ [true]). generalize false. intros.
      generalize b at 1 4. intros.
      induction l0 in b0, b, l |- * using rev_ind; cbn.
      * reflexivity.
      * rewrite rev_app_distr. cbn. rewrite WriteString_Fun_eq.
        destruct l0 as [ | x0 l0 _] using rev_ind.
        -- cbn. reflexivity.
        -- rewrite rev_app_distr. cbn. rewrite <- !app_assoc.
           specialize (IHl0 (b0 :: l) b x). rewrite rev_app_distr in IHl0.
           cbn in *. rewrite <- app_assoc in IHl0. cbn in IHl0. eassumption. }
      now rewrite <- app_assoc.
    + cbn in *. TMSimp. rewrite <- app_assoc. cbn. repeat  f_equal. rewrite encode_string_app. cbn.
      rewrite !rev_app_distr. cbn. rewrite rev_app_distr. cbn. now rewrite <- app_assoc.
    + cbn in *. TMSimp. rewrite <- app_assoc. cbn -[skipn]. repeat f_equal.
      replace (encode_sym t ++ true :: encode_string l0) with ((encode_sym t ++ [true]) ++ encode_string l0).
      { pose proof (length_encode_sym t).
      destruct (encode_sym) eqn:E.
      * cbn in *. subst. reflexivity.
      * cbn in *. inv H. rewrite skipn_app.
        generalize (encode_string l0). intros ?.
        replace (S (length l1 )) with (length (l1 ++ [true])).
        { now rewrite Nat.sub_diag, skipn_all. }
        rewrite length_app. simpl. lia. }
      now rewrite <- app_assoc.
  - cbn. eapply Realise_monotone. { now auto with nocore TMdb. }
    intros t ([], t') ->. eauto.
Qed.

Lemma MoveM_isTotal {Σ : finType} D (n : nat) :
  isTotal (@MoveM Σ D n).
Proof.
  induction n; cbn.
  - eexists. now auto with nocore TMdb.
  - destruct IHn as [c IH]. eexists. eapply TerminatesIn_monotone.
    { now auto with nocore TMdb. }
    intros ? ? ?.
    repeat eexists. { apply Nat.le_refl. }
    { eapply H. }
    intros. apply Nat.le_refl.
Qed.

Lemma TestLeftof_total {Σ} :
  isTotal (@TestLeftof Σ).
Proof.
  unfold TestLeftof.
  eexists. eapply TerminatesIn_monotone.
  { eapply Switch_TerminatesIn; [now auto with nocore TMdb..|].
    instantiate (1 := fun x => if x then _ else ltac:(clear x; refine _)).
    intros []; [now auto with nocore TMdb..|].
    apply Seq_TerminatesIn; [now auto with nocore TMdb..|].
    eapply Switch_TerminatesIn; [now auto with nocore TMdb..|].
    instantiate (1 := fun x => if x then _ else _).
    intros []; now auto with nocore TMdb. }
  intros ? ? ?. exists 1, 5. split; [apply Nat.le_refl|].
  split; [apply H|]. intros tout yout.
  rewrite (destruct_tape tout). cbn.
  intros [-> <-]. destruct current; [apply Nat.le_0_l|].
  exists 1, 3. split; [apply Nat.le_refl|].
  split; [apply Nat.le_refl|].
  intros tout' _. rewrite (destruct_tape tout'). cbn.
  intros ->.
  exists 1, 1. split; [apply Nat.le_refl|].
  split; [apply Nat.le_refl|].
  intros ? ? [-> ?]. destruct current; lia.
Qed.

Lemma WriteB_TerminatesIn (n : nat) (c : option (Fin.t n)) :
  isTotal (WriteB c).
Proof.
  destruct (@MoveM_isTotal (finType_CS bool) Lmove n) as [MoveM_c H_MoveM].
  destruct (@TestLeftof_total (finType_CS bool)) as [kT HT].
  red. eexists. eapply TerminatesIn_monotone.
  { unfold WriteB. destruct c; cbn.
  - instantiate (1 := ltac:(destruct c; refine _ )). cbn.
    apply Switch_TerminatesIn; [now auto with nocore TMdb..|].
    instantiate (1 := fun x => if x then _ else _).
    intros []; now auto with nocore TMdb.
  - cbn. now auto with nocore TMdb. }
  cbn. intros ? ? ?. destruct c; cbn.
    + repeat eexists. { eapply Nat.le_refl. }
      { unshelve eapply (Nat.le_trans _ _ _ _ H).
      eapply Nat.le_refl. }
      intros. TMSimp. destruct yout.
      * cbn. repeat (rewrite !length_app, ?length_rev, ?length_encode_sym; cbn). eapply Nat.le_add_r.
      * repeat eexists. { eapply Nat.le_refl. }
        { repeat (rewrite !length_app, ?length_rev, ?length_encode_sym; cbn).
        eapply Nat.le_add_l. }
        { eapply Nat.le_refl. } { eapply Nat.le_refl. }
        intros. eapply Nat.le_refl.
    + lia.
Qed.


Definition MoveB (m : move) n : pTM (finType_CS bool) unit 1 :=
  Switch TestLeftof (fun b => match b, m with 
                              | true, Rmove => Move Rmove 
                              | _, _ => MoveM m (2 + n)
                              end).
  
Arguments Nat.iter : simpl never.
Opaque Nat.iter.

Lemma midtape_left_midtape {Σ : finType} (l1 l2 : list Σ) m m' r n :
  n = S (length l1) -> 
  Nat.iter n (@tape_move_left Σ) (midtape (rev l1 ++ [m'] ++ l2) m r) = midtape l2 m' (l1 ++ m :: r).
Proof.
  intros ->. induction l1 in m, m', l2 |- *.
  - cbn. reflexivity.
  - cbn. rewrite <- app_assoc. rewrite Nat_iter_S'.
    now rewrite (IHl1 (m' :: l2) m a).
Qed.

Lemma midtape_right_midtape {Σ : finType} l m r1 c r2 n :
  n = S (length r1) -> 
  Nat.iter n (@tape_move_right Σ) (midtape l m (r1 ++ c :: r2)) = midtape (rev r1 ++ m :: l) c r2.
Proof. 
  intros ->. induction r1 in m, c, r2 |- * using rev_ind; cbn.
  - reflexivity.
  - rewrite length_app. cbn. rewrite Nat.add_comm. cbn.
    rewrite <- app_assoc, Nat_iter_S'. cbn.
    rewrite (IHr1 m x (c :: r2)). cbn. now rewrite rev_app_distr.
Qed.

Lemma midtape_right_rightof {Σ : finType} l m rs c n :
  n = 2 + (length rs) ->
  Nat.iter n (@tape_move_right Σ) (midtape l m (rs ++ [c])) = rightof c (rev rs ++ m :: l).
Proof. 
  intros ->. cbn. rewrite Nat_iter_S'.
  rewrite midtape_right_midtape; reflexivity.
Qed.

Lemma MoveB_Realise (n : nat) m :
  MoveB m n ⊨ fun t '(l, t') => forall t_sig, t = [| encode_tape t_sig |] -> t' = [| @encode_tape n (mv m t_sig) |].
Proof.
  epose (R := _). eapply Realise_monotone. 
  { unfold MoveB.
    eapply Switch_Realise. { eapply TestLeftof_Realise. } 
    instantiate (1 := R m). subst R. 
    instantiate (1 := fun m b => if b then _ else _). cbn.
    intros []. { cbn. instantiate (1 := match m0 with Rmove => _ | _ => _ end). cbn. destruct m.
    all: now auto with nocore TMdb. } now auto with nocore TMdb. }
    subst R.

  assert (forall n c rs, Nat.iter n (fun t : tape bool  => tape_move_left t) (leftof c rs) = leftof c rs) as Eleft. {
    clear. intros. clear. induction  n; cbn. { reflexivity. } rewrite Nat_iter_S', IHn. reflexivity. }

  intros t ([], t') ? t_sig ->. TMSimp. f_equal.
  destruct t_sig.
  - TMSimp.
    assert (Nat.iter n (fun t : tape bool  => tape_move t m) niltape = niltape) as ->.
    { induction  n; cbn. { reflexivity. } rewrite Nat_iter_S', IHn. now destruct m. }
    now destruct m.
  - cbn in *. TMSimp. destruct m.
    + TMSimp. now rewrite Eleft.
    + TMSimp. reflexivity.
    + TMSimp. now rewrite Nat_iter_id.
  - TMSimp.
    destruct m.
    + cbn. rewrite <- !Nat_iter_S' with (f := fun t0 => tape_move_left t0).
      rewrite Nat_iter_S. cbn.
      pose proof (@midtape_left_midtape (finType_CS bool)). cbn in H. erewrite <- H. 
      2: reflexivity. rewrite Nat_iter_S'. rewrite length_encode_sym. reflexivity.
    + enough (forall c rs, Nat.iter n (fun t : tape bool  => tape_move_right t) (rightof c rs) = rightof c rs) as -> by reflexivity.
      intros. clear. induction  n; cbn. { reflexivity. } rewrite Nat_iter_S', IHn. reflexivity.
    + now rewrite Nat_iter_id.
  - TMSimp. rename l into rs, l0 into ls.
    rewrite <- !Nat_iter_S' with (f := fun t0 => tape_move t0 m).
    destruct m.
    + cbn. destruct rs.
      * cbn. rewrite Nat_iter_S. cbn. now rewrite Eleft.
      * cbn. pose proof (@midtape_left_midtape (finType_CS bool)). cbn in H.
        rewrite encode_string_app, rev_app_distr. cbn. rewrite rev_app_distr. cbn.
        rewrite Nat_iter_S. cbn. rewrite <- app_assoc. 
        erewrite <- H. 2:reflexivity. rewrite length_encode_sym. reflexivity.
    + cbn. destruct ls.
      * cbn.
        pose proof (@midtape_right_rightof (finType_CS bool)). cbn in H.
        rewrite H. 2:now rewrite length_encode_sym. reflexivity.
      * cbn. rewrite Nat_iter_S'.
        pose proof (@midtape_right_midtape (finType_CS bool)). cbn in H.
        rewrite H. { cbn. rewrite encode_string_app. cbn. rewrite !rev_app_distr. cbn.
        rewrite rev_app_distr. cbn. rewrite <- app_assoc. reflexivity. }
        now rewrite length_encode_sym.
    + cbn. rewrite Nat_iter_id. reflexivity.
Qed.

Lemma MoveB_total (n : nat) :
  exists c, forall m, projT1 (MoveB m n) ↓ fun t k => c <= k.
Proof.
  destruct (@TestLeftof_total (finType_CS bool)) as [c Hlo].
  destruct (@MoveM_isTotal (finType_CS bool) Lmove n) as [c1 H1].
  destruct (@MoveM_isTotal (finType_CS bool) Nmove n) as [c2 H2].
  destruct (@MoveM_isTotal (finType_CS bool) Rmove n) as [c3 H3].
  assert (forall m, projT1 (MoveM m n) ↓ (fun (_ : tapes (finType_CS bool) 1) (k : nat) => c1+c2+c3 <= k)) as HMoveM.
  { intros []; eapply TerminatesIn_monotone; try eassumption.
    all: intros ??; lia. }
  eexists. intros m. specialize (HMoveM m).
  eapply TerminatesIn_monotone.
  { unfold MoveB. eapply Switch_TerminatesIn; [now auto with nocore TMdb..|].
    intros f. instantiate (1 := fun f => if f then _ else _).
    destruct f.
    - destruct m.
      { instantiate (1 := ltac:(destruct m, f; refine _)). all: cbn.
      all: now auto with nocore TMdb. }
      all: cbn; now auto with nocore TMdb.
    - instantiate (1 := ltac:(destruct f; refine _)); cbn.
      now auto with nocore TMdb. }
  intros ? ? ?. repeat eexists.
  { eapply Nat.le_refl. }
  { unshelve eapply (Nat.le_trans _ _ _ _ H).
    { eapply Nat.le_refl. } }
  intros. cbn. TMSimp. destruct yout.
  + destruct m; cbn.
    * repeat eexists. all: intros; (try apply Nat.le_refl); lia.
    * lia.
    * repeat eexists. all: intros; (try apply Nat.le_refl); lia.
  + repeat eexists. all: intros; (try apply Nat.le_refl); lia.
  Unshelve.
  all: exact (fun _ _ => True).
Qed.


(* Specialized Facts *)
Lemma fintype_forall_exists (F : finType) (P : F -> nat -> Prop) :
  (forall x n, P x n -> forall m, m >= n -> P x m) ->
  (forall x : F, exists n, P x n) -> exists N, forall x, P x N.
Proof.
  intros P_mono FE. destruct (fintype_choice FE) as [f Hf].
  exists (list_sum (map f (elem F))).
  intros x. apply (P_mono x _ (Hf x)).
  destruct (in_split _ _ (elem_spec x)) as [? [? ->]].
  rewrite map_app, list_sum_app. cbn. lia.
Qed.

Section FixM.

  Variable Σ : finType.

  Let n := (projT1 (finite_n Σ)).
  Let f := (projT1 (projT2 (finite_n Σ))).
  Let g := (proj1_sig (projT2 (projT2 (finite_n Σ)))).
  Let Hf := (proj1 (proj2_sig (projT2 (projT2 (finite_n Σ))))).
  Let Hg := (proj2 (proj2_sig (projT2 (projT2 (finite_n Σ))))).

  Definition encode_tape' (t : tape Σ) : tape bool := encode_tape (mapTape f t).

  Lemma ReadB_Realise' :
    ReadB n ⊨ fun t '(l, t') => forall t_sig : tape Σ, t = [| encode_tape' t_sig |] -> t' = t /\ l = map_opt f (current t_sig).
  Proof.
    eapply Realise_monotone. { eapply ReadB_Realise. }
    intros t (?, t') ? t_sig ->. rewrite (destruct_tape t') in *.
    specialize (H (mapTape f t_sig) eq_refl) as [-> ->].
    split; [reflexivity|]. eapply mapTape_current.
  Qed.

  Lemma WriteB_Realise' (c : option Σ) :
    WriteB (map_opt f c) ⊨ fun t '(_, t') => forall t_sig, t = [| encode_tape' t_sig |] -> t' = [| encode_tape' (wr c t_sig) |].
  Proof.
    eapply Realise_monotone. { eapply WriteB_Realise. }
    intros t (?, t') ? t_sig ->. rewrite (destruct_tape t') in *.
    specialize (H (mapTape f t_sig) eq_refl) as ->.
    unfold tape_write. destruct c.
    - cbn. destruct t_sig; reflexivity.
    - reflexivity.
  Qed.

  Lemma MoveB_Realise' m :
    MoveB m n ⊨ fun t '(l, t') => forall t_sig, t = [| encode_tape' t_sig |] -> t' = [| encode_tape' (mv m t_sig) |].
  Proof.
    eapply Realise_monotone. { eapply MoveB_Realise. }
    intros t (?, t') ? t_sig ->. rewrite (destruct_tape t') in *.
    specialize (H (mapTape f t_sig) eq_refl) as ->.
    f_equal. destruct t_sig, m; try reflexivity.
    - cbn. destruct l; cbn; reflexivity.
    - cbn. destruct l0; cbn; reflexivity.
  Qed.

  Variable M : TM Σ 1.

  Definition Step (q : state M) : pTM (finType_CS bool) (state M + state M) 1 :=
        Switch (ReadB n) (fun c_i => if halt q then Return Nop (inr q) 
                                     else let '(q', e) := trans M (q, [| map_opt g c_i |]) in 
                                          let '(c', m) := Vector.hd e in
                                          WriteB (map_opt f c') ;; MoveB m n ;; Return Nop (inl q')).

  #[local] Hint Extern 1 (ReadB _ ⊨ _) => eapply ReadB_Realise' : TMdb.
  #[local] Hint Extern 1 (WriteB _ ⊨ _) => eapply WriteB_Realise' : TMdb.
  #[local] Hint Extern 1 (MoveB _ _ ⊨ _) => eapply MoveB_Realise' : TMdb.

  Lemma Step_Realise q :
    Step q ⊨ fun t '(q_, t') => 
      forall t_sig, t = [| encode_tape' t_sig |] ->
      if halt q then q_ = inr q /\ t' = t 
                else let '(q', a) := trans M (q, [| current t_sig |]) in 
                     let '(c', m) := Vector.hd a in
                     q_ = inl q' /\ t' = [| encode_tape' (mv m (wr c' t_sig)) |].
  Proof.
    eapply Realise_monotone.

    {
      unfold Step. eapply Switch_Realise. { now auto with nocore TMdb. } cbn.
      intros c_i. instantiate (1 := fun c_i => _). cbn. instantiate (1 := ltac:(destruct (halt q); refine _)).
      destruct (halt q). { cbn. now auto with nocore TMdb. } 
      instantiate (1 := ltac:(destruct (trans (q, [|map_opt g c_i|])); refine _)). cbn.
      destruct (trans (q, [|map_opt g c_i|])).
      instantiate (1 := ltac:(destruct (Vector.hd t))).
      destruct (Vector.hd t). now auto with nocore TMdb.
    }

    intros t (q_, t') ? t_sig ->. TMSimp. 
    rename t'_0 into t'.
    destruct (halt q) eqn:Eq.
    - TMSimp. split. { reflexivity. } eapply H. reflexivity.
    - specialize (H _ eq_refl) as [[= ->] ->]. cbn in *.
      assert (Efg : forall o, map_opt g (map_opt f o) = o). { intros [s | ]; cbn; now rewrite ?Hg.  }
      rewrite Efg in H0. clear Efg.    
      destruct trans as [q' T] eqn:Eqt.
      destruct Vector.hd as [c' m].
      TMSimp. split. { reflexivity. }
      now eapply H0, H.
  Qed.

  #[local] Hint Extern 1 (Step _ ⊨ _) => eapply Step_Realise : TMdb.

  Lemma WriteB_total'  :
    exists C, forall (c : option (Fin.t n)), projT1 (WriteB c) ↓ fun t k => k >= C.
  Proof.
    eapply fintype_forall_exists; cbn.
    - intros. eapply TerminatesIn_monotone. { eassumption. } 
      intros ? ? ?. lia.
    - eapply WriteB_TerminatesIn.
  Qed.

  Lemma Step_total q :
    isTotal (Step q).
  Proof.
    destruct (MoveB_total n).
    destruct (ReadB_total n).
    destruct (WriteB_total').
    eexists. eapply TerminatesIn_monotone.
    - unfold Step. eapply Switch_TerminatesIn.
      { now auto with nocore TMdb. } { eassumption. } cbn.
      intros c_i. instantiate (1 := ltac:(intros c_i; refine _)); cbn.
      instantiate (1 := ltac:(destruct (halt q); refine _)); cbn.
      destruct halt.
      { now auto with nocore TMdb. }
      instantiate (1 := ltac:(destruct (trans (q, [| map_opt g c_i |])) as [? t],
      (Vector.hd t))).
      destruct (trans (q, [| map_opt g c_i |])); cbn.
      destruct (Vector.hd t).
      now auto with nocore TMdb.
    - cbn. intros ? ? ?. repeat eexists. { apply Nat.le_refl. }
      { eapply H2. }
      intros.
      instantiate (1 := ltac:(destruct (halt q))); cbn.
      destruct halt. { apply Nat.le_0_l. } rename yout into c_i.
      destruct (trans (q, [| map_opt g c_i |])); cbn.
      destruct (Vector.hd t); cbn.
      repeat eexists.
      { apply Nat.le_refl. } { apply Nat.le_refl. } { apply Nat.le_refl. }
      { apply Nat.le_refl. } intros. apply Nat.le_0_l.
    Unshelve.
    all: exact 0.
  Qed.

  Lemma Step_total' :
    exists C, forall q, projT1 (Step q) ↓ fun t k => C <= k.
  Proof.
    eapply fintype_forall_exists.
    - intros. eapply TerminatesIn_monotone. { eassumption. } intros ? ?. lia.
    - intros q. eapply Step_total.
  Qed.

  Theorem WhileStep_Realise :
    StateWhile Step (start M) ⊨ 
      fun t '(q', t') => forall t_sig, t = [| encode_tape' t_sig |] -> exists t_sig', eval M (start M) [| t_sig |] q' [| t_sig' |] /\ t' = [| encode_tape' t_sig'|].
  Proof.
    generalize (start M). intros q.

    eapply Realise_monotone.
    { now auto with nocore TMdb. }

    intros t (l, t') ? t_sig E.
    TMSimp. unfold tapes in *. rename t'_0 into t'.
    remember ([|encode_tape' t_sig|]) as tin.
    remember (l, [|t'|]) as cout.
    induction H in t_sig, l, t', Heqtin, Heqcout |- *.
    - TMSimp. specialize (H _ eq_refl).
      rename l0 into q. destruct (halt q) eqn:Eq.
      + inv Heqcout. destruct H as [[= ->] [= ->]].
      + inv Heqcout. destruct trans as [q' T] eqn:Eqt.
        rewrite (destruct_vector_single T) in *.
        destruct (Vector.hd T) as [c' m] eqn:ET.
        destruct H as [[= ->] [= ->]].
        specialize (IHStateWhile_Rel _ _ _ eq_refl eq_refl) as [t_sig' [H1 [= ->]]].
        exists t_sig'. split; try reflexivity.
        econstructor; eassumption.
    - inv Heqcout. specialize (H _ eq_refl).
      rename l0 into q. destruct (halt q) eqn:Eq.
      + destruct H as [[= ->] [= ->]]. eexists; split; try reflexivity.
        now econstructor.
      + destruct trans as [q' T] eqn:Eqt.
        destruct Vector.hd as [c' m].
        destruct H as [[= ->] [= ->]].
  Qed.


  Theorem WhileStep_Terminates :
   exists C1 C2,
    projT1 (StateWhile Step (start M)) ↓ fun t k => 
            exists t_sig, t = [| encode_tape' t_sig |] /\ 
            exists k' t_sig' q', loopM (initc M [| t_sig |]) k' = Some (mk_mconfig q' [| t_sig' |] ) /\
             k >= C1 * k' + C2.
  Proof.
    unfold initc.
    generalize (start M). intros q.
    destruct (Step_total') as [C HC].
    exists (1 + C), (2 + 2 * C).
    eapply TerminatesIn_monotone.
    {
      eapply StateWhile_TerminatesIn. { intros. eapply Step_Realise. } intros. eapply HC.
    }
    revert q. eapply StateWhileCoInduction.
    intros q tin k H. TMSimp.
    rename ymid0 into steps, ymid into t_sig, ymid1 into t_sig', ymid2 into q'.
    remember [|t_sig|] as tin. remember [|t_sig'|] as tout.
    rename H0 into H. rename H1 into H0.
    induction steps in tin, t_sig, Heqtin, q, H0, H |- *.
    - cbn in H. unfold haltConf in H. cbn in *.
      destruct (halt q) eqn:Eq; cbn.
      + inv H. eexists. split. { apply Nat.le_refl. }
        intros. rewrite (destruct_tape tmid) in *. 
        specialize (H _ eq_refl) as [-> _].
        lia.
      + inv H.
    - cbn in H. unfold haltConf in H. cbn in *.
      destruct (halt q) eqn:Eq; cbn.  
      + inv H. eexists. split. { apply Nat.le_refl. }
        intros. rewrite (destruct_tape tmid) in *.
        specialize (H _ eq_refl) as [-> _].
        lia.
      + subst. unfold step in H. cbn in *.
        unfold current_chars in *. cbn in *.
        destruct trans as (qnxt, A) eqn:Et. cbn in *.
        rewrite (destruct_vector_single A) in *.
        destruct (Vector.hd A) as [c' m].
        cbn in *. pose proof (Hrem := H).
        eapply IHsteps in H. { eexists. split.
        { apply Nat.le_refl. }
        intros. specialize (H1 _ eq_refl).
        rewrite Et in H1. destruct H1. subst.
        repeat eexists. { rewrite <- Hrem. repeat f_equal. now destruct t_sig, m, c'. }
        { apply Nat.le_refl. } lia. } { reflexivity. } lia.
  Qed.

End FixM.

Lemma Sim_Realise {Σ} (L : finType) (M : pTM Σ L 1) R :
  M ⊨ R ->
  Relabel (StateWhile (@Step Σ (projT1 M)) (start (projT1 M))) (projT2 M) ⊨  
    fun t '(l, t') => forall t_sig, t = [| encode_tape' t_sig |] ->
                      exists t_sig', R [| t_sig |] (l, [| t_sig' |]) /\ t' = [| encode_tape' t_sig' |].
Proof.
  intros HM.
  eapply Realise_monotone. { eapply Relabel_Realise, WhileStep_Realise. }
  intros ? ? ?. TMSimp. specialize (H0 _ eq_refl). TMSimp.
  repeat eexists. unfold Realise in HM.
  eapply TM_eval_iff in H as [k H].
  now eapply HM in H.
Qed.

Lemma Sim_Terminates {Σ} (L : finType) (M : pTM Σ L 1) T :
  projT1 M ↓ T ->
  exists C1 C2,
  projT1 (Relabel (StateWhile (@Step Σ (projT1 M)) (start (projT1 M))) (projT2 M)) ↓  
    fun t k => exists t_sig k', t = [| encode_tape' t_sig |] /\ T [| t_sig |] k' /\ k >= C1 * k' + C2.
Proof.
  intros HM.
  destruct (WhileStep_Terminates (projT1 M)) as (C1 & C2 & HC).
  exists C1, C2.
  eapply TerminatesIn_monotone. { eapply Relabel_Terminates, HC. }
  intros ? ? ?. TMSimp.
  eapply HM in H0. TMSimp. 
  destruct ymid1. rewrite (destruct_tape ctapes) in *. repeat eexists; eassumption.
Qed.

Lemma binary_simulation Σ (M : TM Σ 1) :
  {M' : TM (finType_CS bool) 1 |
        (forall q t t', eval M (start M) t q t' -> exists q, eval M' (start M') ([| encode_tape' (Vector.nth t Fin0) |] ) q ([| encode_tape' (Vector.nth t' Fin0)  |] )) /\
        (forall t, (exists q t', eval M' (start M') ([| encode_tape' (Vector.nth t Fin0) |] ) q t') -> (exists q t', eval M (start M) t q t')) }.
Proof.
  exists (projT1 (StateWhile (@Step Σ M) (start M))). split.
  - intros q' t t' [n H] % TM_eval_iff.
    edestruct @Sim_Terminates with (M := (existT _ M (fun _ : state M => tt))) (T := fun tin k => tin = t /\ k >= n).
    * intros tin k [-> Hk]. cbn. exists (mk_mconfig q' t').  eapply @loop_monotone. { exact H. }
      eapply Hk.
    * destruct H0 as [k H0]. cbn in H0. edestruct H0 as [[] H1].
      -- exists (Vector.hd t), n. split. { reflexivity. }
         split. 2: now unfold ge. split. 2:lia.
         rewrite (destruct_tape t). reflexivity.
      -- exists cstate. eapply TM_eval_iff. exists (x * n + k). unfold Relabel, initc in H1. cbn in H1.
         rewrite (destruct_tape t) in *. etransitivity. { exact H1. }
         cbn. repeat apply f_equal.
         eapply (Sim_Realise (M := (existT _ M (fun _ : state M => tt))) (R := fun tin '(_,tout) => exists q', eval M (start M) tin q' tout)) in H1.
         + specialize (H1 (Vector.hd t) eq_refl) as [t'_sig [[q'_ [n' H1] % TM_eval_iff] H2]]. 
           cbn in H2. subst. f_equal.
           eapply loop_injective in H. 2: eassumption. now inv H.
        + clear k H0 H1. intros tin k [q'_ tout] Hter. cbn in *. exists q'_. eapply TM_eval_iff. exists k. exact Hter.
  - intros t (q' & t' & [n H] % TM_eval_iff). 
    eapply (Sim_Realise (M := (existT _ M (fun _ : state M => tt))) (R := fun tin '(_,tout) => exists q', eval M (start M) tin q' tout)) in H.
    * rewrite (destruct_tape t) in *.
      specialize (H (Vector.hd t) eq_refl) as [t'_sig [[q'_ H1] H2]]. 
      cbn in H2. subst. exists q'_, [|t'_sig|]. eassumption. 
    * intros tin k [q'_ tout] Hter. cbn in *. exists q'_. eapply TM_eval_iff. exists k. exact Hter.
Qed.

Section HaltTM_Σ_to_HaltTM_bool.

Variables (Σ : finType) (M : TM Σ 1) (ts : Vector.t (tape Σ) 1).

Definition Σ' := finType_CS bool.
Definition M' : TM Σ' 1 := projT1 (StateWhile (@Step Σ M) (start M)).
Definition ts' : Vector.t (tape Σ') 1 := Vector.map (fun t => encode_tape' t) ts.

Lemma HaltTM_Σ_to_HaltTM_bool_correct : HaltsTM M ts <-> HaltsTM M' ts'.
Proof.
  unfold M', ts'. split.
  - intros (q' & t' & [n H] % TM_eval_iff).
    destruct (Sim_Terminates (M := (existT _ M (fun _ : state M => tt))) (T := fun tin k => tin = ts /\ k >= n)).
    + intros tin k [-> Hk]. cbn. exists (mk_mconfig q' t').  eapply @loop_monotone.
      { exact H. } eapply Hk.
    + destruct H0 as [k H0]. cbn in H0. edestruct H0 as [[] H1].
      -- exists (Vector.hd ts), n. split. { reflexivity. } split. 2: now unfold ge. split. 2:lia.
          apply (Vector.caseS' ts). intros ?.
          apply (Vector.case0). reflexivity.
      -- exists cstate. eexists ctapes. eapply TM_eval_iff. exists (x * n + k). unfold Relabel, initc in H1. cbn in H1.
          revert H1. apply (Vector.caseS' ts). intros ?. cbn.
          intros t0. pattern t0. apply Vector.case0.
          intros H1. exact H1.
  - intros (q' & t' & [n H] % TM_eval_iff).
    eapply (Sim_Realise (M := (existT _ M (fun _ : state M => tt))) (R := fun tin '(_,tout) => exists q', eval M (start M) tin q' tout)) in H.
    + revert H. apply (Vector.caseS' ts). intros ?. cbn.
      intros t0. pattern t0. apply Vector.case0.
      clear ts. rename h into t. intros H.
      specialize (H t eq_refl) as [t'_sig [[q'_ H1] H2]]. cbn in H1. 
      cbn in H2. subst. exists q'_, [|t'_sig|]. eassumption. 
    + intros tin k [q'_ tout] Hter. cbn in *. exists q'_. eapply TM_eval_iff. exists k. exact Hter.
Qed.

End HaltTM_Σ_to_HaltTM_bool.

Require Import Undecidability.Synthetic.Definitions.

Theorem reduction :
  HaltTM 1 ⪯ uncurry (@HaltsTM (finType_CS bool) 1).
Proof.
  unshelve eexists.
  - intros [Σ M t]. exact (M' M, ts' t).
  - intros [Σ M t]. now apply HaltTM_Σ_to_HaltTM_bool_correct.
Qed.
