Require Import Undecidability.FOLC.GenCompleteness Lia Nat.

Definition max_list_with {A} (f : A -> nat) : list A -> nat :=
  fix go l :=
  match l with
  | [] => 0
  | x :: l => Nat.max (f x) (go l)
  end.
Notation max_list := (max_list_with (fun x => x)).

Lemma max_list_spec l :
  l <> nil -> In (max_list l) l. 
Proof.
  destruct l as [ | x l] using rev_ind; try congruence.
  clear IHl. intros _. induction l; cbn in *.
  - left. lia.
  - destruct (Nat.max_dec a (max_list (l ++ [x]))) as [H1 | H1].
    + now left.
    + right. rewrite H1 in *. eauto.
Qed.

Lemma max_list_spec' x l :
  In x l -> x <= max_list l.
Proof.
  intros H.
  induction l in x, H |- *.
  - inv H.
  - inv H; cbn.
    + lia. 
    + eapply IHl in H0. lia.
Qed.

(** ** WKL  *)

(** The predicate [suffix] holds if the first list is a suffix of the second.
The predicate [prefix] holds if the first list is a prefix of the second. *)
Definition prefix {A} : list A -> list A -> Prop := fun l1 l2 => exists k, l2 = l1 ++ k.
Infix "`prefix_of`" := prefix (at level 70) : stdpp_scope.

Definition decidable {X} (p : X -> Prop) := exists f, forall x, p x <-> f x = true.

Record is_tree (tree_T : list bool -> Prop) :=
  {
    tree_inhab : exists l : list bool, tree_T l ;
    tree_p : forall l1 l2, prefix l1 l2 -> tree_T l2 -> tree_T l1 ;
    tree_dec :       decidable tree_T ;
  }.

Record tree :=
  {
  tree_T :> list bool -> Prop ;
  tree_is_tree :> is_tree tree_T
  }.

Definition bounded_tree (T : list bool -> Prop) := 
  exists k, forall a, length a >= k -> ~ T a.

Definition infinite_tree (T : list bool -> Prop) := 
  forall k, exists a, T a /\ (length a >= k ).

Definition infinite_path (T : list bool -> Prop) :=
  exists f : nat -> bool, forall n, T (map f (seq 0 n)).

Definition wellfounded_tree (T : list bool -> Prop) :=
  forall f : nat -> bool, exists n, ~ T (map f (seq 0 n)).

Lemma bounded_infinite_contra T :
  bounded_tree T -> infinite_tree T -> False.
Proof.
  firstorder.
Qed. 

Lemma path_wellfounded_contra T :
  infinite_path T -> wellfounded_tree T -> False.
Proof.
  intros [f H] H2.
  specialize (H2 f) as [n].
  eauto.
Qed.

Definition WKL :=
  forall T : tree, infinite_tree T -> infinite_path T.

(** ** Model existence  *)

Definition model_existence (Cond : forall Sigma D, @interp Sigma D -> Prop) :=
  forall {Sigma : Signature},
  forall {HdF : eq_dec Funcs} {HdP : eq_dec Preds},
  forall {HeF : enumT Funcs} {HeP : enumT Preds},
  forall T (T_closed : closed_T T), consistent T ->
                               has_model (Cond Sigma) T.

Definition countable (X : Type) := inhabited (eq_dec X) /\ inhabited (enumT X).

Definition compactness (C : forall Sigma D, @interp Sigma D -> Prop) :=
  forall {Sigma : Signature},
  forall {HdF : eq_dec Funcs} {HdP : eq_dec Preds},
  forall {HeF : enumT Funcs} {HeP : enumT Preds},
  forall T (T_closed : closed_T T),
  (forall Gamma, Gamma ⊏ T -> has_model SM (fun x => In x Gamma))
  -> has_model (C Sigma) T.

Lemma modex_standard :
  model_existence (fun Sigma D I => @SM Sigma D I /\ countable D).
Proof.
  intros Sigma HdF HdP HeF HeP T T_closed T_cons.
  pose proof (@model_bot_correct Sigma HdF HdP HeF HeP T T_closed).
  exists (@term Sigma). eexists. exists ids.
  setoid_rewrite <- H.
  repeat split; try exact _.
  - intros. eapply Out_T_sub. cbn. asimpl. assumption.
  - eapply model_bot_classical.
  - now eapply model_bot_standard.
Qed.

Lemma modex_compact (C : forall Sigma D, @interp Sigma D -> Prop) :
  model_existence C -> compactness C.
Proof.
  intros HM Sigma HdF HdP HeF HeP T T_closed H.
  apply HM in T_closed as (D & I & rho & HI); trivial.
  + intros [Gamma [H1 H2]]. apply H in H1 as (D & I & rho & H3 & H4).
    apply Soundness' in H2. apply H4. now apply (H2 D I H4 rho).
  + now exists D, I, rho.
Qed.

Lemma compact_standard :
  compactness (fun Sigma D I => @SM Sigma D I /\ countable D).
Proof.
  apply modex_compact. apply modex_standard.
Qed.

Definition decidable_model := 
fun (Sigma : Signature) (D : Type) (I : interp D) => exists f : forall P, vector D (pred_ar P) -> bool, forall P, forall v : vector D (pred_ar P), f P v = true <-> i_P v.

Definition DM `{Signature} D (I : interp D) := SM I /\ countable D /\ decidable_model I.

Definition count_sig := @B_S False ltac:(tauto) nat (fun n => 0).

Definition Neg `{Signature} phi := Impl phi Fal.

Definition Or `{Signature} phi psi := Impl (Neg phi) psi.

Definition And `{Signature} phi psi := Neg (Or (Neg phi) (Neg psi)).

Lemma Neg_sat `{Signature} D (I : interp D) rho phi :
  standard_bot I ->
  rho ⊨ Neg phi <-> ~ rho ⊨ phi.
Proof.
  firstorder.
Qed.

Notation omniscient_on I phi := (forall (rho : env _), dec (rho ⊨ phi)).
Definition omniscient := fun (Sigma : Signature) (D : Type) (I : interp D) => inhabited (forall phi, omniscient_on I phi).

Lemma omniscient_on_Neg `{Signature} D (I : interp D) phi :
  standard_bot I ->
  omniscient_on I phi -> omniscient_on I (Neg phi).
Proof.
  intros ? ? ?. destruct (X rho); cbn; firstorder.
Qed.
Hint Resolve omniscient_on_Neg : core.

Lemma Or_sat `{Signature} D (I : interp D) rho phi psi :
  standard_bot I -> inhabited (omniscient_on I phi) -> inhabited (omniscient_on I psi) ->
  rho ⊨ Or phi psi <-> rho ⊨ phi \/ rho ⊨ psi.
Proof.
  firstorder.
Qed.

Lemma omniscient_on_Or `{Signature} D (I : interp D) phi psi :
  standard_bot I ->
  omniscient_on I phi ->
  omniscient_on I psi ->
  omniscient_on I (Or phi psi).
Proof.
  firstorder.
Qed.
Hint Resolve omniscient_on_Or : core.

Lemma And_sat `{Signature} D (I : interp D) rho phi psi :
  standard_bot I -> inhabited (omniscient_on I phi) -> inhabited (omniscient_on I psi) ->
  rho ⊨ And phi psi <-> rho ⊨ phi /\ rho ⊨ psi.
Proof.
  intros ? [] [].
  split; unfold And; rewrite Neg_sat, Or_sat; eauto; firstorder.
Qed.

Lemma omniscient_on_And `{Signature} D (I : interp D) phi psi :
  standard_bot I ->
  omniscient_on I phi ->
  omniscient_on I psi ->
  omniscient_on I (And phi psi).
Proof.
  intros. destruct (X rho), (X0 rho); cbn; firstorder.
Qed.
Hint Resolve omniscient_on_And : core.

Fixpoint fExists `{Signature} (l : list form) :=
  match l with
  | [] => Fal
  | phi :: l => Or phi (fExists l)
  end.

Lemma to_False_iff {P : Prop} :
  (P -> False) -> (P <-> False).
Proof.
  tauto.
Qed.

Lemma omniscient_on_fExists_sat `{Signature} D (I : interp D) l :
  standard_bot I -> (forall phi, In phi l -> omniscient_on I phi) ->
  omniscient_on I (fExists l).
Proof.
  intros SB omn rho.
  induction l  as [ | phi] in SB, omn, rho |- *.
  - firstorder.
  - cbn - [Or].
    edestruct (omn phi); eauto.
    + left. rewrite Or_sat; eauto. 
    + edestruct IHl; eauto.
      * left. rewrite Or_sat; eauto.
      * right. rewrite Or_sat; eauto. firstorder.
Qed.

Lemma fExists_sat' `{Signature} D (I : interp D) rho l :
  standard_bot I -> (forall phi, In phi l -> omniscient_on I phi) ->
  rho ⊨ fExists l <-> exists phi, In phi l /\ rho ⊨ phi.
Proof.
  intros SB omn.
  induction l.
  - firstorder.
  - cbn - [Or].
    rewrite Or_sat, IHl; eauto.
    split.
    + intros [ | [? []]]; eauto.
    + intros [? [[-> | ]]]; eauto.
    + econstructor. eapply omniscient_on_fExists_sat; eauto.
Qed.

Lemma fExists_sat `{Signature} D (I : interp D) rho l :
  standard_bot I -> omniscient I ->
  rho ⊨ fExists l <-> exists phi, In phi l /\ rho ⊨ phi.
Proof.
  intros ? []. eapply fExists_sat'; eauto.
Qed.

Fixpoint fAll `{Signature} (l : list form) :=
  match l with
  | [] => Impl Fal Fal
  | phi :: l => And phi (fAll l)
  end.

Lemma omniscient_on_fAll_sat `{Signature} D (I : interp D) l :
  standard_bot I -> (forall phi, In phi l -> omniscient_on I phi) ->
  omniscient_on I (fAll l).
Proof.
  intros SB omn rho.
  induction l  as [ | phi] in SB, omn, rho |- *.
  - firstorder.
  - cbn - [And].
    edestruct (omn phi); eauto.
    + edestruct IHl; eauto.
      * left. rewrite And_sat; eauto.
      * right. rewrite And_sat; eauto. firstorder.
    + right. rewrite And_sat; eauto. firstorder.
Qed.

Lemma fAll_sat' `{Signature} D (I : interp D) rho l :
  standard_bot I -> (forall phi, In phi l -> (omniscient_on I phi)) ->
  rho ⊨ fAll l <-> forall phi, In phi l -> rho ⊨ phi.
Proof.
  intros SB omn.
  induction l.
  - firstorder.
  - cbn - [And].
    rewrite And_sat, IHl; eauto.
    split.
    + intros [] ? [-> | ]; eauto.
    + eauto 9.
    + econstructor. eapply omniscient_on_fAll_sat; eauto.
Qed.

Lemma fAll_sat `{Signature} D (I : interp D) rho l :
  standard_bot I -> omniscient I ->
  rho ⊨ fAll l <-> forall phi, In phi l -> rho ⊨ phi.
Proof.
  intros ? []. eapply fAll_sat'; eauto.
Qed.

Definition listable {X} (p : X -> Prop) := { L : list X | forall x, p x <-> In x L}.

Lemma listable_list_length :
  forall k : nat, listable (fun x : list bool => length x = k).
Proof.
  induction k as [ | k [L IH] ].
  - exists [ [] ]. intros [] ; cbv ; firstorder. inv H.
  - exists (map (cons true) L ++ map (cons false) L).
    intros l.
    rewrite in_app_iff, !in_map_iff.
    repeat setoid_rewrite <- IH.
    destruct l as [ | [] ].
    + cbn. split. inversion 1. firstorder congruence.
    + cbn. split. 
      * inversion 1. eauto.
      * firstorder; now inv H.
    + cbn. split. 
      * inversion 1. eauto.
      * firstorder; now inv H.
Qed.

Notation nat := (nat).

Fixpoint mapi {X Y} (f : nat -> X -> Y) (l : list X) i :=
  match l with
  | [] => []
  | x :: l => f i x :: mapi f l (S i)
  end.

Lemma in_mapi_iff {X Y} (f : nat -> X -> Y) l y i :
  In y (mapi f l i) <-> exists x j, f (j + i) x = y /\ nth_error l j = Some x.
Proof.
  induction l as [ | x l] in i |- *; cbn.
  - firstorder. destruct x0; inv H0.
  - rewrite IHl. intuition subst.
    + now exists x, 0. 
    + destruct H0 as (x' & j & H1 & H2).
      exists x', (S j). split. rewrite <- H1; f_equal. lia. now cbn.
    + destruct H as (x' & [ | j] & H1 & H2); cbn in *.
      * inv H2. eauto.
      * right. exists x', j. split. rewrite <- H1; f_equal. lia. now cbn.
Qed.

Lemma mapi_app {X Y} (f : nat -> X -> Y) (l1 l2 : list X) i :
  mapi f (l1 ++ l2) i = mapi f l1 i ++ mapi f l2 (length l1 + i).
Proof.
  induction l1 in l2, i |- *; cbn.
  - reflexivity.
  - rewrite IHl1. repeat f_equal. lia.
Qed.

Lemma infinite_iff (T : tree) :
  infinite_tree T <-> forall k : nat, exists a : list bool, T a /\ | a | = k.
Proof.
  split.
  - intros H k. destruct (H k) as (? & ? & ?).
    exists (firstn k x). split. eapply tree_p. eapply T. 2:eauto.
    rewrite <- (firstn_skipn k x) at 2. eexists; eauto.
    rewrite firstn_length. lia.
  - intros H k. destruct (H k) as (? & ? & ?). exists x. split. eauto. lia.
Qed.

Section WKL.

  Variable T : tree.
  Variable T_D : list bool -> bool.
  Variable HD : forall x, T_D x = true <-> T x.

  Definition phi n := fExists (map (fun l => fAll (mapi (fun i (b : bool) => if b then @Pred count_sig i Vector.nil else Neg (@Pred count_sig i Vector.nil)) l 0)) (filter T_D (proj1_sig (listable_list_length n)))).

  Definition Th psi := exists n, psi = phi n.

  Lemma phi_down_S D (I : interp D) rho n :
    @standard_bot count_sig D I -> omniscient I ->
      rho ⊨ phi (S n) -> rho ⊨ phi n.
  Proof.
    intros SB omn H.
    eapply fExists_sat in H as (phi' & H1 & H); eauto.
    eapply in_map_iff in H1 as (l & <- & [H3 H4] % in_filter_iff); eauto.
    rewrite fAll_sat in H; eauto.
    destruct (listable_list_length (S n)) as [L HL].
    cbn in *. eapply HL in H3.
    destruct l as [ | b l _] using rev_ind; try now inv H3.
    rewrite app_length in H3. cbn in H3. rewrite plus_comm in H3. inv H3.
    eapply fExists_sat; eauto.
    eexists. split.
    - eapply in_map_iff. exists l. split. reflexivity.
      eapply in_filter_iff. split.
      destruct listable_list_length as [L' HL'].
      + cbn. eapply HL'. reflexivity.
      + eapply HD in H4. eapply HD.
        eapply tree_p. eapply T. 2:exact H4. exists [b]; eauto.
    - eapply fAll_sat; eauto. intros. eapply H. rewrite mapi_app. eapply in_app_iff. eauto.
  Qed.

  Lemma phi_down D (I : interp D) rho n m :
    @standard_bot count_sig D I -> omniscient I ->
    rho ⊨ phi n -> n >= m -> rho ⊨ phi m.
  Proof.
    intros SB omn H1 H2. induction H2.
    - eauto.
    - eapply IHle, phi_down_S, H1; eauto.
  Qed.

  (* Induktionsbeispiele von Kathrin *)

  Lemma decidable_to_omniscient {Σ : Signature} (I : interp unit) :
    decidable_model I -> standard_bot I -> omniscient I.
  Proof.
    intros [d Hd] SB. econstructor. intros phi rho.
    induction phi in rho |- *; cbn.
    - firstorder.
    - destruct (d P (Vector.map (eval rho) t)) eqn:E.
      + left. now eapply Hd.
      + right. intros ? % Hd. congruence.
    - destruct (IHphi1 rho), (IHphi2 rho); firstorder.
    - destruct (IHphi (tt .: rho)). left; now intros [].
      right. firstorder.
  Qed.

  Lemma omniscient_to_classical {Σ : Signature} D (I : interp D) :
    omniscient I -> classical I.
  Proof.
    intros [d] rho phi psi. cbn.
    destruct (d phi rho), (d psi rho); tauto.
  Qed.

  Lemma compact_DM_WKL :
    compactness (@DM) -> infinite_tree T -> infinite_path T.
  Proof.
    intros compact infT.
    destruct (compact count_sig _ _ _ _ Th) as (D & I & rho & H & (classI & standI) & (eq_dec_D & enum_D) & (f & decI)).
    - intros psi n [m ->]. unfold phi.
      induction proj1_sig; cbn.
      + econstructor.
      + destruct (T_D a); repeat econstructor; eauto.
        generalize 0 as k.
        induction a; intros; cbn; try destruct a; repeat econstructor.
        * intros. inv X.
        * eauto.
        * intros. inv X.
        * eauto.
    - intros Γ HΓ.
      assert (exists L, Γ = map phi L) as [L ->]. {
        induction Γ as [ | psi Γ].
        - now exists [].
        - destruct IHΓ as [L]. firstorder.
          subst. specialize (HΓ psi (or_introl eq_refl)) as [n Hn].
          exists (n :: L). subst. reflexivity.
      }
      pose (m := max_list L).
      rewrite infinite_iff in infT.
      destruct (infT m) as (l & Hl & Hs).
      exists unit.
      unshelve epose (I := _ : @interp count_sig unit).
      + econstructor.
        * intros [].
        * cbn. intros n _.
          exact (nth n l false = true).
        * exact False.
      + exists I.
        assert (omn : omniscient I).
        { eapply decidable_to_omniscient.
          unshelve eexists.
          -- cbn. intros n _.
             exact (nth n l false).
          -- cbn. reflexivity.
          -- now cbv.
        }
        assert (SB : standard_bot I).
        { now cbv. }
        exists (fun _ => tt). repeat split; eauto.
        * intros phi (n & <- & H) % in_map_iff.
          assert (Hn : n <= m) by now eapply max_list_spec'.
          eapply phi_down; eauto.  
          eapply fExists_sat; eauto. eexists. split.
          -- eapply in_map_iff. exists l. split. reflexivity.
             eapply in_filter_iff. split.
             destruct listable_list_length. cbn. now eapply i.
             now eapply HD.
          -- eapply fAll_sat; eauto. intros phi (b & j & <- & HH) % in_mapi_iff.
             rewrite <- plus_n_O. destruct b; cbn.
             rewrite <- nth_default_eq. unfold nth_default. now rewrite HH.
             rewrite <- nth_default_eq. unfold nth_default. destruct (nthe j l); congruence.
        * now eapply omniscient_to_classical.
    - pose (g := fun n : nat => f n Vector.nil).
      exists g. intros n. unfold Th in H.
      specialize (H (phi n) ltac:(unfold contains; eauto)).
      assert ( forall l, forall phi0 : form, phi0 el mapi (fun (i : nat) (b : bool) => if b then @Pred count_sig i Vector.nil else Neg (@Pred count_sig i Vector.nil)) l 0 -> forall rho0 : env D, dec (rho0 ⊨ phi0)) as HHH by shelve.
      eapply fExists_sat' in H as (phi' & H1 & H); eauto.
      eapply in_map_iff in H1 as (l & <- & [H3 H4] % in_filter_iff).
      rewrite fAll_sat' in H.
      destruct (listable_list_length n) as [L HL].
      cbn in *. eapply HL in H3.
      enough (l = [g p | p ∈ seq 0 n]) as -> by now eapply HD.
      subst. clear - H decI standI.
      revert H. generalize 0 as n.
      induction l; cbn; intros.
      + reflexivity.
      + f_equal. destruct a.
        * pose proof (H (@Pred count_sig n Vector.nil) (or_introl eq_refl)) as H0.
          eapply decI in H0. unfold g. cbn in H0. now rewrite H0.
        * pose proof (H (Neg (@Pred count_sig n Vector.nil)) (or_introl eq_refl)) as H0.
          cbn in H0. unfold g. rewrite <- decI in H0.
          symmetry. eapply not_true_is_false.
          intros [] % H0 % standI.
        * eapply IHl. intros. eapply H. eauto.
      + eauto.
      + eauto. 
      + intros phi0 ? % in_map_iff. clear - H2 standI decI HHH.
        induction filter.
        * exfalso. destruct H2 as (? & ? & ?); cbn in *; congruence.
        * decide (phi0 = fAll (mapi (fun (i : nat) (b : bool) => if b then @Pred count_sig i Vector.nil else Neg (@Pred count_sig i Vector.nil)) a 0)).
          -- subst. intros.
             eapply omniscient_on_fAll_sat. eauto. eapply HHH. 
          -- eapply IHl. destruct H2 as (? & ? & ?). destruct H0.
             ++ subst. congruence.
             ++ eauto.
                Unshelve. {
                  intros ? ? ? % in_mapi_iff. clear - H1 standI decI.
                  revert H1.
                  generalize 0 as k.
                  induction l; intros k H1.
                  * exfalso. destruct H1 as (? & [] & ? & ?); cbn in *; congruence.
                  * decide (phi0 = @Pred count_sig k Vector.nil).
                    -- subst. intros. destruct (f k Vector.nil) eqn:E.
                       left. eapply decI. eauto. right. intros ? % decI. cbn in *. congruence.
                    -- decide (phi0 = Neg (@Pred count_sig k Vector.nil)).
                       ++ subst. intros. destruct (f k Vector.nil) eqn:E.
                          right. eapply decI in E. cbn. firstorder. left.
                          intros ? % decI. cbn in *. congruence.
                       ++ eapply (IHl (S k)).
                          destruct H1 as (x & j & ? & ?).
                          destruct j.
                          ** cbn in H0. destruct x.
                             --- inv H0. cbn in n. congruence.
                             --- inv H0. cbn in n0. congruence.
                          ** cbn in *. exists x, j; destruct x; subst; split; eauto; repeat f_equal; lia.
                }
  Qed.

End WKL.

Theorem compact_implies_WKL :
  compactness (@DM) -> forall T : tree, infinite_tree T -> infinite_path T.
Proof.
  intros.
  pose proof (tree_dec T) as [f Hf].
  eapply compact_DM_WKL with (T_D := f); eauto. 
  firstorder.
Qed.
Print Assumptions compact_implies_WKL.
