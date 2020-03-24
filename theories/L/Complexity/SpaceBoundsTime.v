From Undecidability.L Require Import L Complexity.ResourceMeasures AbstractMachines.Programs.
Require Import PslBase.Lists.BaseLists.

Fixpoint L_Pro n {struct n}: list Pro :=
  match n with
    0 => []
  | S n =>
    concat (map (fun i => map (cons (varT i)) (L_Pro (n-i))) (natsLess n))
     ++ map (cons appT) (L_Pro n)
     ++ map (cons lamT) (L_Pro n)
     ++ map (cons retT) (L_Pro n)
     ++ [[]]
  end.

Hint Rewrite in_concat_iff : list.
Hint Rewrite in_app_iff : list.
Hint Rewrite in_map_iff : list.
Hint Rewrite filter_In : list.

Lemma L_Pro_in_iff n P :
  P el L_Pro n <-> sizeP P <= n.
Proof.
  revert P;induction n as [n IH] using lt_wf_ind;intros P.
  destruct n;cbn.
  all:destruct P;cbn. 
  -omega.  
  -omega.
  -transitivity True. 2: now intuition omega. split. tauto. intros [].
   autorewrite with list. intuition.
  -autorewrite with list. unfold sizeP in *.
   split.
   +intuition.
    all:now repeat match goal with
                     H : exists x, _ |- _ => destruct H
                   | H : (_ :: _ = _ :: _) |- _ => inv H
                   | H : ?P el L_Pro _ |- _ => rewrite IH in H;[ | omega]
                   | H : _ <=? _ = true |- _ => apply leb_complete in H
                   | H : _ :: _ el [[]] |- _ => now inv H
                   | _ => intuition;autorewrite with list in *;subst;cbn [sizeT];unfold sizeP in *
                   end.  
   +intros H.
    destruct t.
    1:left.
    2-4: repeat (left + right);eexists;split;[reflexivity| ].
    2-4:now cbn [sizeT] in *; apply IH;try omega.
    cbn in H.
    eexists. split. 2:autorewrite with list. 2:eexists;split;[reflexivity |].
    autorewrite with list. eexists. split. reflexivity.
    autorewrite with list.
    rewrite IH. 2:now cbn in H;omega. omega.
    apply natsLess_in_iff. omega.
Qed.

Lemma L_Pro_mono n m :
  n <= m -> L_Pro n <<= L_Pro m.
Proof.
  repeat intro. rewrite L_Pro_in_iff in *. omega.
Qed.

Lemma L_Pro_length' f :
  0 <= f 0 
  -> (forall n, 1 + 3 * f n + sumn (map f (natsLess (S n))) <= f (S n)) 
  -> forall n, length (L_Pro n) <= f n.
Proof.
  intros H0 HS.
  induction n as [n IH] using lt_wf_ind.
  destruct n.
  -cbn. omega.
  -cbn -[mult].
   autorewrite with list. 
   cbn [length].
   setoid_rewrite IH;[|omega..].
   enough ((| concat (map (fun i : nat => map (cons (varT i)) (L_Pro (n - i))) (natsLess n)) |)
           <= sumn (map f (natsLess (S n)))).
   { rewrite H. rewrite <- HS. omega. }
   rewrite length_concat. rewrite map_map. setoid_rewrite map_length.
   rewrite sumn_map_natsLess with (n:=S n).
   cbn. rewrite Nat.sub_diag,<- H0. cbn.
   induction n. reflexivity.
   rewrite natsLess_S,!map_app,!map_map,!sumn_app.
   repeat setoid_rewrite Nat.sub_succ. rewrite IHn. 2:now intuition.
   cbn -[L_Pro].  rewrite IH. 2:omega.
   reflexivity.
Qed.

Lemma L_Pro_length n :
  length (L_Pro n) <= (fun n => match n with 0 => 0 | S n => 5^n end) n.
Proof.
  apply L_Pro_length'. reflexivity.
  intros []. reflexivity.
  rewrite natsLess_S,map_app,sumn_app, map_map.
  cbn -[Nat.pow mult plus].
  enough (forall n, sumn (map (fun x : nat => 5 ^ x) (natsLess n)) + 1 <= 5^n).
  { cbn in *. rewrite <- H at 7. omega. }
  clear.
  induction n;cbn. reflexivity.
  rewrite <- IHn at 4. omega.
Qed.

Lemma L_term_card n A:
  (forall s, s el A -> size s <= n) ->
  (5^(2*n) < length A) ->
  ~ dupfree A.
Proof.
  intros HallSmall' Hlong Hdupfree'.
  pose (A':= map compile A).
  assert (HallSmall : forall P : Pro, P el A' -> sizeP P <= 2*n).
  {subst A'. intros ? (s&<-&?) % in_map_iff. etransitivity. apply sizeP_size.
   rewrite HallSmall'. all:eauto. }
  clear HallSmall'.
  erewrite <- map_length with (f:=compile) in Hlong. fold A' in Hlong.
  assert (Hdupfree : dupfree A').
  {eapply dupfree_map. intros. now eapply compile_inj. eauto. }
  clear Hdupfree'.
  clearbody A'. clear A.
  eapply dupfree_Nodup in Hdupfree.
  assert (H:A' <<= L_Pro (2*n)).
  {hnf. setoid_rewrite L_Pro_in_iff. eauto. }
  eapply NoDup_incl_length in H. 2:eassumption.
  rewrite L_Pro_length in H.
  eapply lt_not_le. 2:eassumption. rewrite <- Hlong.
  destruct n. cbn. omega.
  replace (2*S n) with (S (S (2*n))) by omega.
  eapply Nat.pow_lt_mono_r. all:omega.
Qed.

Section TraceArgument.

  Variable X : Type.
  Variable R : X -> X -> Prop.

  Inductive trace: list X -> Prop :=
  | traceUn s : trace [s]
  | traceCons s s' A : R s s' -> trace (s'::A) -> trace (s::s'::A).

  Lemma trace_app a1 a2 A1 A2 :
    trace (a1 :: A1 ++ a2 :: A2) -> pow R (S (length A1)) a1 a2.
  Proof.
    induction A1 in a1 |-*. all:cbn. all:intros H. all:inv H.
    -now eapply rcomp_1 with (R:=R).
    -eapply pow_add with (n:=1) (R:=R).
     eexists;split. now eapply rcomp_1 with (R:=R);eassumption.
     eauto.
  Qed.

End TraceArgument.

Lemma trace_not_dupfree_loop (X : eqType) (R: X -> X -> Prop) s (A:list X) :
  trace R (s::A) -> (~dupfree (s::A)) -> exists s' k, star R s s' /\ pow R (S k) s' s'.
Proof.
  intros tr (a&A1&A2&A3&eqA) % not_dupfree.
  induction A1 in tr, s, A, eqA |- *.
  -inv eqA. eapply trace_app in tr. eauto using star. 
  -inv eqA. inv tr. now exfalso;induction A1;inv H1.
   edestruct IHA1 as (s0&k&R1&R2). 1,2:eassumption.
   exists s0, k. split. 2:eassumption.
   eauto using star.
Qed.  


Lemma time_Leftmost_space_trace s t k m:
  hasTime k s -> Leftmost.spaceBS m s t ->
  exists A, trace step (s::A)
       /\ length A = k
       /\ (forall d, last (s::A) d = t)
       /\ forall s', s' el (s::A) -> size s' <= m.
Proof.
  intros (t'&Tm) (Sp&lam)%(proj1 (Leftmost.spaceBS_correct_lm _ _ _)).
  assert (m<=m) by eauto. revert Sp H. generalize m at 1 2 as m';intros m' Sp lem.
  apply timeBS_evalIn, Leftmost.timeBS_correct_lm in Tm as (Tm&lam').
  inv lam. inv lam'.
  induction k in m',lem,s, Sp,Tm |-*.
  -cbv in Tm. subst s. inv Sp. 2:easy.
   exists []. cbn. repeat split. eauto using trace. intuition subst;cbn in *. omega.
  -eapply pow_add with (n:=1) in Tm as (s'&R&Tm).
   eapply rcomp_1 with (R:=Leftmost.step_lm) in R.
   inv Sp. easy.
   eapply (Leftmost.step_lm_functional R) in H as <-.
   eapply Leftmost.step_lm_step in R.
   apply Nat.max_lub_iff in lem as [].
   edestruct IHk as (A&?&?&?&?). 1-3:eassumption.
   exists (s'::A);repeat split.
   +eauto using trace.
   +cbn;omega.
   +cbn;intuition.
   +cbn;intuition. all:subst. all:eauto.
Qed.

Lemma Leftmost_space_bounds_time k s t m:
  hasTime k s -> Leftmost.spaceBS m s t -> k <= 25^m.
Proof.
  intros Tm Sp.
  edestruct Nat.le_gt_cases. eassumption. exfalso.
  edestruct time_Leftmost_space_trace as (A&tr&leq&_&allSmall). 1,2:eassumption.
  edestruct trace_not_dupfree_loop with (s:=s)(A:=A) as (s'&?).
  now eauto.
  -eapply L_term_card. eassumption. rewrite Nat.pow_mul_r. change (5^2) with 25. rewrite H. cbn. omega.
  -destruct Tm as (?&?&lam).
    eapply uniform_confluent_noloop.
    1,2,4:now eauto using uniform_confluence,pow_star.
    intros ? R. inv lam. inv R.
Qed.

Lemma time_space_trace s k m:
  hasTime k s -> (forall s', s >* s' -> size s' <= m) ->
  exists A, trace step (s::A)
       /\ length A = k
       /\ forall s', s' el (s::A) -> size s' <= m.
Proof.
  intros (t'&Tm&lam) Sp.
  assert (m<=m) by eauto. revert Sp H. generalize m at 1 2 as m';intros m' Sp lem.
  inv lam.
  induction k in m',lem,s, Sp,Tm |-*.
  -exists []. cbn. repeat split. eauto using trace. intuition subst;cbn in *. rewrite <- lem. eauto using starR.
  -eapply pow_add with (n:=1) in Tm as (s'&R&Tm).
   eapply rcomp_1 with (R:=step) in R.
   edestruct IHk as (A&?&?&?). 1-3:now eauto using star.
   exists (s'::A);repeat split.
   +eauto using trace.
   +cbn;omega.
   +cbn;intuition. all:subst. all:eauto using star,le_trans.
Qed.

Lemma maxSize_bounds_time k s m:
  hasTime k s -> (forall s', s >* s' -> size s' <= m) -> k <= 25^m.
Proof.
  intros Tm Sp.
  edestruct Nat.le_gt_cases. eassumption. exfalso.
  edestruct time_space_trace as (A&tr&leq&?). 1,2:eassumption.
  edestruct trace_not_dupfree_loop with (s:=s)(A:=A) as (s'&?).
  now eauto.
  -eapply L_term_card. eassumption. rewrite Nat.pow_mul_r. change (5^2) with 25. rewrite H. cbn. omega.
  -destruct Tm as (?&?&lam).
    eapply uniform_confluent_noloop.
    1,2,4:now eauto using uniform_confluence,pow_star.
    intros ? R. inv lam. inv R.
Qed.

Corollary space_bounds_time k s m:
  hasTime k s -> hasSpace m s -> k <= 25^m.
Proof.
  rewrite hasSpace_iff. intuition. eauto using maxSize_bounds_time.
Qed.
