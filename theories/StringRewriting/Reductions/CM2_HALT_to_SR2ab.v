Require Import List Relation_Operators Lia.
Import ListNotations.

Require Import Undecidability.StringRewriting.SR01.
Require Import Undecidability.CounterMachines.CM2.

Require Import ssreflect ssrbool ssrfun.

Arguments rt_trans {A R x y z}.

Module Facts.
(* induction principle wrt. a decreasing measure f *)
(* example: elim /(measure_ind length) : l. *)
Lemma measure_ind {X : Type} (f : X -> nat) (P : X -> Prop) : 
  (forall x, (forall y, f y < f x -> P y) -> P x) -> forall (x : X), P x.
Proof.
  apply : well_founded_ind.
  apply : Wf_nat.well_founded_lt_compat. move => *. by eassumption.
Qed.
Arguments measure_ind {X}.

(* duplicates argument *)
Lemma copy {A : Prop} : A -> A * A.
Proof. done. Qed.

Lemma iter_plus {X: Type} {f: X -> X} {x: X} {n m: nat} : 
  Nat.iter (n + m) f x = Nat.iter n f (Nat.iter m f x).
Proof. by rewrite /Nat.iter nat_rect_plus. Qed.

Section ForallNorm.
Context {X : Type} {P : X -> Prop}.

Lemma ForallE {l} : Forall P l -> if l is x :: l then P x /\ Forall P l else True.
Proof. by case. Qed.

Lemma Forall_nilI : Forall P [].
Proof. by constructor. Qed.

Lemma Forall_consI {x l} : P x -> Forall P l -> Forall P (x :: l).
Proof. by constructor. Qed.

Lemma Forall_nilP : Forall P [] <-> True.
Proof. by constructor. Qed.

Lemma Forall_consP {x l} : Forall P (x :: l) <-> P x /\ Forall P l.
Proof. by constructor=> [/ForallE | [/Forall_consI H] /H]. Qed.

Lemma Forall_singletonP {x} : Forall P [x] <-> P x.
Proof. rewrite Forall_consP Forall_nilP. by constructor=> [[? ?] | ?]. Qed.

Lemma Forall_appP {l1 l2}: Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
Proof.
  elim: l1; first by (constructor; by [|case]).
  move=> ? ? IH /=. by rewrite ?Forall_consP IH and_assoc.
Qed.

Lemma Forall_repeatP {x n} : Forall P (repeat x n) <-> (n = 0 \/ P x).
Proof.
  elim: n; first by (constructor => *; [by left | by constructor]).
  move=> n IH /=. rewrite Forall_consP IH.
  constructor; first by (move=> [? _]; right).
  case; [done | constructor; [done | by right]].
Qed. 

Definition Forall_norm := (@Forall_appP, @Forall_singletonP, @Forall_consP, @Forall_nilP).
End ForallNorm.

Lemma repeat_appP {X: Type} {x: X} {n m: nat} : 
  repeat x n ++ repeat x m = repeat x (n+m).
Proof. by elim: n; [| move=> ? /= ->]. Qed.

Lemma In_appl {X : Type} {x: X} {l1 l2: list X} : In x l1 -> In x (l1 ++ l2).
Proof. move=> ?. apply: in_or_app. by left. Qed.

Lemma In_appr {X : Type} {x: X} {l1 l2: list X} : In x l2 -> In x (l1 ++ l2).
Proof. move=> ?. apply: in_or_app. by right. Qed.

Arguments nth_error_In {A l n x}.

Lemma nth_error_Some_in_combine {X: Type} {l: list X} {i x}:
  nth_error l i = Some x -> 
  In (i, x) (combine (seq 0 (length l)) l).
Proof.
  move Hk: (0) => k Hi. have ->: (i = i + k) by lia.
  elim: l i k {Hk} Hi; first by case.
  move=> y l IH [|i] k.
  - move=> /= [<-]. by left.
  - move=> /IH {}IH /=. right. by have ->: (S (i + k) = i + S k) by lia.
Qed.
End Facts.

Import Facts.

Module SR_facts.
Import StringRewriting.SR01.
Lemma stepI {srs u v a b c d s t} : 
  s = (u ++ a :: b :: v) -> t = (u ++ c :: d :: v) -> In ((a, b), (c, d)) srs ->
  step srs s t.
Proof. move=> -> ->. by constructor. Qed.

Lemma reachable_appI {srs u v s t} : reachable srs s t -> reachable srs (u ++ s ++ v) (u ++ t ++ v).
Proof.
  elim; [| move=> *; by apply: rt_refl | move=> *; apply: rt_trans; by eassumption ].
  move=> {}s {}t [] u' v' > ?. 
  apply /rt_step /(stepI (u := u ++ u') (v := v' ++ v)); last by eassumption.
  all: by rewrite -?app_assoc.
Qed.

Lemma reachable_applI {srs u s t} : reachable srs s t -> reachable srs (u ++ s) (u ++ t).
Proof. move=> /reachable_appI => /(_ u []). by rewrite ?app_nil_r. Qed.

Lemma reachable_apprI {srs v s t} : reachable srs s t -> reachable srs (s ++ v) (t ++ v).
Proof. by move=> /reachable_appI => /(_ [] v). Qed.
End SR_facts.

Module CM_facts.
Lemma haltingP {cm c} : halting cm c <-> length cm <= state c.
Proof.
  move:c => [p a b]. rewrite /halting /=.
  move Hoi: (nth_error cm p) => oi.
  case: oi Hoi; last by move=> /nth_error_None.
  move=> [] x => [|?] Hp /=.
  - constructor; [by case; lia | by rewrite -nth_error_None Hp].
  - move: x a b Hp => [] [|?] [|?]; 
      (constructor; [by case; lia | by rewrite -nth_error_None Hp]).
Qed.

Lemma halting_eq {cm c n} : halting cm c -> Nat.iter n (step cm) c = c.
Proof.
  move=> Hc. elim: n; first done.
  move=> ? /= ->. by rewrite Hc.
Qed. 

Lemma values_ub cm c n : 
  value1 (Nat.iter n (CM2.step cm) c) + value2 (Nat.iter n (CM2.step cm) c) <= n + value1 c + value2 c.
Proof.
  move Hk : (n + value1 c + value2 c) => k.
  have : n + value1 c + value2 c <= k by lia.
  elim: n k c {Hk}; first done.
  move=> n IH k [p a b]. have ->: S n = n + 1 by lia.
  rewrite iter_plus /=. 
  case: (nth_error cm p).
  - move=> [] [] => [||?|?]; move: a b => [|?] [|?] /= ?; apply: IH => /=; by lia.
  - move=> ?. apply: IH => /=. by lia.
Qed.

End CM_facts.

Module Argument.
Import Facts SR_facts CM_facts.
Section Reduction.
(* given two-counter machine *)
Context (cm : Cm2).

Local Notation sb := ((0, @None nat)). (* blank *)
Local Notation sl := ((1, @None nat)). (* left marker *)
Local Notation sr := ((2, @None nat)). (* right marker *)
Local Notation sm := ((3, @None nat)). (* middle marker *)

Local Notation sz := ((4, @None nat)). (* 0 *)
Local Notation so := ((5, @None nat)). (* 1 *)
Local Notation st := ((6, @None nat)). (* temporary marker *)

Local Notation sb' p := ((0, @Some nat p)). (* blank *)
Local Notation sl' p := ((1, @Some nat p)). (* left marker *)
Local Notation sr' p := ((2, @Some nat p)). (* right marker *)
Local Notation sm' p := ((3, @Some nat p)). (* middle marker *)

Definition states := map (fun i => if i is dec _ q then q else 0) cm.
Definition sum : list nat -> nat := fold_right Nat.add 0. 

Definition state_bound := 1 + length cm + sum states.

Lemma state_boundP {p i} : nth_error cm p = Some i -> 
  (if i is dec _ q then q else 0) + 1 + p < state_bound.
Proof.
  rewrite /state_bound /states.
  elim: (cm) p; first by case.
  move=> ? l IH [|p] /= => [[->] | /IH]; last by lia.
  by case: (i); lia.
Qed.

(* encode instruction i at position n *)
Definition enc_Instruction (ni: (nat * Instruction)) : Srs :=
  match ni with
  | (p, inc b) => if b then [((sr' p, sz), (sb, sr' (S p)))] else [((sz, sl' p), (sl' (S p), sb))]
  | (p, dec b q) => 
      if b then [((sm, sr' p), (sm, sr' (S p))); ((sb, sr' p), (sr' q, sz))] 
      else [((sl' p, sm), (sl' (S p), sm)); ((sl' p, sb), (sz, sl' q))]
  end.

(* constructed string rewriting system *)
Definition srs : Srs := 
  (* initialization *)
  [ ((sz, sz), (st, sr)); (* 00 -> tr *)
    ((sz, st), (sl' 0, sm)) (* 0t -> l_0 m *) ] ++
  (* simulation *)
  flat_map enc_Instruction (combine (seq 0 (length cm)) cm) ++
  (* state movement to the right *)
  flat_map (fun p => [
    ((sl' p, sb), (sl, sb' p)); ((sl' p, sm), (sl, sm' p)); 
    ((sb' p, sb), (sb, sb' p)); ((sb' p, sm), (sb, sm' p)); ((sb' p, sr), (sb, sr' p));
    ((sm' p, sb), (sm, sb' p)); ((sm' p, sr), (sm, sr' p))]) (seq 0 state_bound) ++
  (* state movement to the left *)
  flat_map (fun p => [
    ((sb, sr' p), (sb' p, sr)); ((sm, sr' p), (sm' p, sr)); 
    ((sb, sb' p), (sb' p, sb)); ((sm, sb' p), (sm' p, sb));
    ((sb, sm' p), (sb' p, sm)); ((sl, sm' p), (sl' p, sm))]) (seq 0 state_bound) ++
  (* finalization *)
  map (fun p => ((sz, sl' p), (so, so))) (seq (length cm) (state_bound - length cm)) ++
  flat_map (fun n => [(((n, None), so), (so, so)); ((so, (n, None)), (so, so))]) (seq 0 6)
  .

Lemma move_sb_right {p n} : p < state_bound -> reachable srs ((sb' p) :: repeat sb n) ((repeat sb n) ++ [sb' p]).
Proof.
  move=> Hp. elim: n; first by apply: rt_refl.
  move=> n IH /=. apply: rt_trans; 
    [apply: rt_step | apply: (reachable_applI (u := [sb])); exact: IH].
  apply: (stepI (u := []) (v := repeat sb n)); [by reflexivity | by reflexivity |].
  rewrite /srs. apply /In_appr /In_appr /In_appl /in_flat_map.
  exists p. constructor; [apply /in_seq; by lia | move=> /=; by tauto].
Qed.

Lemma move_sb_left {p n} : p < state_bound -> reachable srs ((repeat sb n) ++ [sb' p]) ((sb' p) :: repeat sb n).
Proof.
  move=> Hp. elim: n; first by apply: rt_refl.
  move=> n IH /=. apply: rt_trans; 
    [apply: (reachable_applI (u := [sb])); exact: IH | apply: rt_step].
  apply: (stepI (u := []) (v := repeat sb n)); [by reflexivity | by reflexivity |].
  rewrite /srs. apply /In_appr /In_appr /In_appr /In_appl /in_flat_map.
  exists p. constructor; [apply /in_seq; by lia | move=> /=; by tauto].
Qed.


Lemma reachable_repeat_soI {u v: list Symbol} : v = repeat so (length u) -> In so u -> 
  Forall (fun '(n, op) => n <= 5 /\ op = None) u -> 
  reachable srs u v.
Proof.
  move=> -> {v}. elim /(measure_ind (@length Symbol)) : u.
  move=> []; first done.
  move=> x u /= IH [->|].
  - move: u IH => [* | y u]; first by apply: rt_refl.
    move=> /= IH /ForallE [_ Hyl]. apply: (rt_trans (y := so :: so :: u)).
    + apply: rt_step. apply: (stepI (u := [])); [done | done |].
      rewrite /srs. do 5 apply /In_appr. apply /in_flat_map.
      move: y Hyl => [n op] /ForallE [[? ->]] _. exists n.
      constructor; [apply /in_seq; by lia | move=> /=; by tauto].
    + apply: (reachable_applI (u := [so])). 
      apply: IH => /=; [by lia | by left |].
      constructor; first by (constructor; by [|lia]).
      by move: Hyl => /ForallE [].
  - move=> /copy [Hu] /IH {}IH /ForallE [Hx /IH] /(_ ltac:(lia)) {}IH.
    apply: (rt_trans (y := x :: repeat so (length u))); first by apply: (reachable_applI (u := [x])).
    move: (u) Hu => [|? u']; first done.
    move=> _ /=. apply: rt_step. apply: (stepI (u := [])); [done | done |].
    move: x Hx => [n ?] [? ->].
    rewrite /srs. do 5 apply /In_appr. apply /in_flat_map.
    exists n.
    constructor; [apply /in_seq; by lia | move=> /=; by tauto].
Qed.


Section Transport.
(* number of steps until halting *)
Context (n_cm: nat).
Definition c0 := {| state := 0; value1 := 0; value2 := 0 |}.
Context (H_n_cm: halting cm (Nat.iter n_cm (CM2.step cm) c0)).

Lemma cm_value1_ub n : value1 (Nat.iter n (CM2.step cm) c0) <= n_cm.
Proof.
  have [|->] : n <= n_cm \/ n = ((n - n_cm) + n_cm) by lia.
  - move=> ?. have := values_ub cm c0 n.
    rewrite /c0 /=. by lia.
  - rewrite iter_plus halting_eq; first done.
    have := values_ub cm c0 n_cm.
    rewrite /c0 /=. by lia.
Qed.

Lemma cm_value2_ub n : value2 (Nat.iter n (CM2.step cm) c0) <= n_cm.
Proof.
  have [|->] : n <= n_cm \/ n = ((n - n_cm) + n_cm) by lia.
  - move=> ?. have := values_ub cm c0 n.
    rewrite /c0 /=. by lia.
  - rewrite iter_plus halting_eq; first done.
    have := values_ub cm c0 n_cm.
    rewrite /c0 /=. by lia.
Qed.

Lemma cm_state_ub n : state (Nat.iter n (CM2.step cm) c0) < state_bound.
Proof.
  elim: n; first by (rewrite /= /state_bound; lia).
  move=> n /=. move: (Nat.iter _ _ c0) => [p a b] /=.
  move Hoi: (nth_error cm p) => oi. case: oi Hoi; last done.
  case.
  - by move=> > /state_boundP.
  - move: a b => [|?] [|?] [] > /state_boundP /=; by lia.
Qed.

Definition d := 5 + n_cm + n_cm. (* maximal space requirement *)

(* s is (0^(n-a) l_p _^a m _^b r 0^(n-b)) with a unique state annotation *)
Definition enc_Config : Config -> list Symbol :=
  fun '{| state := p; value1 := a; value2 := b |} => 
    (repeat sz (1 + n_cm-a)) ++ [sl' p] ++ (repeat sb a) ++ [sm] ++ 
    (repeat sb b) ++ [sr] ++ (repeat sz (1 + n_cm-b)).

(* s is (0^(n-a) l _^a m _^b r_p 0^(n-b)) with a unique state annotation *)
Definition enc_Config' : Config -> list Symbol :=
  fun '{| state := p; value1 := a; value2 := b |} => 
    (repeat sz (1 + n_cm-a)) ++ [sl] ++ (repeat sb a) ++ [sm] ++ 
    (repeat sb b) ++ [sr' p] ++ (repeat sz (1 + n_cm-b)).

Arguments List.app : simpl never.

Lemma reachable_enc_c0 : reachable srs (repeat sz d) (enc_Config c0).
Proof using.
  apply: (rt_trans (y := (repeat sz (1 + n_cm)) ++ [sz] ++ [st] ++ [sr] ++ (repeat sz (1 + n_cm)))).
  - have ->: d = 1 + n_cm + 1 + 1 + 1 + 1 + n_cm by (rewrite /d; lia).
    rewrite -?repeat_appP -?app_assoc. do ? apply: reachable_applI.
    apply /rt_step /(stepI (u := [])); [done | done |].
    apply /In_appl. rewrite /=. by tauto.
  - apply /rt_step /(stepI (u := repeat sz (1 + n_cm))); [done | done |].
    apply /In_appl. rewrite /=. by tauto.
Qed.

Lemma move_sb_right' {p n x y} : p < state_bound -> ((x, y) = (1, 3) \/ (x, y) = (3, 2)) ->
  reachable srs ([(x, Some p)] ++ repeat sb n ++ [(y, None)]) ([(x, None)] ++ repeat sb n ++ [(y, Some p)]).
Proof.
  move=> ? /= Hxy. case: n.
  - apply: rt_step. apply: (stepI (u := []) (v := [])); [done | done |].
    rewrite /srs. apply /In_appr /In_appr /In_appl /in_flat_map. exists p.
    constructor; [apply /in_seq; by lia | move: Hxy => /= [] [-> ->]; by tauto].
    
  - move=> n. apply: (rt_trans (y := [(x, None)] ++ [sb' p] ++ (repeat sb n) ++ [(y, None)])).
    + rewrite /= -/([sb] ++ _) ?app_assoc. do 2 apply: reachable_apprI. 
      apply /rt_step /(stepI (u := []) (v := [])); [by reflexivity| by reflexivity | ].
      apply /In_appr /In_appr /In_appl /in_flat_map. exists p.
      constructor; [apply /in_seq; by lia | move: Hxy => /= [] [-> _]; by tauto].
    + rewrite -?app_assoc. apply: reachable_applI. 
      apply: (rt_trans (y := (repeat sb n) ++ [sb' p] ++ [(y, None)])).
      * rewrite ?app_assoc. apply: reachable_apprI. by apply: move_sb_right.
      * apply: rt_step. 
        apply: (stepI (u := repeat sb n) (v := [])); [by reflexivity | |].
        ** by rewrite (ltac:(lia) : S n = n + 1) -repeat_appP -?app_assoc.
        ** apply /In_appr /In_appr /In_appl /in_flat_map. exists p.
          constructor; [apply /in_seq; by lia | move: Hxy => /= [] [_ ->]; by tauto].
Qed.

Lemma move_right n : let c := (Nat.iter n (CM2.step cm) c0) in 
  reachable srs (enc_Config c) (enc_Config' c). 
Proof.
  move=> c. subst c.
  move Hc: (Nat.iter n _ c0) => c.
  case: c Hc => p a b Hc /=.
  apply: (reachable_applI (u := repeat sz _)).
  rewrite ?app_assoc. apply: reachable_apprI.
  have := cm_state_ub n. rewrite Hc /= => ?.
  apply: (rt_trans (y := [sl] ++ (repeat sb a) ++ [sm' p] ++ (repeat sb b) ++ [sr])).
  - rewrite ?app_assoc. do 2 apply: reachable_apprI.
    apply: move_sb_right'; by tauto.
  - rewrite -?app_assoc. do 2 apply: reachable_applI.
    apply: move_sb_right'; by tauto.
Qed.

Lemma move_left n : let c := (Nat.iter n (CM2.step cm) c0) in 
  reachable srs (enc_Config' c) (enc_Config c). 
Proof.
Admitted.

Arguments Nat.sub : simpl never.
Arguments repeat : simpl never.

Lemma simulate_cm_step {n} : let c := (Nat.iter n (CM2.step cm) c0) in
  reachable srs (enc_Config c) (enc_Config (CM2.step cm c)).
Proof.
  move=> c. subst c.
  have := cm_value2_ub n. have := cm_value1_ub n.
  have := move_right n. have := move_left (1+n). move=> /=.
  case: (Nat.iter n _ _) => p a b /=.
  move Hoi: (nth_error cm p) => oi.
  case: oi Hoi; last by (move=> *; apply: rt_refl). case; case.
  (* inc b *)
  - move=> /nth_error_Some_in_combine Hp /= Hr Hl ? ?.
    apply: rt_trans; first by eassumption.
    apply: rt_trans; last by eassumption.
    rewrite -/(repeat sb (S b)) (ltac:(lia) : S b = b + 1) -repeat_appP -?app_assoc.
    do 5 apply: reachable_applI. rewrite ?app_assoc.
    rewrite (ltac:(lia) : (S n_cm - b) = 1 + ((S n_cm - (b + 1)))) -repeat_appP ?app_assoc.
    apply: reachable_apprI.
    apply /rt_step /(stepI (u := []) (v := [])); [done | done |].
    apply /In_appr /In_appl /in_flat_map.
    eexists. constructor; [by eassumption | by left].
  (* inc a *)
  - move=> /nth_error_Some_in_combine Hp _ _ ? ?. apply: rt_step.
    apply: (stepI (u := repeat sz (n_cm-a)) (a := sz) (b := sl' p) (c := sl' (S p)) (d := sb)).
    + by rewrite (ltac:(lia) : S n_cm - a = (n_cm - a) + 1) -repeat_appP /= -app_assoc /=.
    + done.
    + rewrite /srs. apply /In_appr /In_appl /in_flat_map.
      eexists. constructor; [by eassumption | by left].
  (* dec b q *)
  - move=> q /nth_error_Some_in_combine Hp /= Hr Hl _ Hb.
    apply: rt_trans; first by eassumption.
    apply: rt_trans; last by eassumption.
    case: (b) Hb => [_ | b' Hb'] /=.
    + do 3 apply: reachable_applI. apply: rt_step. 
      apply: (stepI (u := [])); [done | done |].
      rewrite /srs. apply /In_appr /In_appl /in_flat_map.
      eexists. constructor; [by eassumption | by left].
    + 
      rewrite -/(repeat sb (S b')) (ltac:(lia) : S b' = b' + 1) (ltac:(lia) : S n_cm - b' = 1 + (S n_cm - (b' + 1))).
      rewrite -?repeat_appP -?app_assoc.
      do 5 apply: reachable_applI. apply: rt_step. 
      apply: (stepI (u := [])); [done | done |].
      rewrite /srs. apply /In_appr /In_appl /in_flat_map.
      eexists. constructor; [by eassumption | right; by left].
  (* dec a q*)
  - move=> q /nth_error_Some_in_combine Hp _ _ Ha _. apply: rt_step.
    case: (a) Ha => [_ | a' Ha'] /=.
    + apply: (stepI (u := repeat sz (1+n_cm))); [done | done |].
      rewrite /srs. apply /In_appr /In_appl /in_flat_map.
      eexists. constructor; [by eassumption | by left].
    + rewrite (ltac:(lia) : (S n_cm - a' = (n_cm - a') + 1)) -repeat_appP -?app_assoc.
      apply: (stepI (u := repeat sz (n_cm - a'))); [done | done |].
      rewrite /srs. apply /In_appr /In_appl /in_flat_map.
      eexists. constructor; [by eassumption | right; by left].
Qed.

Lemma simulate_cm_halting {n} : let c := (Nat.iter n (CM2.step cm) c0) in
  halting cm c -> reachable srs (enc_Config c) (repeat so d).
Proof.
  move=> c /haltingP. subst c.
  have := cm_value1_ub n. have := cm_value2_ub n. have := cm_state_ub n.
  move: (Nat.iter _ _ c0) => [p a b] /= *.
  apply: (rt_trans (y := (repeat sz (n_cm - a)) ++ [so; so] ++ _)).
  - apply: rt_step. rewrite (ltac:(lia) : S n_cm - a = (n_cm - a) + 1) -repeat_appP -?app_assoc.
    apply: (stepI (u := repeat sz (n_cm - a))); [done | done |].
    rewrite /srs. apply /In_appr /In_appr /In_appr /In_appr /In_appl.
    apply /in_map_iff. exists p. constructor; first done.
    apply /in_seq. by lia.
  - apply: reachable_repeat_soI.
    + congr repeat. rewrite ?app_length ?repeat_length /= /d. by lia.
    + apply /In_appr. by left.
    + rewrite ?Forall_norm ?Forall_repeatP (ltac:(done) : (None = None) <-> True).
      by lia.
Qed.
End Transport.

Lemma transport : CM2_HALT cm -> SR2ab (srs, sz, so).
Proof.
  move=> [n /copy [Hn] /(simulate_cm_halting n Hn) H]. exists (@d n).
  apply: rt_trans; last by eassumption.
  apply: rt_trans; first by apply: (reachable_enc_c0).
  elim: (n in Nat.iter n); first by apply: rt_refl.
  move=> m IH {H}. apply: rt_trans; [by exact: IH | by apply: simulate_cm_step].
Qed.

Print Assumptions transport.
  

OBSOLETE
(* s is (0^n1 l _^a m _^b r 0^n2) with a unique state annotation *)
Definition enc_Config : Config -> list Symbol -> Prop :=
  fun '{| state := p; value1 := a; value2 := b |} s => 
  exists n1 n2, map fst s = 
    map fst ((repeat sz n1) ++ [sl] ++ (repeat sb a) ++ [sm] ++ (repeat sb b) ++ [sr] ++ (repeat sz n2))
  /\ exists m1 m2, map snd s = (repeat None (n1 + m1)) ++ [Some p] ++ (repeat None (n2 + m2)).

(* position the state at l *)
Lemma asd {c s} : enc_Config c s -> exists t, reachable srs s t /\ enc_Config c t /\ In (sl' (state c)) t.

(*

(* in_state p v means that v contains exactly one stateful symbol (containing p) *)
Inductive in_state (p: nat) : list Symbol -> Prop :=
  | in_state_hd {v n} : Forall (fun '(_, y) => y = None) v -> in_state p (((n, Some p)) :: v)
  | in_state_tl {v n} : in_state p v -> in_state p (((n, None)) :: v).

Definition enc_Config : Config -> list Symbol -> Prop :=
  fun '{| state := p; value1 := a; value2 := b |} s => 
  exists u v w, 
    (* s is (u l 0^a m 0^b r v) with a unique state annotation *)
    s = u ++ v ++ w /\ in_state p v /\ 
    map fst v = map fst ([sl] ++ (repeat sb a) ++ [sm] ++ (repeat sb b) ++ [sr]).

(* cm step is simulated by sr step *)
Lemma cm_step_to_sr_step {c: Config} {s: list Symbol} : 
  enc_Config c s -> exists t, SR01.reachable srs s t /\ enc_Config (CM2.step cm c) t.
Proof.
  move: c => [p a b] /= [u] [v] [w] [->] [Hpv Hv].
  case: (nth_error cm p); first last.
  { exists (u ++ v ++ w). constructor; [apply: rt_refl | by exists u, v, w]. }
  case.
  (* inc instruction *)
  - 
*)

