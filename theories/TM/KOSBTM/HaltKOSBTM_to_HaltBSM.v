Require Import Undecidability.TM.KOSBTM.KOSBTM.

Require Import Undecidability.Shared.Libs.PSL.Vectors.FinNotation Undecidability.Shared.Libs.PSL.Vectors.Vectors Undecidability.Shared.Libs.PSL.EqDec.

Require Import List Arith Lia Bool.

From Undecidability.Shared.Libs.DLW 
  Require Import utils list_bool pos vec subcode sss.

From Undecidability.StackMachines.BSM 
  Require Import bsm_defs.

Import ListNotations.
Import VectorNotations2.
Local Open Scope vector.

Set Default Proof Using "Type".

Tactic Notation "rew" "length" := autorewrite with length_db.

Local Notation "e #> x" := (vec_pos e x).
Local Notation "e [ v / x ]" := (vec_change e x v).

Local Notation "P // s -[ k ]-> t" := (sss_steps (@bsm_sss _) P k s t).
Local Notation "P // r -+> s" := (sss_progress(@bsm_sss _)  P r s).
Local Notation "P // s ->> t" := (sss_compute (@bsm_sss _) P s t).

Definition enc_tape (t : tape) : Vector.t (list bool) 4 := 
    [| left t ; match curr t with Some c => [c] | None => [] end ; right t ; [] |]%vector.

Ltac solve_sc := 
  repeat match goal with
          | [ |- (?i, _) <sc (?i, _)] => eexists [], _; split; [reflexivity | cbn; try lia]
          | [ |- (?o + ?i, ?c1) <sc (?i, ?c2) ] => exists (firstn o c2); eexists; split; [ reflexivity | cbn; lia]
          | [ |- (?l, ?c1) <sc (?i, ?c2) ] => 
            let x := fresh "x" in
            let H := fresh "H" in 
            evar (x : nat);
            assert (l = x + i); [ ring_simplify; subst x; reflexivity | rewrite H; subst x ] 
          end.

Local Hint Extern 0 => solve_sc : core.    

Notation CURR := (Fin1 : Fin.t 4).
Notation LEFT := (Fin0 : Fin.t 4).
Notation RIGHT := (Fin2 : Fin.t 4).
Notation ZERO := (Fin3 : Fin.t 4).
Notation CURR_ := 1.
Notation LEFT_ := 0.
Notation RIGHT_ := 2.
Notation ZERO_ := 3.

Notation JMP i := (POP ZERO i i).

Section fixi.

    Variable i : nat.

    Notation END := (23 + i).

    Definition MOVE_L :=
        [
        (* i *)       POP  CURR (8 + i) (5 + i)   ;
        (* i +  1 *)  POP  LEFT (14 + i) (12 + i) ;
        (* i +  2 *)  PUSH CURR  true ;
        (* i +  3 *)  PUSH RIGHT true;
        (* i +  4 *)  JMP  END ;
        (* i +  5 *)  POP  LEFT (17 + i) END ;
        (* i +  6 *)  PUSH CURR true ;
        (* i +  7 *)  JMP END ;
        (* i +  8 *)  POP LEFT (21 + i) (19 + i) ;
        (* i +  9 *)  PUSH CURR true ;
        (* i + 10 *)  PUSH RIGHT false ;
        (* i + 11 *)  JMP END ;
        (* i + 12 *)  PUSH RIGHT true ;
        (* i + 13 *)  JMP END ;
        (* i + 14 *)  PUSH CURR false ;
        (* i + 15 *)  PUSH RIGHT true ;
        (* i + 16 *)  JMP END ;
        (* i + 17 *)  PUSH CURR false ;
        (* i + 18 *)  JMP END ;
        (* i + 19 *)  PUSH RIGHT false ;
        (* i + 20 *)  JMP END ;
        (* i + 21 *)  PUSH CURR false ;
        (* i + 22 *)  PUSH RIGHT false 
        ].

    Fact MOVE_L_length : length MOVE_L = 23.
    Proof. reflexivity. Qed.

    Fact MOVE_L_spec t : (i,MOVE_L) // (i, enc_tape t) ->> (END, enc_tape (mv Lmove t)).
    Proof.
      unfold MOVE_L.
      destruct t as [[ [ | l ls] [ [] | ] ] rs].
      - bsm sss POP one with CURR (8 + i) (5 + i) [].
        bsm sss POP empty with LEFT (14 + i) (12 + i).
        bsm sss PUSH with RIGHT true.
        bsm sss POP empty with ZERO END END.
        bsm sss stop.
      - bsm sss POP zero with CURR (8 + i) (5 + i) [].
        bsm sss POP empty with LEFT (21 + i) (19 + i). 
        bsm sss PUSH with RIGHT false.
        bsm sss POP empty with ZERO END END.
        bsm sss stop.
      - bsm sss POP empty with CURR (8 + i) (5 + i).
        bsm sss POP empty with LEFT (17 + i) END.
        bsm sss stop.
      - bsm sss POP one with CURR (8 + i) (5 + i) [].
        destruct l.
        + bsm sss POP one with LEFT (14 + i) (12 + i) ls.
          bsm sss PUSH with CURR true.
          bsm sss PUSH with RIGHT true.
          bsm sss POP empty with ZERO END END.
          bsm sss stop.
        + bsm sss POP zero with LEFT (14 + i) (12 + i) ls.
          bsm sss PUSH with CURR false.
          bsm sss PUSH with RIGHT true.
          bsm sss POP empty with ZERO END END.
          bsm sss stop.
      - bsm sss POP zero with CURR (8 + i) (5 + i) [].
        destruct l.
        + bsm sss POP one with LEFT (21 + i) (19 + i) ls.
          bsm sss PUSH with CURR true.
          bsm sss PUSH with RIGHT false.
          bsm sss POP empty with ZERO END END.
          bsm sss stop.
        + bsm sss POP zero with LEFT (21 + i) (19 + i) ls.
          bsm sss PUSH with CURR false.
          bsm sss PUSH with RIGHT false.
          bsm sss stop. 
      - bsm sss POP empty with CURR (8 + i) (5 + i).
        destruct l.
        + bsm sss POP one with LEFT (17 + i) END ls.
          bsm sss PUSH with CURR true.
          bsm sss POP empty with ZERO END END.
          bsm sss stop.
        + bsm sss POP zero with LEFT (17 + i) END ls.
          bsm sss PUSH with CURR false.
          bsm sss POP empty with ZERO END END.
          bsm sss stop. 
    Qed.

    Definition MOVE_R :=
        [
        (* i *)       POP  CURR (8 + i) (5 + i)   ;
        (* i +  1 *)  POP  RIGHT (14 + i) (12 + i) ;
        (* i +  2 *)  PUSH CURR  true ;
        (* i +  3 *)  PUSH LEFT true;
        (* i +  4 *)  JMP  END ;
        (* i +  5 *)  POP  RIGHT (17 + i) END ;
        (* i +  6 *)  PUSH CURR true ;
        (* i +  7 *)  JMP END ;
        (* i +  8 *)  POP RIGHT (21 + i) (19 + i) ;
        (* i +  9 *)  PUSH CURR true ;
        (* i + 10 *)  PUSH LEFT false ;
        (* i + 11 *)  JMP END ;
        (* i + 12 *)  PUSH LEFT true ;
        (* i + 13 *)  JMP END ;
        (* i + 14 *)  PUSH CURR false ;
        (* i + 15 *)  PUSH LEFT true ;
        (* i + 16 *)  JMP END ;
        (* i + 17 *)  PUSH CURR false ;
        (* i + 18 *)  JMP END ;
        (* i + 19 *)  PUSH LEFT false ;
        (* i + 20 *)  JMP END ;
        (* i + 21 *)  PUSH CURR false ;
        (* i + 22 *)  PUSH LEFT false 
        ].

    Fact MOVE_R_length : length MOVE_R = 23.
    Proof. reflexivity. Qed.

    Fact MOVE_R_spec t : (i,MOVE_R) // (i, enc_tape t) ->> (END, enc_tape (mv Rmove t)).
    Proof.
      unfold MOVE_R.
      destruct t as [[ls c] rs]; destruct rs as [ | r rs], c as [ [] | ].
      - bsm sss POP one with CURR (8 + i) (5 + i) [].
        bsm sss POP empty with RIGHT (14 + i) (12 + i).
        bsm sss PUSH with LEFT true.
        bsm sss POP empty with ZERO END END.
        bsm sss stop.
      - bsm sss POP zero with CURR (8 + i) (5 + i) [].
        bsm sss POP empty with RIGHT (21 + i) (19 + i). 
        bsm sss PUSH with LEFT false.
        bsm sss POP empty with ZERO END END.
        bsm sss stop.
      - bsm sss POP empty with CURR (8 + i) (5 + i).
        bsm sss POP empty with RIGHT (17 + i) END.
        bsm sss stop.
      - bsm sss POP one with CURR (8 + i) (5 + i) [].
        destruct r.
        + bsm sss POP one with RIGHT (14 + i) (12 + i) rs.
          bsm sss PUSH with CURR true.
          bsm sss PUSH with LEFT true.
          bsm sss POP empty with ZERO END END.
          bsm sss stop.
        + bsm sss POP zero with RIGHT (14 + i) (12 + i) rs.
          bsm sss PUSH with CURR false.
          bsm sss PUSH with LEFT true.
          bsm sss POP empty with ZERO END END.
          bsm sss stop.
      - bsm sss POP zero with CURR (8 + i) (5 + i) [].
        destruct r.
        + bsm sss POP one with RIGHT (21 + i) (19 + i) rs.
          bsm sss PUSH with CURR true.
          bsm sss PUSH with LEFT false.
          bsm sss POP empty with ZERO END END.
          bsm sss stop.
        + bsm sss POP zero with RIGHT (21 + i) (19 + i) rs.
          bsm sss PUSH with CURR false.
          bsm sss PUSH with LEFT false.
          bsm sss stop. 
      - bsm sss POP empty with CURR (8 + i) (5 + i).
        destruct r.
        + bsm sss POP one with RIGHT (17 + i) END rs.
          bsm sss PUSH with CURR true.
          bsm sss POP empty with ZERO END END.
          bsm sss stop.
        + bsm sss POP zero with RIGHT (17 + i) END rs.
          bsm sss PUSH with CURR false.
          bsm sss POP empty with ZERO END END.
          bsm sss stop. 
    Qed.

End fixi.

Section fixM.

    Variable M : KOSBTM.

    Notation δ := (trans M).

    Variable j : nat.

    Notation "! p" := (proj1_sig (Fin.to_nat p)) (at level 1).

    Notation c := 76.

    Local Notation "'if!' x 'is' p 'then' a 'else' b" := (match x with p => a | _ => b end) (at level 0, p pattern).

    Notation END := (j + (1 + num_states M) * c).

    Definition PROG (i : Fin.t (S (num_states M))) :=
      let off := j + c * !i in
      [
         (*      off *)  POP CURR (26 + off) (51 + off) ;
         (*  1 + off *)  PUSH CURR (if! δ (i, Some true) is Some (_, Some false, _) then false else true)
      ] ++
         (*  2 + off *)  match δ (i, Some true) with Some (_, _, Rmove) => MOVE_R (2 + off) | Some (_, _, Lmove) => MOVE_L (2 + off) | _ => repeat (JMP (25 + off)) 23 end ++
      [  (* 25 + off *)  JMP (match δ (i, Some true) with None => END | Some (q', _, _) => (j + c * ! q') end) ;
         (* 26 + off *)  PUSH CURR (if! δ (i, Some false) is Some (_, Some true, _) then true else false) ]
         ++
         (* 27 + off *)  match δ (i, Some false) with Some (_, _, Rmove) => MOVE_R (27 + off) | Some (_, _, Lmove) => MOVE_L (27 + off) | _ => repeat (JMP (50 + off)) 23 end ++
      [  (* 50 + off *)  JMP (match δ (i, Some false) with None => END | Some (q', _, _) => (j + c * ! q') end) ;
         (* 51 + off *)  match δ (i, None) with None => JMP END | Some (_, Some w, _) => PUSH CURR w | Some _ => JMP (52 + off) end ] ++
         (* 52 + off *)  match δ (i, None) with Some (_, _, Rmove) => MOVE_R (52 + off) | Some (_, _, Lmove) => MOVE_L (52 + off) | _ => repeat (JMP (75 + off)) 23 end ++
      [  (* 75 + off *)  JMP (match δ (i, None) with None => END | Some (q', _, _) => (j + c * ! q') end )
      ]
      .
 
    Fact PROG_length i : length (PROG i) = c.
    Proof. unfold PROG. rewrite app_length.
           destruct (δ (i, Some false)) as [ [[? []] []] | ] eqn:E1;
           destruct (δ (i, Some true)) as [ [[? []] []] | ] eqn:E2;
           destruct (δ (i, None)) as [ [[? []] []] | ]  eqn:E3.
           all:reflexivity.
    Qed. 
 
    Lemma subcode1 i : let off := j  + c * !i in (26 + off, [PUSH CURR (if! δ (i, Some false) is Some (_, Some true, _) then true else false) ]
    ++
    (* 27 + off *)  match δ (i, Some false) with Some (_, _, Rmove) => MOVE_R (27 + off) | Some (_, _, Lmove) => MOVE_L (27 + off) | _ => repeat (JMP (50 + off)) 23 end ++
 [  (* 50 + off *)  JMP (match δ (i, Some false) with None => END | Some (q', _, _) => (j + c * ! q') end) ;
    (* 51 + off *)  match δ (i, None) with None => JMP END | Some (_, Some w, _) => PUSH CURR w | Some _ => JMP (52 + off) end ] ++
    (* 52 + off *)  match δ (i, None) with Some (_, _, Rmove) => MOVE_R (52 + off) | Some (_, _, Lmove) => MOVE_L (52 + off) | _ => repeat (JMP (75 + off)) 23 end ++
 [  (* 75 + off *)  JMP (match δ (i, None) with None => END | Some (q', _, _) => (j + c * ! q') end )
 ]) <sc (off, PROG i).
    Proof.
      intros ?. 
      match goal with
      | [ |- (?o + ?i, ?c1) <sc (?i, ?c2) ] => exists (firstn o c2); exists []; split
      end.
      rewrite app_nil_r. 2:rewrite firstn_length, PROG_length. 2:lia.
      enough (firstn 26 (PROG i) = [ POP CURR (26 + off) (51 + off) ;
      (*  1 + off *)  PUSH CURR (if! δ (i, Some true) is Some (_, Some false, _) then false else true)
   ] ++
      (*  2 + off *)  match δ (i, Some true) with Some (_, _, Rmove) => MOVE_R (2 + off) | Some (_, _, Lmove) => MOVE_L (2 + off) | _ => repeat (JMP (25 + off)) 23 end ++
   [  (* 25 + off *)  JMP (match δ (i, Some true) with None => END | Some (q', _, _) => (j + c * ! q') end)]); subst off. rewrite H. 
      unfold PROG. now rewrite <- !app_assoc. 
      unfold PROG. destruct (δ (i, Some One)) as [ [ [] [] ] | ]; reflexivity.
    Qed.

    Lemma subcode2 i : let off := j + c * !i in (51 + off, [
    (* 51 + off *)  match δ (i, None) with None => JMP END | Some (_, Some w, _) => PUSH CURR w | Some _ => JMP (52 + off) end ] ++
    (* 52 + off *)  match δ (i, None) with Some (_, _, Rmove) => MOVE_R (52 + off) | Some (_, _, Lmove) => MOVE_L (52 + off) | _ => repeat (JMP (75 + off)) 23 end ++
 [  (* 75 + off *)  JMP (match δ (i, None) with None => END | Some (q', _, _) => (j + c * ! q') end )
 ]) <sc (off, PROG i).
    Proof.
      intros ?. 
      match goal with
      | [ |- (?o + ?i, ?c1) <sc (?i, ?c2) ] => exists (firstn o c2); exists []; split
      end.
      rewrite app_nil_r. 2:rewrite firstn_length, PROG_length. 2:lia.
      enough (firstn 51 (PROG i) = [ POP CURR (26 + off) (51 + off) ;
      (*  1 + off *)  PUSH CURR (if! δ (i, Some true) is Some (_, Some false, _) then false else true)
   ] ++
      (*  2 + off *)  match δ (i, Some true) with Some (_, _, Rmove) => MOVE_R (2 + off) | Some (_, _, Lmove) => MOVE_L (2 + off) | _ => repeat (JMP (25 + off)) 23 end ++
   [  (* 25 + off *)  JMP (match δ (i, Some true) with None => END | Some (q', _, _) => (j + c * ! q') end) ;
      (* 26 + off *)  PUSH CURR (if! δ (i, Some false) is Some (_, Some true, _) then true else false) ]
      ++
      (* 27 + off *)  match δ (i, Some false) with Some (_, _, Rmove) => MOVE_R (27 + off) | Some (_, _, Lmove) => MOVE_L (27 + off) | _ => repeat (JMP (50 + off)) 23 end ++
   [  (* 50 + off *)  JMP (match δ (i, Some false) with None => END | Some (q', _, _) => (j + c * ! q') end)]); subst off. rewrite H.  
      unfold PROG. now rewrite <- !app_assoc.
      unfold PROG. destruct (δ (i, Some One)) as [ [ [] [] ] | ]; destruct (δ (i, Some false)) as [ [ [] [] ] | ]; reflexivity.
    Qed.

    Lemma case_Some_false o {X} (c1 c2 : X) : (if! o is Some false then c1 else c2 = c1 /\ o = Some false) 
                            \/ (if! o is Some false then c1 else c2 = c2 /\ o <> Some false).
    Proof using M.
      destruct o as [ [] | ]; firstorder congruence.
    Qed.

    Lemma case_Some_true o {X} (c1 c2 : X) : (if! o is Some true then c1 else c2 = c1 /\ o = Some true) 
                            \/ (if! o is Some true then c1 else c2 = c2 /\ o <> Some true).
    Proof using M.
      destruct o as [ [] | ]; firstorder congruence.
    Qed.

    Lemma case_None (o : option bool) {X} (c2 : X) c1 : (if! o is Some w then c1 w else c2 = c2 /\ o = None) 
                            \/ (exists w, (if! o is Some w then c1 w else c2) = c1 w /\ o = Some w).
    Proof.
      destruct o as [ [] | ]. right. eauto. right. eauto. eauto.
    Qed.

    Fact PROG_spec (i : Fin.t (S (num_states M))) t :
      (j + c * !i, PROG i) // (j + c * !i, enc_tape t) -+> match δ (i, curr t) 
                                                   with None => (END, enc_tape t) |
                                                        Some (q', w, m) => (j + c * !q' , enc_tape (mv m (wr w t)))
                                                   end.
    Proof.
      set (off := j + c * !i).
      destruct t as [[ls [ [] | ]] rs] eqn:Eq_tape.
      - cbn [curr].
        eapply sss_progress_compute_trans. exists 1. split. lia. econstructor. 2:econstructor.
        eapply subcode_sss_step with (P := (off, [POP CURR (26 + off) (51 + off)])). auto.      
        eapply in_sss_step with (l := []). cbn; lia.
        econstructor 3. reflexivity.
        unfold PROG.
        (* bsm sss POP one with CURR (26 + off) (51 + off) []. bsm sss stop.  *)
        destruct (δ (i, Some true)) as [ [[q' w] m] | ] eqn:Eq_nxt.
        + edestruct (@case_Some_false w) as [ [H H0] | [H H0]].
          * rewrite H.
            bsm sss PUSH with CURR false.
            destruct m eqn:Eq_mv.
            -- eapply subcode_sss_compute_trans with (P := (2+off, MOVE_L (2 + off))). eauto.
               cbn - [plus mult].
               eapply (MOVE_L_spec (2 + off) (ls, Some Zero, rs)).
               bsm sss POP empty with ZERO (j + c * ! q') (j + c * ! q').
               bsm sss stop. rewrite H0. reflexivity.
            -- eapply subcode_sss_compute_trans with (P := (2+off, MOVE_R (2 + off))). eauto.
               cbn - [plus mult].
               eapply (MOVE_R_spec (2 + off) (ls, Some Zero, rs)).
               bsm sss POP empty with ZERO (j + c * ! q') (j + c * ! q').
               bsm sss stop. rewrite H0. reflexivity.
            -- bsm sss POP empty with ZERO (25 + off) (25 + off).
               bsm sss POP empty with ZERO (j + c * !q') (j + c * !q').
               bsm sss stop. subst; reflexivity.
          * rewrite H. bsm sss PUSH with CURR true.
            destruct m eqn:Eq_mv.
            -- eapply subcode_sss_compute_trans with (P := (2+off, MOVE_L (2 + off))). eauto.
               cbn - [plus mult].
               eapply (MOVE_L_spec (2 + off) (ls, Some One, rs)).
               bsm sss POP empty with ZERO (j + c * ! q') (j + c * ! q').
               bsm sss stop. destruct w as [ [] | ]; try reflexivity. congruence.
            -- eapply subcode_sss_compute_trans with (P := (2+off, MOVE_R (2 + off))). eauto.
               cbn - [plus mult].
               eapply (MOVE_R_spec (2 + off) (ls, Some One, rs)).
               bsm sss POP empty with ZERO (j + c * ! q') (j + c * ! q').
               bsm sss stop. destruct w as [ [] | ]; try reflexivity. congruence.
            -- bsm sss POP empty with ZERO (25 + off) (25 + off).
               bsm sss POP empty with ZERO (j + c * !q') (j + c * !q').
               bsm sss stop. destruct w as [ [] | ]; try reflexivity. congruence.
        + bsm sss PUSH with CURR true.
          bsm sss POP empty with ZERO (25 + off) (25 + off).
          bsm sss POP empty with ZERO END END.
          bsm sss stop.
      - cbn [curr].
        eapply sss_progress_compute_trans. exists 1. split. lia. econstructor. 2:econstructor.
        eapply subcode_sss_step with (P := (off, [POP CURR (26 + off) (51 + off)])). auto.      
        eapply in_sss_step with (l := []). cbn; lia.
        econstructor 2. reflexivity.
        unfold PROG.
(*         bsm sss POP zero with CURR (26 + off) (51 + off) []. *) 
        eapply subcode_sss_compute_trans; try eapply subcode1. 2:{ bsm sss stop. }
        destruct (δ (i, Some false)) as [ [[q' w] m] | ] eqn:Eq_nxt.
        + edestruct (@case_Some_true w) as [ [] | []].
          * rewrite H. change (j + 76 * !i)  with off.
            bsm sss PUSH with CURR true.
            destruct m eqn:Eq_mv.
            -- eapply subcode_sss_compute_trans with (P := (27+off, MOVE_L (27 + off))). eauto.
               eapply (MOVE_L_spec (27 + off) (ls, Some One, rs)).
               replace (23 + (27 + off)) with (24 + (26 + off)) by lia.
               bsm sss POP empty with ZERO (j + c * ! q') (j + c * ! q').
               bsm sss stop. rewrite H0. reflexivity.
            -- eapply subcode_sss_compute_trans with (P := (27 +off, MOVE_R (27 + off))). eauto.
               eapply (MOVE_R_spec (27 + off) (ls, Some One, rs)).
               replace (23 + (27 + off)) with (24 + (26 + off)) by lia.
               bsm sss POP empty with ZERO (j + c * ! q') (j + c * ! q').
               bsm sss stop. rewrite H0. reflexivity.
            -- bsm sss POP empty with ZERO (50 + off) (50 + off).
               replace (50 + off) with (24 + (26 + off)) by lia.
               bsm sss POP empty with ZERO (j + c * !q') (j + c * !q').
               bsm sss stop. subst; reflexivity.
          * rewrite H. change (j + 76 * !i)  with off.
            bsm sss PUSH with CURR false.
            destruct m eqn:Eq_mv.
            -- eapply subcode_sss_compute_trans with (P := (27+off, MOVE_L (27 + off))). replace (27 + off) with (1 + (26 + off)) at 1 by lia. eauto.
               eapply (MOVE_L_spec (27 + off) (ls, Some false, rs)).
               replace (23 + (27 + off)) with (24 + (26 + off)) by lia.
               bsm sss POP empty with ZERO (j + c * ! q') (j + c * ! q').
               bsm sss stop. destruct w as [ [] | ]; try reflexivity. congruence.
            -- eapply subcode_sss_compute_trans with (P := (27 +off, MOVE_R (27 + off))). 
               replace (27 + off) with (1 + (26 + off)) at 1 by lia. eauto.
               eapply (MOVE_R_spec (27 + off) (ls, Some false, rs)).
               replace (23 + (27 + off)) with (24 + (26 + off)) by lia.
               bsm sss POP empty with ZERO (j + c * ! q') (j + c * ! q').
               bsm sss stop. destruct w as [ [] | ]; try reflexivity. congruence.
            -- bsm sss POP empty with ZERO (50 + off) (50 + off).
               replace (50 + off) with (24 + (26 + off)) by lia.
               bsm sss POP empty with ZERO (j + c * !q') (j + c * !q').
               bsm sss stop. destruct w as [ [] | ]; try reflexivity. congruence.
        + change (j + 76 * !i) with off. 
          bsm sss PUSH with CURR false.
          bsm sss POP empty with ZERO (50 + off) (50 + off).
          replace (50 + off) with (24 + (26 + off)) by lia.
          bsm sss POP empty with ZERO END END.
          bsm sss stop.
      - cbn [curr].
        eapply sss_progress_compute_trans. exists 1. split. lia. econstructor. 2:econstructor.
        eapply subcode_sss_step with (P := (off, [POP CURR (26 + off) (51 + off)])). auto.      
        eapply in_sss_step with (l := []). cbn; lia.
        econstructor 1. reflexivity.
        unfold PROG.
        (* bsm sss POP empty with CURR (26 + off) (51 + off). *)
        eapply subcode_sss_compute_trans; try eapply subcode2. 2:{ bsm sss stop. }
        destruct (δ (i, None)) as [ [[q' w] m] | ] eqn:Eq_nxt.
        + edestruct (@case_None w) as [ [] | []].
          * rewrite H. change (j + 76 * !i)  with off.
            bsm sss POP empty with ZERO (52 + off) (52 + off).
            destruct m eqn:Eq_mv.
            -- eapply subcode_sss_compute_trans with (P := (52+off, MOVE_L (52 + off))). eauto.
               eapply (MOVE_L_spec (52 + off) (ls, None, rs)).
               replace (23 + (52 + off)) with (24 + (51 + off)) by lia.
               bsm sss POP empty with ZERO (j + c * ! q') (j + c * ! q').
               bsm sss stop. rewrite H0. reflexivity.
            -- eapply subcode_sss_compute_trans with (P := (52 +off, MOVE_R (52 + off))). eauto.
               eapply (MOVE_R_spec (52 + off) (ls, None, rs)).
               replace (23 + (52 + off)) with (24 + (51 + off)) by lia.
               bsm sss POP empty with ZERO (j + c * ! q') (j + c * ! q').
               bsm sss stop. rewrite H0. reflexivity.
            -- replace (52 + off) with (1 + (51 + off)) by lia.
               bsm sss POP empty with ZERO (75 + off) (75 + off).
               replace (75 + off) with (24 + (51 + off)) by lia.
               bsm sss POP empty with ZERO (j + c * !q') (j + c * !q').
               bsm sss stop. subst; reflexivity.
          * destruct w eqn:Eq_w.
            -- change (j + 76 * !i)  with off.
               bsm sss PUSH with CURR b.
               destruct m eqn:Eq_mv.
               ++ eapply subcode_sss_compute_trans with (P := (52+off, MOVE_L (52 + off))). replace (52 + off) with (1 + (51 + off)) at 1 by lia. eauto.
                  eapply (MOVE_L_spec (52 + off) (ls, Some b, rs)).
                  replace (23 + (52 + off)) with (24 + (51 + off)) by lia.
                  bsm sss POP empty with ZERO (j + c * ! q') (j + c * ! q').
                  bsm sss stop.
               ++ eapply subcode_sss_compute_trans with (P := (52 +off, MOVE_R (52 + off))). 
                  replace (52 + off) with (1 + (51 + off)) at 1 by lia. eauto.
                  eapply (MOVE_R_spec (52 + off) (ls, Some b, rs)).
                  replace (23 + (52 + off)) with (24 + (51 + off)) by lia.
                  bsm sss POP empty with ZERO (j + c * !q') (j + c * ! q').
                  bsm sss stop.
               ++ bsm sss POP empty with ZERO (75 + off) (75 + off).
                  replace (75 + off) with (24 + (51 + off)) by lia.
                  bsm sss POP empty with ZERO (j + c * !q') (j + c * !q').
                  bsm sss stop.
            -- change (j + 76 * !i)  with off.
               bsm sss POP empty with ZERO (52 + off) (52 + off).
               destruct m eqn:Eq_mv.
               ++ eapply subcode_sss_compute_trans with (P := (52+off, MOVE_L (52 + off))). replace (52 + off) with (1 + (51 + off)) at 1 by lia. eauto.
                  eapply (MOVE_L_spec (52 + off) (ls, None, rs)).
                  replace (23 + (52 + off)) with (24 + (51 + off)
                                                 ) by lia.
                  bsm sss POP empty with ZERO (j + c * !q') (j + c * ! q').
                  bsm sss stop.
               ++ eapply subcode_sss_compute_trans with (P := (52 +off, MOVE_R (52 + off))). 
                  replace (52 + off) with (1 + (51 + off)) at 1 by lia. eauto.
                  eapply (MOVE_R_spec (52 + off) (ls, None, rs)).
                  replace (23 + (52 + off)) with (24 + (51 + off)) by lia.
                  bsm sss POP empty with ZERO (j + c * !q') (j + c * ! q').
                  bsm sss stop.
               ++ replace (52 + off) with (1 + (51 + off)) by lia.
                  bsm sss POP empty with ZERO (75 + off) (75 + off).
                  replace (75 + off) with (24 + (51 + off)) by lia.
                  bsm sss POP empty with ZERO (j + c * !q') (j  + c * !q').
                  bsm sss stop.
        + change (j + 76 * !i) with off. 
          bsm sss POP empty with ZERO END END.
          bsm sss stop.
    Qed.


    Fixpoint sim (n : nat) (H : n <= S (num_states M)) : list (bsm_instr 4).
    Proof using j.
      destruct n.
      - exact [].
      - refine (sim n _ ++ _). abstract lia.
        assert (Hn : n < S (num_states M)) by abstract lia.
        refine (PROG (Fin.of_nat_lt Hn)).
    Defined. 
    
    Definition SIM : list (bsm_instr 4). refine (@sim (S (num_states M)) _). Proof using M j. abstract lia. Defined.

    Lemma sim_length (n : nat) (H : n <= S (num_states M)) : 
       @length (bsm_instr 4) (@sim n H) = c * n.
    Proof.
      induction n.
      - unfold sim. cbn. lia.
      - unfold sim. fold sim. rewrite app_length. rewrite PROG_length. rewrite IHn. lia.
    Qed.

    Lemma SIM_length : length SIM = c * (S (num_states M)).
    Proof.
      unfold SIM. rewrite sim_length. lia.
    Qed.
    Arguments sim _ _ : clear implicits.

    Lemma of_nat_lt_0 n (H : 0 < S n) : Fin.of_nat_lt H = @Fin.F1 n.
    Proof.
      unfold Fin.of_nat_lt. reflexivity.
    Qed.

    Arguments Fin.of_nat_lt _ {_} _.

    Lemma PROG_sim_sc q n (H : n <= S (num_states M)) : ! q < n -> (j + 76 * ! q, PROG q) <sc (j, sim n H).
    Proof.
      revert q.
      induction n as [n IH] using lt_wf_ind; intros q. 
      destruct n.
      - intros. lia.
      - intros H0. eapply le_lt_or_eq in H0 as [H0 | H0].
        + unfold sim. fold sim. eapply subcode_app_end. eapply IH. lia. lia.
        + inversion H0. subst. clear H0. unfold sim. fold sim. revert H IH.
          eapply (Fin.caseS' q).
          * intros H IH. cbn [Fin.to_nat proj1_sig sim]. rewrite of_nat_lt_0.
            cbn - [PROG]. eexists [], []. split. rewrite app_nil_r. reflexivity. reflexivity.
          * clear q. intros q H IH.
            erewrite Fin.of_nat_ext.
            rewrite Fin.of_nat_to_nat_inv.
            eapply subcode_right. rewrite sim_length.
            pose proof (Fin.R_sanity 1 q). clear IH.
            cbn - [mult] in *. destruct (Fin.to_nat q). cbn - [mult] in *. inversion H0. reflexivity.
    Qed.

    Lemma PROG_sc q : (j + 76 * ! q, PROG q) <sc (j, SIM).
    Proof.
      eapply PROG_sim_sc. destruct (Fin.to_nat q). cbn. lia.
    Qed.

    Theorem SIM_computes q t q' t' :
       KOSBTM.eval M q t q' t' -> (j,SIM) // (j + c * !q, enc_tape t) ->> (END, enc_tape t').
    Proof.
      induction 1.
      - eapply subcode_sss_compute_trans with (P := (j + 76 * !q, PROG q)). eapply PROG_sc.
        eapply sss_progress_compute. eapply PROG_spec.
        rewrite H.
        bsm sss stop.
      - eapply subcode_sss_compute_trans with (P := (j + 76 * !q, PROG q)). eapply PROG_sc.
        eapply sss_progress_compute. eapply PROG_spec.
        rewrite H. eapply IHeval.
    Qed.

    Theorem SIM_term q t i out :
       i < j \/ i >= j + length SIM ->
       (j,SIM) // (j + c * !q, enc_tape t) ->> (i, out) -> exists q' t', i = END /\ out = enc_tape t' /\ KOSBTM.eval M q t q' t'.
    Proof.
      intros Hout [k H]. revert q t H.
      induction k as [k IH] using lt_wf_ind; intros q t H.
      edestruct PROG_spec as [k' H'].
      eapply subcode_sss_subcode_inv in H. 4: eapply PROG_sc. 4: eapply H'. 2:{ apply bsm_sss_fun. }
      - destruct H as (k'' & -> & HH).
        destruct (δ (q, curr t)) as [ [[q' w] m] | ] eqn:Eq_nxt.
        + eapply IH in HH.
          * destruct HH as (q'' & t'' & -> & -> & HH). exists q'', t''; repeat split.
            econstructor. eassumption. eassumption.
          * destruct H'. lia.   
        + eapply sss_steps_stop in HH as [= <- <-].
          exists q, t. repeat split. econstructor. eauto.
          unfold out_code. right. unfold fst, code_end, snd, fst, plus. rewrite SIM_length. fold plus. lia.
      - unfold out_code.
        destruct Hout.
        + left. cbn. lia.
        + right. unfold fst, code_end, snd, fst. rewrite PROG_length.
          transitivity (j + length SIM). rewrite SIM_length. destruct (Fin.to_nat q). cbn - [plus mult]. lia. lia.
    Qed.

    Theorem SIM_correct t :
      HaltKOSBTM (M, t) <-> BSM_HALTING (existT _ 4 (existT _ j (existT _ SIM (enc_tape t)))).
    Proof.
      split.
      - intros (q' & t' & H). eapply SIM_computes in H.
        unfold BSM_HALTING. eexists. split. rewrite mult_comm in H.
        match type of H with _ // (?K, _) ->> _ => replace K with j in H end. 2: cbn; lia.
        eapply H.
        unfold out_code. right. unfold fst, code_end, snd, fst. rewrite SIM_length. lia.
      - intros ([i out] & H1 & H2). pose proof (HS := @SIM_term pos0).
        cbn [Fin.to_nat proj1_sig] in HS. rewrite NPeano.Nat.mul_0_r, NPeano.Nat.add_0_r in HS.
        eapply HS in H1 as (q' & t' & -> & -> & H).
        exists q', t'. eassumption. 
        unfold out_code, code_start, code_end, fst, snd in H2. lia.
    Qed.

End fixM.

Require Import Undecidability.Synthetic.Definitions.

Theorem KOSBTM_to_BSM :
  HaltKOSBTM ⪯ Halt_BSM.
Proof.
  unshelve eexists.
  - intros [M t]. exists 4. exists 0. exists (SIM M 0). exact (enc_tape t).
  - intros [M t]. setoid_rewrite Halt_BSM_iff. eapply SIM_correct.
Qed.
