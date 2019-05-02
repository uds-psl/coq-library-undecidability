From Undecidability Require Import LAM.Prelims L.L.

Inductive Tok := varT (n :nat) | appT | lamT | retT.
Notation Pro := (list Tok) (only parsing).

Fixpoint compile (s: L.term) : Pro :=
  match s with
    var x => [varT x]
  | app s t => compile s ++ compile t ++ [appT]
  | lam s => lamT :: compile s ++ [retT]
  end.

Inductive reprP : Pro -> term -> Prop :=
  reprPC s : reprP (compile s) (lam s).

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

Lemma sizeP_size : forall s, 1+sum (map sizeT (compile s)) <= 2*size s.
Proof.
  induction s;cbn.
  all:autorewrite with list. all:cbn. all:try omega.
Qed.

 

Fixpoint jumpTarget (l:nat) (res:Pro) (P:Pro) : option (Pro*Pro) :=
  match P with
  | retT :: P => match l with
                | 0 => Some (res,P)
                | S l => jumpTarget l (res++[retT]) P
                end
  | lamT :: P => jumpTarget (S l) (res++[lamT])P
  | t :: P    => jumpTarget l (res++[t]) P
  | []        => None
  end.


Lemma jumpTarget_correct s c: jumpTarget 0 [] (compile s ++ retT::c) = Some (compile s,c).
Proof.
  change (Some (compile s,c)) with (jumpTarget 0 ([]++compile s) (retT::c)).
  generalize 0.
  generalize (retT::c) as c'. clear c.
  generalize (@nil Tok) as c. 
  induction s;intros c' c l.
  -reflexivity.
  -cbn. autorewrite with list. rewrite IHs1,IHs2. cbn. now autorewrite with list. 
  -cbn. autorewrite with list. rewrite IHs. cbn. now autorewrite with list.
Qed.

(** Injectivity of compile *)

Fixpoint decompile l P A : option (list term) :=
  match P with
    retT::P => match l with
                0 => Some A
              | S l => match A with
                        s::A => decompile l P (lam s::A)
                      | [] => None
                      end
              end
  | varT n::P => decompile l P (var n::A)
  | lamT::P =>  decompile (S l) P A
  | appT::P => match A with
               t::s::A => decompile l P (app s t::A)
             | _ => None
              end
  | [] => Some A
  end.

Lemma decompile_correct' l s P A:
  decompile l (compile s++P) A = decompile l P (s::A).
Proof.
  induction s in l,P,A|-*. all:cbn.
  -congruence.
  -autorewrite with list. rewrite IHs1. cbn. rewrite IHs2. reflexivity.
  -autorewrite with list. rewrite IHs. reflexivity.
Qed.

Lemma compile_inj s s' :
  compile s = compile s' -> s = s'.
Proof.
  intros eq.
  specialize (@decompile_correct' 0 s [] []) as H1.
  specialize (@decompile_correct' 0 s' [] []) as H2.
  rewrite eq in H1. rewrite H1 in H2. now inv H2.
Qed.
