(* All of the following are considered preliminaries *)
From Undecidability.HOU Require Export std.tactics std.reductions std.misc std.decidable 
        std.countability std.retracts
        std.lists.basics std.lists.advanced std.lists.misc
        std.ars.basic std.ars.confluence std.ars.normalisation 
        std.ars.evaluator std.ars.list_reduction. 

#[export] Hint Extern 4 => 
match goal with
|[ H: False |- _ ] => destruct H
|[ H: true=false |- _ ] => discriminate H
|[ H: false=true |- _ ] => discriminate H
end : core.