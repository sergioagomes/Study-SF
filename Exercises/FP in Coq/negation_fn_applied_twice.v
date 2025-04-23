(*
Exercise: 1 star, standard (negation_fn_applied_twice)
Now state and prove a theorem negation_fn_applied_twice similar to the previous one but where the second hypothesis says that the function f has the property that f x = negb x.
(* FILL IN HERE *)
(* Do not modify the following line: *)
Definition manual_grade_for_negation_fn_applied_twice : option (nat×string) := None.
(The last definition is used by the autograder.)
*)

Theorem  negation_fn_applied_twicel: 
    forall (f: bool -> bool),
    (forall(x: bool), f x = negb x )->
    forall (b: bool), f (f b) = b.
Proof.
    intros f H b.
    rewrite H .
    rewrite H .
    destruct b; 
    simpl.
    - reflexivity .
    - reflexivity .
Qed.




Definition manual_grade_for_negation_fn_applied_twice : option (nat x string) := None .