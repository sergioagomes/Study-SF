(*
Exercise: 2 stars, standard, optional (decreasing)
To get a concrete sense of this, find a way to write a sensible Fixpoint definition (of a simple function on numbers, say) that does terminate on all inputs, but that Coq will reject because of this restriction.
(If you choose to turn in this optional exercise as part of a homework assignment, make sure you comment out your solution so that it doesn't cause Coq to reject the whole file!)
(* FILL IN HERE *)
☐
*)
Fixpoint loop (n : nat) : nat := loop n.