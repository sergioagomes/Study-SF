Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) ->
    forall (b : bool), f (f b) = b.
Proof.
  intros f H b. (*introduce f, in hypothesis H and b in context*)
  rewrite H.    (*replace f b to b, using hypothesis H *)
  rewrite H.    (*replace f b to b again*)
  reflexivity.  (*proofs b = b by reflexivity*)
Qed.


(*
forall function f: bool -> bool, if f is a indentity function, that
means f x = x forall x: bool, aplies f twice in each boolean b, that's 
result in own b(f(f b) = b).

*)