(*
Exercise: 3 stars, standard, optional (andb_eq_orb)
Prove the following theorem. (Hint: This can be a bit tricky, depending on how you approach it. You will probably need both destruct and rewrite, but destructing everything in sight is not the best way.)
*)

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c H.
  destruct b; destruct c; simpl in H.
  - (*case b= true c= true*)
    simpl. 
    reflexivity. 
  - (* b=true c=false*) 
    rewrite H. 
    simpl.
    reflexivity.
  - 
    rewrite H. 
    reflexivity.
  - 
    simpl. 
    reflexivity.
Qed.
