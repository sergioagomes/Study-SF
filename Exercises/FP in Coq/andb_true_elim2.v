Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b eqn:Eb.
  { (* Case when b = true *)
    destruct c eqn:Ec.
    + (* Case when c = true *)
      reflexivity.
    + (* Case when c = false *)
      intros H.
      simpl in H.
      rewrite H. 
      reflexivity.
  }
  { (* Case when b = false *)
    destruct c eqn:Ec.
    + (* Case when c = true *)
      intros H.
      simpl in H.
      reflexivity.
    + (* Case when c = false *)
      intros H.
      simpl in H.
      rewrite H.
      reflexivity. 
  }
Qed.