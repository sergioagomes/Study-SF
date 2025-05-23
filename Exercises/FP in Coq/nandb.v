From Coq Require Export String.

Definition nandb (b1:bool) (b2:bool) : bool :=
    match b1, b2 with
    | true, true => false
    | true, false => true
    | false, true => true
    | false, false => true
    end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.
