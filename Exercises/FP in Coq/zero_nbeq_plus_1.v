Require Import Nat.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
   intros n.
   destruct n as [| n'].
   - (*Case n = 0*)
    simpl.
    reflexivity.
  - (*Case n = S n' *)
    simpl.
    reflexivity.
Qed.
