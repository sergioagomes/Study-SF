From Coq Require Export String.

Inductive day : Type :=
 | monday
 | tuesday
 | wednesday
 | thursday
 | friday
 | saturday
 | sunday.


 Definition next_weekday (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday).
Compute (next_weekday (next_weekday saturday)).

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
  Proof. simpl. reflexivity. Qed.


  Inductive bool : Type :=
  | true
  | false.


Definition negb (b:bool) : bool :=
    match b with
    | true => false
    | false => true
    end.
    

Definition andb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => b2
    | false => false
    end.

Definition orb (b1:bool) (b2:bool) : bool :=
    match b1 with
    | true => true
    | false => b2
    end.
       
Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.


Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).
Notation "! x" := (negb x)(at level 75, right associativity).
Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.
Example test_andb1: true && false = false.
Proof. simpl. reflexivity. Qed.
Example test_negb1:  (! true) = false.
Proof. simpl. reflexivity. Qed.


(* Conditional expressions*)
(*Definition negb' (b:bool) : bool :=
  if b then false
  else true.*)

(*Check type of expression*)
Check true
 : bool .

Check (negb true)
 : bool .

Check negb
 : bool -> bool .


(*Types*)

(*Enumerated type*)
Inductive rgb : Type :=
| red
| green
| blue.

(*ADT*)
Inductive color : Type :=
| black
| white
| primary (p : rgb).


Definition monochrome (c:color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.
(* the pattern primary _  is a shorhand for 
the constructor primary applied to any rgb constructor expect red.*)



(* Define a Module in Coq*)
Module Playground.
  Definition foo : rgb := blue.
  Definition bar : rgb := red.
End Playground.

Definition foo : bool := true.
Definition bar : bool := true.

Check Playground.foo : rgb.
Check foo : bool.

(*Tuples*)
Module TuplePlayGround.

Inductive bit : Type :=
| b1
| b0.

(*Tuple Type*)
Inductive nybble : Type :=
  | bits (b0 b1 b2 b3 : bit).

Check (bits b1 b0 b1 b0)
 : nybble.


(*test with all bits are b0*)
Definition all_zero (nb: nybble) : bool :=
 match nb with
 | (bits b0 b0 b0 b0) => true
 | (bits _ _ _ _) => false
 end.

End TuplePlayGround.

(* Numbers*)
Module NatPlayground.

(*define natural numbers*)
Inductive nat : Type :=
 | O
 | S (n : nat).

(*predecessor function*)
Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.
(*The second branch can be read: "if n has the form S n' for some n', then return n'."
*) 

End NatPlayground.

Check (S(S(S (S 0)))).

Definition minusfour (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S O) => O
  | S (S (S O)) => O
  | S (S (S (S n'))) => n'
  end.

Compute(minusfour 8).

Check S : nat -> nat.
Check pred : nat -> nat.
Check minusfour : nat -> nat.


(*Define Recursion*)
Fixpoint even (n:nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n : nat) : bool :=
   negb (even n).

Example test_odd1: odd 1 = true.
Proof. simpl. reflexivity. Qed.
Example test_odd2: odd 4 = false.
Proof. simpl. reflexivity. Qed.


Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute(plus 10 20).

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n', S m' => minus n' m'
  end.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Compute(exp 2 3).

(* Make numerical expressions easy to read*)
Notation "x + y" := (plus x y)
                    (at level 50, left associativity)
                    : nat_scope.

Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.

Notation "x * y" := (mult x y) 
                    (at level 40, left associativity)
                    : nat_scope.

Check ((0 + 1) + 1) : nat.


(*tests natural numbers for equality*)
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Example test_eqb: eqb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_eqb2: eqb 2 4 = false.
Proof. simpl. reflexivity. Qed.

(*test if the first args is less than or equal to second argument*)
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb1: leb 2 2 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb2: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
Example test_leb3: leb 4 2 = false.
Proof. simpl. reflexivity. Qed.

(*define simple notation for both cases*)
Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.


Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.


(*PROOF BY SIMPLIFICATION*)
Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

(*reflexiviity do simpl*)
Theorem plus_O_n' : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(*PROOF BY REWRITE*)
Theorem plus_id_example : forall n m:nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m H.
  rewrite -> H.
  reflexivity.
Qed.