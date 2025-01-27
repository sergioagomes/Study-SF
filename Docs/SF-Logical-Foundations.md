# Logical Foundations

## Logic

Logic is the study of reasoning and inference, particularly focusing
on the principles and methods used to determine whether a given statement or argument is valid or invalid.

## Proof Assistants

Proof assistants are software tools designed to assist in the development
and verification of mathematical proofs. these tools fals into two broad categories:

- Automated theorem provers provide "push-button" operation: you give them a proposition and they return either true or false (or, sometimes, don't know: ran out of time). Although their capabilities are still limited to specific domains, they have
  matured tremendously in recent years and are used now in a multitude of settings. Examples of such tools include SAT solvers, SMT solvers, and model checkers.-
- Proof assistants are hybrid tools that automate the more routine aspects of building proofs while depending on
  human guidance for more difficult aspects. Widely used proof assistants include Isabelle, Agda, Twelf, ACL2, PVS, and Coq, among many others.

### Coq

- Coq is a proof assistant that has been under development since 1993, it's provides a rich
  enviroment for interactive development of machine-checked formal reasoning.
- The kernel of the Coq system is a simple proof-checker.
- Include a large library of common definitions and lemmas.

## Functional Programing In Coq

### Data and Functions
#### Day of the Week

defining a set of data values --a type:

```Coq
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.
```

define a new type called day, and monday... are the members, so with type defined
we can write functions that operate on members.

```Coq
Definition next_weekday (d: day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.
```
So the argument and return types of this function are explicitly declared here. coq can ofter figure out these types for itself when ther are not given explicitly, it can do type inferece, but is common include them to make reading easier.

After defined a function, we can check that it works on some examples, in coq are three different ways to do examples, the first is using the command **Compute** to evalute a compound expression involving next_weekday.
```Coq
Compute (next_weekday friday).
(* =>> monday : day*)

Compute (next_weekday (next_weekday saturday)).
(* =>> tuesday : day*)
```
 
So I can record what I expect the reseult to be in the form of a Coq example:
```coq
Example test_next_working_day:
  (next_working_day (next_working_day saturday)) = tuesday.
```

This "code" does two things:
  - It makes an assertion ( second working day after satuarday is tuesday)
  - Gives the assertion a name tha can be used to refer to it later.

So after this Coq can verify it, using:
```coq
Proof. simpl. reflexitivy. Qed.
```

#### Types

- Every expression in Coq has a type, use command **Check** to print a type of an expression
```coq
Check true
  : bool.

(*
  true : bool
	   : bool
*)

Check (negb true)
  : bool.
(*
  ! true : bool
	   : bool
*)
```

- Functions like negb itself are also data values (true and false), their types are called function types, and they're written with arrows, like:
```coq
Check negb
  : bool → bool.
```
- negb type is written **bool -> bool**.
- is read like "Given an input of type bool, this function produces an output of type bool".

#### New Types from Old
- Enumerated Type and ADTs
```coq
(*Enumerated type*)
Inductive rbg : Type :=
| red
| green
| blue.

(*ADTs*)
Inductive color : Type :=
| black
| white
| primary (p : rbg).
```

#### Modules

In Coq, the module system allows you to organize your code and limit the scope of definitions to avoid naming conflicts and improve modularity.



#### Numbers

- define natural number:
```coq
Inductive nat : Type :=
  | O
  | S (n : nat).
```
- With this definition, 0 is represented by **O**, 1 by **S O**, 2 by **S(S O)**.
- O constructor represents zero - (this is a letter "O" not the numeral 0).
- S can be put in front of a natural number to yield another one -- i.e., if n is a natural number, then S n is too.

- So the constructo O belongs to the set nat.
- If **n** is a constructor expression belonging to the set nat, then **S n** is also a constructor expression belonging to the set nat.
- constructor expressions formed in these two ways are the only ones belonging to the set nat.

For most interesting computations involving numbers, simple pattern matching is not enough: we also need recursion. For example, to check that a number n is even, we may need to recursively check whether n-2 is even. Such functions are introduced with the keyword Fixpoint instead of Definition.
```coq
Fixpoint even (n:nat) : bool :=
  match n with
  | O ⇒ true
  | S O ⇒ false
  | S (S n') ⇒ even n'
  end.
```
- Fixpoint is use when we want do recursion.
- We can define functions with multi-argument with recursion:
```coq
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O ⇒ m
  | S n' ⇒ S (plus n' m)
  end.

Compute (plus 3 2).
(* ===> 5 : nat *)
```
- The steps of simplification that Coq performs:
```coq
(*      plus 3 2
   i.e. plus (S (S (S O))) (S (S O))
    ==> S (plus (S (S O)) (S (S O)))
          by the second clause of the match
    ==> S (S (plus (S O) (S (S O))))
          by the second clause of the match
    ==> S (S (S (plus O (S (S O)))))
          by the second clause of the match
    ==> S (S (S (S (S O))))
          by the first clause of the match
   i.e. 5  *)
```
- if two or more arguments have the same type, they casn be written together:
```coq
Fixpoint mult (n m : nat) : nat :=
  match n with
  | O ⇒ O
  | S n' ⇒ plus m (mult n' m)
  end.
```
- we can match two expressions at once by putting a comma between them:
```coq
Fixpoint minus (n m:nat) : nat :=
  match n, m with
  | O , _ ⇒ O
  | S _ , O ⇒ n
  | S n', S m' ⇒ minus n' m'
  end.
```
- We also can make numerical expressions easier to read:
```coq
Notation "x + y" := (plus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x - y" := (minus x y)
                       (at level 50, left associativity)
                       : nat_scope.
Notation "x * y" := (mult x y)
                       (at level 40, left associativity)
                       : nat_scope.
```
- OBS: The level, associativity, and nat_scope annotations control how these notations are treated by Coq's parser.

- Coq comes with almost nothing built-in, so if we want test equality, we need define.
```coq
Fixpoint equality (n m : nat) : bool :=
  match n with
  | O ⇒ match m with
         | O ⇒ true
         | S m' ⇒ false
         end
  | S n' ⇒ match m with
            | O ⇒ false
            | S m' ⇒ equality n' m'
            end
  end.
```

### Proof by Simplification
A proof by simplification involves breaking down complex terms into their simplest forms by systematically applying definitions, axioms, and reduction rules of the system. The goal is to reduce the problem step by step until the conclusion becomes trivial or self-evident. This method is particularly effective when the proof's objective can be achieved solely by simplifying expressions, without requiring additional logical reasoning or case analysis.

```coq
Theorem plus_O_n : ∀ n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.


(*∀ ->  means forall*)
```

- **Theorem:** it's a math afirmation that we want prove.
- **plus_0_n:** theorem name.
- **∀ n : nat, 0 + n = n**
  - **∀ n : nat:** means forall n of type nat 
  - **0 + n = n:** This is the property we are proving. It states that adding 0 to any natural number n results in n itself. 
- **Proof. :** stats proof
    -**intros :** A tactic used to introduce variables or hypotheses into the context of the test. In this case, the variable **n**.
    -**simpl:** It is a tactic that simplifies the expression in the current target. In this case, the expression **0 + n** is simplified to **n,** because the definition of addition in Coq is recursive, and **0 + n** is definitionally equal to **n**.
    - **reflexivity:** It is a tactic used to prove equalities in which both sides are identical or definitionally equal.
    - **Qed. :** Finish proof and saves theorem.

### Proof by Rewriting
Proof by rewriting is a technique that uses a known equality (for example, a hypothesis like x = y) to replace one term with another in an expression.

```coq
Theorem plus_id_example : ∀ n m:nat,
  n = m →
  n + n = m + m.

(*->: means implies *)
```

### Proof by Case Analysis
- Not Everything can be proved by simple calculation and rewriting.
- In general, unknown, hypothetical values (arbitrary numbers, booleans, lists, etc.) can block simplification.
- Example by book, where we get stucked.
- command **Abort** is used to give up for a while.
```coq
Theorem plus_1_neq_0_firsttry: forall n : nat,
 (n + 1) =? 0 = false.

Proof.
  intros n.
  simpl. (*does nothing*)
Abort.
```
- this happens because **n** is unknow, so neither expressions could be simplified.
- So to make progress, we need to consider the possible forms of **n** separately.
- if **n** is **0**, we can calculate the final result of **(n + 1) =? 0**, and check the result is false, and
**n = S n'** for some **n'**.
- But we don't know exactly what number **n + 1** represents.
- we can calculate that at least it will begin with one **S**, with this calculate **(n + 1) =?** again.
- The tatic that tells Coq to consider, separately, the cases where **n = O** and where **n = S n'** is called
**destruct**.
- Example by book:
```coq
Theorem plus_1_neq_0 : ∀ n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. 
  Qed.
```
- destruct generates two subgoals, which we must them prove, separately, in order to get Coq to accept
the theorem.
- Annotation **as [| n']** is called an intro pattern, tell to coq what variable names to introduce in
each subgoal.
- In general, what goes between the square bracks is a list of lists of names, separated by **|**, in our
case, the first component is empty, since O constructor doesn't  take any arguments, the second component
gives a single name, n', since S is a unary constructor.
- In each subgoal, Coq remembers the assumption about n that is relevant for this subgoal -- either n = 0 or n = S n' for some n'.
-  The eqn:E annotation tells to destruct to give name E to this equation.
- the **-** signs after destruct are called bullets, and they mark the parts of the proof that correspond to the two generated subgoals. The part of the proof script that comes after a bullet is the entire proof for the corresponding subgoal.