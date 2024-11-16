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

### Introduction

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
```co