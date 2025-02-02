(*|
=============================================================
 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 8
=============================================================
|*)

Require Import Pset8Sig.

(*|
Introduction
============

Computer programs commonly manipulate data from different sources, at different levels of privacy or trust.  An e-commerce website, for example, might keep track of the contents of each individual cart, and it would be a severe issue if one user got access to the content of another user's cart.

Such “information-flow” issues are of a different nature from the functionality bugs that we usually think of, but they are also pervasive and tricky to detect and fix: for example, for a few weeks in 2011, Facebook's abuse-reporting tool made it possible to access a user's private photos by reporting one of their *public* photos for abuse: the tool would then conveniently offer to report other photos, *including private ones* that the reporter was not allowed to access. (https://www.zdnet.com/article/facebook-flaw-allows-access-to-private-photos/)

In this pset, we will see how type systems can help with information-flow issues.  We will operate in a simplified setting in which all information is either “public” or “private”, and we will concern ourselves only with *confidentiality*, the property that private inputs should not influence public program outputs.

Informally, we'll prove the correctness of a type system such that type-safe programs do not leak private data: that is, we'll prove that changing the private inputs of a well-typed program does not change its public outputs.  We'll say that well-typed programs are “confidential”.

Note that this formulation doesn't rule out side channels: changing the private inputs of a program might change its runtime or even whether it terminates.

Language definition
===================

This is as usual:
|*)

Module Impl.
Inductive bop := Plus | Minus | Times.

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Bop (b : bop) (e1 e2 : arith).

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Declare Scope  arith_scope.
Notation "a + b" := (Bop Plus a b) : arith_scope.
Notation "a - b" := (Bop Minus a b) : arith_scope.
Notation "a * b" := (Bop Times a b) : arith_scope.
Delimit Scope arith_scope with arith.

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (thn els : cmd)
| While (e : arith) (body : cmd).

(* Here are some notations for the language, which again we won't really
 * explain. *)
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";;" := Sequence (at level 76). (* This one changed slightly, to avoid parsing clashes. *)
Notation "'when' e 'then' thn 'else' els 'done'" := (If e%arith thn els) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" := (While e%arith body) (at level 75).

(*|
Program semantics
=================

And the semantics of the language are as expected; the language is made deterministic by defaulting to 0 when a variable is undefined.
|*)

Definition valuation := fmap var nat.

Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Bop bp e1 e2 =>
    match bp with
    | Plus => Nat.add
    | Minus => Nat.sub
    | Times => Nat.mul
    end (interp e1 v) (interp e2 v)
  end.

Inductive eval : valuation -> cmd -> valuation -> Prop :=
| EvalSkip : forall v,
    eval v Skip v
| EvalAssign : forall v x e,
    eval v (Assign x e) (v $+ (x, interp e v))
| EvalSeq : forall v c1 v1 c2 v2,
    eval v c1 v1
    -> eval v1 c2 v2
    -> eval v (Sequence c1 c2) v2
| EvalIfTrue : forall v e thn els v',
    interp e v <> 0
    -> eval v thn v'
    -> eval v (If e thn els) v'
| EvalIfFalse : forall v e thn els v',
    interp e v = 0
    -> eval v els v'
    -> eval v (If e thn els) v'
| EvalWhileTrue : forall v e body v' v'',
    interp e v <> 0
    -> eval v body v'
    -> eval v' (While e body) v''
    -> eval v (While e body) v''
| EvalWhileFalse : forall v e body,
    interp e v = 0
    -> eval v (While e body) v.

(*|
Typing judgment
===============

The `Confidential` judgment below indicates that a program respects confidentiality.  It takes a set of public variables and a command and returns a `Prop` indicating whether the program is safe.  Take the time to understand exactly how `Confidential` works (or, even better, take a few moments to think how you would define a `Confidential` predicate).

In full generality, information-flow systems associate a label to each variable.  We'll simplify things and classify variables as “public” or “private”, and instead of having a map giving the label of each value, we'll keep track of the set of all public variables.

First, we need a way to collect the variables of an expression (we haven't seen the `set` type too often; see the tips in ``Pset8Sig.v`` for a quick recap).
|*)

Fixpoint vars (e: arith) : set var :=
  match e with
  | Const n => {} (** A constant has no variables **)
  | Var x => {x} (** A variable has… one variable! **)
  | Bop _ e1 e2 => vars e1 \cup vars e2 (** An operator's variables are the variables of its subterms **)
  end.

(*|
The parameter `pub` below represents the set of all public variables.  This is predeclared and fixed.  But there is also a distinct `set var` argument.  This is because we need to consider *implicit* as well as *explicit* flows.

- An explicit flow happens when assigning to a variable.  If `e` mentions variable `x`, then `y := e` may cause data to flow from `x` into `y`.  If `x` is private and `y` is public, we want to rule that out.

- An implicit flow happens when assigning to a variable *under a conditional*.  If `e` mentions variable `x`, then `when e then y := 1` may cause data to flow from `x` to `y` (can you see why?).  There, too, if `x` is private and `y` is public, we want to disallow this flow.

This is why we have the second `set var` (`pc`) argument below: in addition to the set of public variables, we keep track of the set of variables from which data may flow implicitly.  We call that set “pc”, for “program counter”.
|*)

Inductive Confidential (pub: set var) : set var (* pc *) -> cmd (* program *) -> Prop :=
| ConfidentialSkip : forall pc,
    Confidential pub pc Skip
(** A `Skip` is safe. **)
| ConfidentialAssignPrivate : forall pc x e,
    ~ x \in pub ->
    Confidential pub pc (Assign x e)
(** Assigning to a private variable is safe. **)
| ConfidentialAssignPublic : forall pc x e,
    vars e \subseteq pub ->
    pc \subseteq pub ->
    Confidential pub pc (Assign x e)
(** Assigning to a public variable variable is safe as long as the expression does not mention private variables and we are not under a conditional that depends on private variables. **)
| ConfidentialSeq : forall pc c1 c2,
    Confidential pub pc c1 ->
    Confidential pub pc c2 ->
    Confidential pub pc (Sequence c1 c2)
(** A sequence is safe if both halves of it are safe. **)
| ConfidentialIf : forall pc e thn els,
    Confidential pub (pc \cup vars e) thn ->
    Confidential pub (pc \cup vars e) els ->
    Confidential pub pc (If e thn els)
(** A conditional is safe if both branches are safe, noting that the branches run with additional variables in the `pc`. **)
| ConfidentialWhile : forall pc e body,
    Confidential pub (pc \cup vars e) body ->
    Confidential pub pc (While e body).
(** A while loop is safe if its body is safe, noting that the body runs with additional variables in the `pc`. **)

(*|
Here are a few examples:
|*)

Definition pub_example := {"x", "y", "z"}. (* Variables x, y, z are public. *)

Example confidential_prog :=
  ("x" <- "y" + 1;;
   "a" <- "a" * "b";;
   when "y" then "a" <- 0 else "b" <- 0 done).

Goal Confidential pub_example {} confidential_prog.
Proof.
  unfold confidential_prog, pub_example.
  apply ConfidentialSeq; simplify.
  - apply ConfidentialSeq; simplify.
    + apply ConfidentialAssignPublic; simplify.
      * sets.
      * sets.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
  - apply ConfidentialIf; simplify.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
Qed.

Example leaky_prog :=
  (when "a" then "x" <- 1 else "x" <- 2 done).

Goal ~ Confidential pub_example {} leaky_prog.
Proof.
  unfold leaky_prog, pub_example, not; simplify.
  invert H; simplify.
  invert H3; simplify.
  - sets.
  - pose proof @subseteq_In _ "a" _ _ H4.
    sets.
Qed.

(*|
Proof of noninterference
=========================

We first need a relation to characterize “equivalent” valuations — that is, valuations that agree on all public variables.  `restrict s m` means restrict the valuation `m` to just the keys in `s`:
|*)

Definition same_public_state pub (v1 v2: valuation) :=
  restrict pub v1 = restrict pub v2.

(* Before we get started proving properties of our type system, please read
 * Pset8Sig.v and consider the questions below. This task is
 * ungraded, but we are assigning it in hopes it helps you complete the
 * following parts.

 Suppose an expression contains only public variables. Under what valuations 
 do we expect them to evaluate to the same value?

 All of them

 Suppose an expression evaluates to different values under different
 valuations. What do we know about this expression if the different valuations
 share the same public state? Do we know anything if the valuations do not 
 share the same public state?

 Same public state, different values -> influenced by private state
 Different public state -> we don't know anything

 The noninterference property says that running a program in states with 
 private variables holding potentially different values does not change the 
 public outputs of the program.

 The key difficulty is to deal with *divergence* — the cases where the two 
 program executions take different paths.

 When does this happen?  How does that translate in terms of the variables
 in `pc`?

 That happens in If statements and While loops, where there are private vars in pc
  
 Can a divergent execution affect the values of public variables?

 Yes

 When a Confidential program executes, in what ways can it modify the 
 valuation? How does this depend on the values of `pc`?

 It can modify the valuation by updating any private vars,
 or public vars, but only if there are no private vars in pc


 *)

Lemma restrict_not_in: forall {K V} (k: K) (v: V) (s: set K) (m: fmap K V),
    ~ k \in s ->
    restrict s (m $+ (k, v)) = restrict s m.
Proof.
  simplify.
  maps_equal.
  excluded_middle (k0 \in s).
    + rewrite !lookup_restrict_true by assumption.
      simplify; equality.
    + rewrite !lookup_restrict_false by assumption.
      equality.
Qed.

Lemma restrict_subseteq: forall {K V} (s t: set K) (m n: fmap K V),
    t \subseteq s->
    restrict s m = restrict s n ->
    restrict t m = restrict t n.
Proof.
  simplify.
  maps_equal.
  excluded_middle (k \in t).
  assert (restrict s m $? k = restrict s n $? k) by equality.
  +  assert (k \in s).
     apply subseteq_In with t; assumption.
     rewrite !lookup_restrict_true by assumption.
     rewrite !lookup_restrict_true in H2 by assumption.
     assumption.
  + rewrite !lookup_restrict_false by assumption.
    equality.
Qed.

Lemma restrict_vars_interp: forall v v2 e,
    restrict (vars e) v = restrict (vars e) v2 ->
    interp e v = interp e v2.
Proof.
  induct e; simplify.
  equality.

  assert (restrict {x} v $? x = restrict {x} v2 $? x) by equality.
  rewrite !lookup_restrict_true in H0.
  cases (v $? x); cases (v2 $? x); simplify; equality.
  sets.
  sets.

  assert (restrict (vars e1) v = restrict (vars e1) v2).
  apply restrict_subseteq with ({ } \cup (vars e1 \cup vars e2)); sets.
  apply IHe1 in H0.
  assert (restrict (vars e2) v = restrict (vars e2) v2).
  apply restrict_subseteq with ({ } \cup (vars e1 \cup vars e2)); sets.
  apply IHe2 in H1.
  cases b; simplify; equality.
Qed.

Fixpoint assignments (c : cmd) : set var :=
  match c with
  | Skip => {}
  | Assign x _ => {x}
  | Sequence c1 c2 => assignments c1 \cup assignments c2
  | If _ thn els => assignments thn \cup assignments els
  | While _ body => assignments body
  end.

Lemma same_public_vars: forall pub v v2,
    same_public_state pub v v2 ->
    forall x, x \in pub -> (v $? x) = (v2 $? x).
Proof.
  simplify.
  invert H.
  assert (restrict pub v $? x= restrict pub v2 $? x) by equality.
  rewrite !lookup_restrict_true in H by assumption.
  assumption.
Qed.

Lemma contrapositive: forall (P Q : Prop), (P -> Q) -> (~Q -> ~P).
Proof.
  simplify.
  propositional.
Qed.

Lemma private_var: forall e v v2 pub,
    interp e v <> interp e v2 ->
    same_public_state pub v v2 ->
    ~ vars e \subseteq pub.
Proof.
  induct e; simplify.
  equality.
  
  assert (forall x, x \in pub -> (v $? x) = (v2 $? x)).
  apply same_public_vars; assumption.
  assert (x \in pub -> (v $? x) = (v2 $? x)).
  apply H1.
  assert ((v $? x) <> (v2 $? x) -> ~ x \in pub).
  apply contrapositive; assumption.
  assert (~x \in pub).
  apply H3.
  cases (v $? x); cases (v2 $? x); simplify; equality.
  sets.

  assert ((interp e1 v <> interp e1 v2) \/ (~ interp e1 v <> interp e1 v2)).
  apply Classical_Prop.classic.
  cases H1; simplify.
  assert (~ vars e1 \subseteq pub).
  apply IHe1 with (v := v) (v2 := v2); assumption.
  sets.

  assert (interp e2 v <> interp e2 v2).
  cases b; simplify; linear_arithmetic.
  assert (~ vars e2 \subseteq pub).
  apply IHe2 with (v := v) (v2 := v2); assumption.
  sets.
Qed.

Lemma divergence: forall c v v2 e pub pc,
    interp e v <> interp e v2 ->
    same_public_state pub v v2 ->
    Confidential pub (pc \cup vars e) c ->
    assignments c \cap pub = {}.
Proof.
  simplify.
  assert (~ vars e \subseteq pub).
  apply private_var with (v := v) (v2 := v2); assumption.
  induct c; simplify.
  sets.
  
  invert H1; sets.

  invert H1.
  assert (assignments c1 \cap pub = { }).
  apply IHc1 with (v := v) (v2 := v2) (e := e) (pc := pc); eauto.
  assert (assignments c2 \cap pub = { }).
  apply IHc2 with (v := v) (v2 := v2) (e := e) (pc := pc); eauto.
  sets.

  invert H1.
  assert (assignments c1 \cap pub = { }).
  apply IHc1 with (v := v) (v2 := v2) (e := e0) (pc := pc \cup vars e); eauto.
  replace ({ } \cup ((pc \cup vars e) \cup vars e0)) with
    (({ } \cup (pc \cup vars e0)) \cup vars e) by sets.
  assumption.
  assert (assignments c2 \cap pub = { }).
  apply IHc2 with (v := v) (v2 := v2) (e := e0) (pc := pc \cup vars e); eauto.
  replace ({ } \cup ((pc \cup vars e) \cup vars e0)) with
    (({ } \cup (pc \cup vars e0)) \cup vars e) by sets.
  assumption.
  sets.

  invert H1.
  apply IHc with (v := v) (v2 := v2) (e := e0) (pc := pc \cup vars e); eauto.
  replace ({ } \cup ((pc \cup vars e) \cup vars e0)) with
    (({ } \cup (pc \cup vars e0)) \cup vars e) by sets.
  assumption.
Qed.

Lemma no_assignments_same_public: forall c pub v v2,
    assignments c \cap pub = {} ->
    eval v c v2 ->
    same_public_state pub v v2.
Proof.
  induct 2; simplify.
  equality.
  unfold same_public_state.
  assert (~ x \in pub) by sets.
  apply restrict_not_in with (v := interp e v) (m := v)  in H0.
  equality.
  
  assert (same_public_state pub v v1).
  apply IHeval1; sets.
  assert (same_public_state pub v1 v2).
  apply IHeval2; sets.
  equality.

  apply IHeval; sets.
  
  apply IHeval; sets.

  assert (same_public_state pub v v').
  apply IHeval1; sets.
  assert (same_public_state pub v' v'').
  apply IHeval2; sets.
  equality.

  equality.
Qed.

Lemma non_interference' :
  forall pub c v1 v1',
    eval v1 c v1' ->
    forall v2 v2' pc, 
    eval v2 c v2' ->
    Confidential pub pc c ->
    same_public_state pub v1 v2 ->
    same_public_state pub v1' v2'.
Proof.
  induct 1; simplify.
  invert H0.
  invert H.
  assumption.
  
  unfold same_public_state.
  invert H.
  invert H1.
  invert H0.
  assert (restrict pub (v $+ (x, interp e v)) = restrict pub v).
  apply restrict_not_in.
  assumption.
  assert (restrict pub (v2 $+ (x, interp e v2)) = restrict pub v2).
  apply restrict_not_in.
  assumption.
  equality.

  clear H5.
  assert (restrict(vars e) v = restrict (vars e) v2).
  apply restrict_subseteq with pub; assumption.
  assert (interp e v = interp e v2).
  apply restrict_vars_interp; assumption.
  rewrite H0.
  excluded_middle (x \in pub).
  assert (restrict pub (v $+ (x, interp e v2)) = (restrict pub v) $+ (x, interp e v2)).
  apply Pset8Sig.Unnamed_thm; assumption.
  assert (restrict pub (v2 $+ (x, interp e v2)) = (restrict pub v2) $+ (x, interp e v2)).
  apply Pset8Sig.Unnamed_thm; assumption.
  equality.
  assert (restrict pub (v $+ (x, interp e v)) = restrict pub v).
  apply restrict_not_in.
  assumption.
  assert (restrict pub (v2 $+ (x, interp e v2)) = restrict pub v2).
  apply restrict_not_in.
  assumption.
  equality.
  
  invert H1.
  invert H2.
  assert (same_public_state pub v1 v4).
  apply IHeval1 with (v2 := v0) (pc := pc); assumption.
  apply IHeval2 with (v2 := v4) (pc := pc); assumption.

  invert H2.
  invert H1.
  apply IHeval with (v2 := v2) (pc := (pc \cup vars e)); assumption.

  assert (assignments thn \cap pub = {}).
  apply divergence with (v := v) (v2 := v2) (e := e) (pc := pc); eauto.
  linear_arithmetic.
  apply no_assignments_same_public with (pub := pub) in H0.
  assert (assignments els \cap pub = {}).
  apply divergence with (v := v) (v2 := v2) (e := e) (pc := pc); eauto.
  linear_arithmetic.
  apply no_assignments_same_public with (pub := pub) in H11.
  equality.
  assumption.
  assumption.
  
  invert H2.
  invert H1.
  assert (assignments thn \cap pub = {}).
  apply divergence with (v := v) (v2 := v2) (e := e) (pc := pc); eauto.
  linear_arithmetic.
  apply no_assignments_same_public with (pub := pub) in H11.
  assert (assignments els \cap pub = {}).
  apply divergence with (v := v) (v2 := v2) (e := e) (pc := pc); eauto.
  linear_arithmetic.
  apply no_assignments_same_public with (pub := pub) in H0.
  equality.
  assumption.
  assumption.
  
  apply IHeval with (v2 := v2) (pc := (pc \cup vars e)); assumption.

  invert H2.
  apply IHeval2 with (v2 := v'0) (pc := pc).
  assumption.
  assumption.
  invert H3.
  apply IHeval1 with (v2 := v2) (pc := (pc \cup vars e)); assumption.

  invert H3.
  assert (assignments body \cap pub = {}).
  apply divergence with (v := v) (v2 := v2') (e := e) (pc := pc); eauto.
  linear_arithmetic.
  apply no_assignments_same_public with (pub := pub) in H0.
  assert (assignments (while e loop body done) \cap pub = {}).
  apply divergence with (v := v) (v2 := v2') (e := e) (pc := pc); eauto.
  linear_arithmetic.
  constructor.
  replace ((pc \cup vars e) \cup vars e) with (pc \cup vars e) by sets.
  assumption.
  apply no_assignments_same_public with (pub := pub) in H1.
  equality.
  assumption.
  assumption.

  invert H0.
  invert H1.
  assert (assignments body \cap pub = {}).
  apply divergence with (v := v) (v2 := v2) (e := e) (pc := pc); eauto.
  linear_arithmetic.
  apply no_assignments_same_public with (pub := pub) in H7.
  assert (assignments (while e loop body done) \cap pub = {}).
  apply divergence with (v := v) (v2 := v2) (e := e) (pc := pc); eauto.
  linear_arithmetic.
  constructor.
  replace ((pc \cup vars e) \cup vars e) with (pc \cup vars e) by sets.
  assumption.
  apply no_assignments_same_public with (pub := pub) in H9.
  equality.
  assumption.
  assumption.

  assumption.
Qed.

(* HINT 1-2 (see Pset8Sig.v) *) 
Theorem non_interference :
  forall pub c v1 v1' v2 v2',
    eval v1 c v1' ->
    eval v2 c v2' ->
    Confidential pub {} c ->
    same_public_state pub v1 v2 ->
    same_public_state pub v1' v2'.
Proof.
  simplify.
  apply non_interference' with (c := c) (v1 := v1) (v2 := v2) (pc := {}); assumption.
Qed.

(*|
Congratulations, you have proved that our type system is *sound*: it catches all leaky programs!  But it is not *complete*: there are some good programs that it rejects, too.  In other words, it *overapproximates* the set of unsafe programs.

Can you give an example of a safe program (a program that does not leak data) that our system would reject?
|*)

Definition tricky_example : cmd :=
  "a" <- 1 ;; "b" <- 1 ;; when "x" then "x" <- "a" else "x" <- "b" done.

Lemma tricky_rejected : ~ Confidential pub_example {} tricky_example.
Proof.
  propositional.
  invert H.
  invert H4.
  invert H2.
  unfold pub_example in H1.
  contradict H1.
  sets.
  simplify.
  unfold pub_example in H4.
  assert ("a" \in {"a"}) by sets.
  apply subseteq_In with (s2 := {"x", "y", "z"}) in H.
  sets.
  assumption.
Qed.

Lemma tricky_confidential :
  forall v1 v1' v2 v2',
    eval v1 tricky_example v1' ->
    eval v2 tricky_example v2' ->
    same_public_state pub_example v1 v2 ->
    same_public_state pub_example v1' v2'.
Proof.
  simplify.
  invert H.
  invert H5.
  invert H4.
  invert H8.
  replace (interp 1 v1) with 1 in H7 by equality.
  replace (interp 1 (v1 $+ ("a", 1))) with 1 in H7 by equality.
  invert H7.
  invert H8.
  
  invert H0.
  invert H4.
  invert H3.
  invert H8.
  replace (interp 1 v2) with 1 in H7 by equality.
  replace (interp 1 (v2 $+ ("a", 1))) with 1 in H7 by equality.
  invert H7.
  invert H8.

  replace (interp "a" (v1 $+ ("a", 1) $+ ("b", 1))) with 1.
  replace (interp "a" (v2 $+ ("a", 1) $+ ("b", 1))) with 1.

  unfold same_public_state in *.
  assert ((restrict pub_example (v1 $+ ("a", 1) $+ ("b", 1) $+ ("x", 1)))
          = (restrict pub_example (v1 $+ ("a", 1) $+ ("b", 1))) $+ ("x", 1)).
  apply Pset8Sig.Unnamed_thm.
  unfold pub_example.
  sets.
  assert ((restrict pub_example (v2 $+ ("a", 1) $+ ("b", 1) $+ ("x", 1)))
          = (restrict pub_example (v2 $+ ("a", 1) $+ ("b", 1))) $+ ("x", 1)).
  apply Pset8Sig.Unnamed_thm.
  unfold pub_example.
  sets.
  replace (restrict pub_example (v1 $+ ("a", 1) $+ ("b", 1))) with (restrict pub_example (v1 $+ ("a", 1))) in H.
  replace (restrict pub_example (v2 $+ ("a", 1) $+ ("b", 1))) with (restrict pub_example (v2 $+ ("a", 1))) in H0.
  replace (restrict pub_example (v1 $+ ("a", 1))) with (restrict pub_example v1) in H.
  replace (restrict pub_example (v2 $+ ("a", 1))) with (restrict pub_example v2) in H0.
  equality.
  unfold pub_example in *.
  assert (~ "a" \in {"x", "y", "z"}) by sets.
  apply restrict_not_in with (v := 1) (m := v2) in H2.
  equality.
  unfold pub_example in *.
  assert (~ "a" \in {"x", "y", "z"}) by sets.
  apply restrict_not_in with (v := 1) (m := v1) in H2.
  equality.
  unfold pub_example in *.
  assert (~ "b" \in {"x", "y", "z"}) by sets.
  apply restrict_not_in with (v := 1) (m := (v2 $+ ("a", 1))) in H2.
  equality.
  unfold pub_example in *.
  assert (~ "b" \in {"x", "y", "z"}) by sets.
  apply restrict_not_in with (v := 1) (m := (v1 $+ ("a", 1))) in H2.
  equality.
  simplify.
  equality.
  simplify.
  equality.

  invert H8.
  unfold pub_example in *.
  assert ({"x"} \subseteq {"x", "y", "z"}) by sets.
  apply restrict_subseteq with (m := v1) (n := v2) in H.
  assert (~ "a" \in {"x"}) by sets.
  apply restrict_not_in with (v := 1) (m := v1) in H0 as H2.
  apply restrict_not_in with (v := 1) (m := v2) in H0 as H3.
  assert (~ "b" \in {"x"}) by sets.
  apply restrict_not_in with (v := 1) (m := (v1 $+ ("a", 1))) in H4 as H7.
  apply restrict_not_in with (v := 1) (m := (v2 $+ ("a", 1))) in H4 as H8.
  assert (restrict {"x"} (v1 $+ ("a", 1) $+ ("b", 1)) = restrict {"x"} (v2 $+ ("a", 1) $+ ("b", 1))) by equality.
  apply restrict_vars_interp with (e := "x") in H9.
  equality.
  apply H1.

  invert H8.
  
  invert H0.
  invert H4.
  invert H3.
  invert H8.
  replace (interp 1 v2) with 1 in H7 by equality.
  replace (interp 1 (v2 $+ ("a", 1))) with 1 in H7 by equality.
  invert H7.
  invert H8.

  unfold pub_example in *.
  assert ({"x"} \subseteq {"x", "y", "z"}) by sets.
  apply restrict_subseteq with (m := v1) (n := v2) in H.
  assert (~ "a" \in {"x"}) by sets.
  apply restrict_not_in with (v := 1) (m := v1) in H0 as H2.
  apply restrict_not_in with (v := 1) (m := v2) in H0 as H3.
  assert (~ "b" \in {"x"}) by sets.
  apply restrict_not_in with (v := 1) (m := (v1 $+ ("a", 1))) in H4 as H7.
  apply restrict_not_in with (v := 1) (m := (v2 $+ ("a", 1))) in H4 as H8.
  assert (restrict {"x"} (v1 $+ ("a", 1) $+ ("b", 1)) = restrict {"x"} (v2 $+ ("a", 1) $+ ("b", 1))) by equality.
  apply restrict_vars_interp with (e := "x") in H9.
  equality.
  apply H1.

  invert H8.

  replace (interp "b" (v1 $+ ("a", 1) $+ ("b", 1))) with 1.
  replace (interp "b" (v2 $+ ("a", 1) $+ ("b", 1))) with 1.
  unfold same_public_state in *.
  assert ((restrict pub_example (v1 $+ ("a", 1) $+ ("b", 1) $+ ("x", 1)))
          = (restrict pub_example (v1 $+ ("a", 1) $+ ("b", 1))) $+ ("x", 1)).
  apply Pset8Sig.Unnamed_thm.
  unfold pub_example.
  sets.
  assert ((restrict pub_example (v2 $+ ("a", 1) $+ ("b", 1) $+ ("x", 1)))
          = (restrict pub_example (v2 $+ ("a", 1) $+ ("b", 1))) $+ ("x", 1)).
  apply Pset8Sig.Unnamed_thm.
  unfold pub_example.
  sets.
  replace (restrict pub_example (v1 $+ ("a", 1) $+ ("b", 1))) with (restrict pub_example (v1 $+ ("a", 1))) in H.
  replace (restrict pub_example (v2 $+ ("a", 1) $+ ("b", 1))) with (restrict pub_example (v2 $+ ("a", 1))) in H0.
  replace (restrict pub_example (v1 $+ ("a", 1))) with (restrict pub_example v1) in H.
  replace (restrict pub_example (v2 $+ ("a", 1))) with (restrict pub_example v2) in H0.
  equality.
  unfold pub_example in *.
  assert (~ "a" \in {"x", "y", "z"}) by sets.
  apply restrict_not_in with (v := 1) (m := v2) in H2.
  equality.
  unfold pub_example in *.
  assert (~ "a" \in {"x", "y", "z"}) by sets.
  apply restrict_not_in with (v := 1) (m := v1) in H2.
  equality.
  unfold pub_example in *.
  assert (~ "b" \in {"x", "y", "z"}) by sets.
  apply restrict_not_in with (v := 1) (m := (v2 $+ ("a", 1))) in H2.
  equality.
  unfold pub_example in *.
  assert (~ "b" \in {"x", "y", "z"}) by sets.
  apply restrict_not_in with (v := 1) (m := (v1 $+ ("a", 1))) in H2.
  equality.
  simplify.
  equality.
  simplify.
  equality.
Qed.

End Impl.

Module ImplCorrect : Pset8Sig.S := Impl.

(* Authors:
   Clément Pit-Claudel 
   Amanda Liu *)
