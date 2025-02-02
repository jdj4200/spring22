(** * 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 1 *)

(* Welcome to 6.822!  Read through `Pset1Signature.v` before starting here. *)

Require Import Frap Pset1Signature.

Module Impl.
  (* The first part of this assignment involves the [bool] datatype,
   * which has the following definition.
   * <<
       Inductive bool :=
       | true
       | false.
     >>
   * We will define logical negation and conjunction of Boolean values,
   * and prove some properties of these definitions.
   *)

  (* Define [Neg] so that it implements Boolean negation, which flips
   * the truth value of a Boolean value.
   *)
  Definition Neg (b : bool) : bool :=
    match b with
    | true => false
    | false => true
    end.


  Compute Neg true.
  
  
  (* For instance, the negation of [true] should be [false].
   * This proof should follow from reducing both sides of the equation
   * and observing that they are identical.
   *)
  Theorem Neg_true : Neg true = false.
  Proof.
    equality.
Qed.    

  (* Negation should be involutive, meaning that if we negate
   * any Boolean value twice, we should get the original value back.

   * To prove a fact like this that holds for all Booleans, it suffices
   * to prove the fact for both [true] and [false] by using the
   * [cases] tactic.
   *)
  Theorem Neg_involutive : forall b : bool, Neg (Neg b) = b.
  Proof.
    induct b; equality.
    Qed.

  (* Define [And] so that it implements Boolean conjunction. That is,
   * the result value should be [true] exactly when both inputs
   * are [true].
   *)
    Definition And (x y : bool) : bool :=
      match x, y with
      | true, true => true
      | _, _  => false
      end.

  (* Here are a couple of examples of how [And] should act on
   * concrete inputs.
   *)
  Theorem And_true_true : And true true = true.
  Proof.
    equality.
    Qed.
  
  Theorem And_false_true : And false true = false.
  Proof.
    equality.
    Qed.

  (* Prove that [And] is commutative, meaning that switching the order
   * of its arguments doesn't affect the result.
   *)
  Theorem And_comm : forall x y : bool, And x y = And y x.
  Proof.
    induct x; try equality.
    induct y; equality.
    Qed.

  (* Prove that the conjunction of a Boolean value with [true]
   * doesn't change that value.
   *)
  Theorem And_true_r : forall x : bool, And x true = x.
  Proof.
    induct x; try equality.
    Qed.

  (* In the second part of this assignment, we will work with a simple language
   * of imperative arithmetic programs that sequentially apply operations
   * to a natural-number-valued state.

   * The [Prog] datatype defines abstract syntax trees for this language.
   *)

  Print Prog.

  (* Define [run] such that [run p n] gives the final state
   * that running the program [p] should result in, when the
   * initial state is [n].
   *)
  Fixpoint run (p : Prog) (initState : nat) : nat :=
    match p with
    | Done => initState
    | AddThen n next => run next (initState + n)
    | MulThen n next => run next (initState * n)
    | DivThen n next => run next (initState /  n)
    | VidThen n next => run next (n / initState)
    | SetToThen n next => run next  n
    end.

  Theorem run_Example1 : run Done 0 = 0.
  Proof.
    equality.
  Qed.

  Theorem run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
  Proof.
    equality.
    Qed.

  Theorem run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.
  Proof.
    equality.
  Qed.

  Theorem run_Example4 : run (DivThen 2 Done) 1 = 0.
  Proof. equality. Qed.

  (* Define [numInstructions] to compute the number of instructions
   * in a program, not counting [Done] as an instruction.
   *)
  Fixpoint numInstructions (p : Prog) : nat :=
   match p with
    | Done => 0
    | AddThen _ next  => 1 + numInstructions next
    | MulThen _ next => 1 + numInstructions next
    | DivThen _ next => 1 + numInstructions next
    | VidThen _ next => 1 + numInstructions next
    | SetToThen _ next => 1 + numInstructions next
   end.
   
  Theorem numInstructions_Example :
    numInstructions (MulThen 5 (AddThen 2 Done)) = 2.
  Proof.
    equality.
    Qed.

  (* Define [concatProg] such that [concatProg p1 p2] is the program
   * that first runs [p1] and then runs [p2].
   *)
  Fixpoint concatProg (p1 p2 : Prog) : Prog :=
    match p1 with
    | Done => p2
    | AddThen n next  => AddThen n (concatProg next p2)
    | MulThen n next => MulThen n (concatProg next p2)
    | DivThen n next => DivThen n (concatProg next p2)
    | VidThen n next => VidThen n (concatProg next p2)
    | SetToThen n next => SetToThen n (concatProg next p2)
   end.

  Theorem concatProg_Example :
       concatProg (AddThen 1 Done) (MulThen 2 Done)
       = AddThen 1 (MulThen 2 Done).
  Proof.
    equality.
    Qed.

  (* Prove that the number of instructions in the concatenation of
   * two programs is the sum of the number of instructions in each
   * program.
   *)
  Theorem concatProg_numInstructions
    : forall (p1 p2 : Prog), numInstructions (concatProg p1 p2)
                        = numInstructions p1 + numInstructions p2.
  Proof.
    induct p1; simplify; try equality.
  Qed.
  
  (* Prove that running the concatenation of [p1] with [p2] is
     equivalent to running [p1] and then running [p2] on the
     result. *)
  Theorem concatProg_run
    : forall (p1 p2 : Prog) (initState : nat),
      run (concatProg p1 p2) initState =
      run p2 (run p1 initState).
  Proof.
    induct p1; simplify; try equality.
    Qed.

  (* Read this definition and understand how division by zero is handled. *)
  Fixpoint runPortable (p : Prog) (state : nat) : bool * nat :=
    match p with
    | Done => (true, state)
    | AddThen n p => runPortable p (n+state)
    | MulThen n p => runPortable p (n*state)
    | DivThen n p =>
        if n ==n 0 then (false, state) else
        runPortable p (state/n)
    | VidThen n p =>
        if state ==n 0 then (false, 0) else
        runPortable p (n/state)
    | SetToThen n p =>
        runPortable p n
    end.
  Arguments Nat.div : simpl never. (* you don't need to understand this line *)

  (* Here are a few examples: *)

  Definition goodProgram1 := AddThen 1 (VidThen 10 Done).
  Example runPortable_good : forall n,
    runPortable goodProgram1 n = (true, 10/(1+n)).
  Proof. simplify. equality. Qed.

  Definition badProgram1 := AddThen 0 (VidThen 10 Done).
  Example runPortable_bad : let n := 0 in
    runPortable badProgram1 n = (false, 0).
  Proof. simplify. equality. Qed.

  Definition badProgram2 := AddThen 1 (DivThen 0 Done).
  Example runPortable_bad2 : forall n,
    runPortable badProgram2 n = (false, 1+n).
  Proof. simplify. equality. Qed.

  (* Prove that running the concatenation [p] using [runPortable]
     coincides with using [run], as long as [runPortable] returns
     [true] to confirm that no divison by zero occurred. *)
  Lemma runPortable_run : forall p s0 s1,
    runPortable p s0 = (true, s1) -> run p s0 = s1.
  Proof.
    induct p; simplify.

    equality.

    apply IHp.
    Search (_ + _ = _ + _).
    rewrite Nat.add_comm.
    apply H.

    apply IHp.
    rewrite Nat.mul_comm.
    apply H.

    cases n.
    simplify.
    apply IHp.
    equality.

    simplify.
    apply IHp.
    apply H.

    cases s0.
    simplify.
    apply IHp.
    equality.

    simplify.
    apply IHp.
    apply H.

    apply IHp.
    apply H.
Qed.

  (* The final goal of this pset is to implement [validate : Prog -> bool]
     such that if this function returns [true], the program would not trigger
     division by zero regardless of what state it starts out in.  [validate] is
     allowed to return [false] for some perfectly good programs that never cause
     division by zero, but it must recognize as good the examples given below.  In
     jargon, [validate] is required to be sound but not complete, but "complete
     enough" for the use cases defined by the examples given here: *)

  Definition goodProgram2 := AddThen 0 (MulThen 10 (AddThen 0 (DivThen 1 Done))).
  Definition goodProgram3 := AddThen 1 (MulThen 10 (AddThen 0 (VidThen 1 Done))).
  Definition goodProgram4 := Done.
  Definition goodProgram5 := SetToThen 0 (DivThen 1 Done).
  Definition goodProgram6 := SetToThen 1 (VidThen 1 Done).
  Definition goodProgram7 := AddThen 1 (DivThen 1 (DivThen 1 (VidThen 1 Done))).

  (* If you already see a way to build [validate] that meets the
   * requirements above, _and have a plan for how to prove it correct_,
   * feel free to just code away. Our solution uses one intermediate definition
   * and one intermediate lemma in the soundness proof -- both of which are more
   * sophisticated than the top-level versions given here. *)

  (* If a clear plan hasn't emerged in 10 minutes (or if you get stuck later),
   * take a look at the hints for this pset at the end of the signature file.
   * It is not expected that this pset is doable for everyone without the hints,
   * and some planning is required to complete the proof successfully.
   * In particular, repeatedly trying out different combinations of tactics
   * and ideas from hints until something sticks can go on for arbitrarily long
   * with little insight and no success; just guessing a solution is unlikely.
   * Thus, we encourage you to take your time to think, look at the hints when
   * necessary, and only jump into coding when you have some idea why it should
   * succeed. Some may call Coq a video game, but it is not a grinding contest. *)

  (* HINT 1 (see Pset1Signature.v) *)

  Fixpoint validateMinimum (p : Prog) (minimum : nat) : bool :=
    match p with
    | Done => true
    | AddThen n next => validateMinimum next (minimum + n)
    | MulThen n next => validateMinimum next (minimum * n)
    | DivThen n next =>
        if n ==n 0 then false else validateMinimum next (minimum / n)
    | VidThen n next =>
        if minimum ==n 0 then false else validateMinimum next 0
    | SetToThen n next => validateMinimum next n
    end.

  Definition validate (p : Prog) : bool := validateMinimum p 0.

  (* Start by making sure that your solution passes the following tests, and add
   * at least one of your own tests: *)

  Example validate1 : validate goodProgram1 = true.
  Proof. equality. Qed.
  Example validate2 : validate goodProgram2 = true.
  Proof. equality. Qed.
  Example validate3 : validate goodProgram3 = true.
  Proof. equality. Qed.
  Example validate4 : validate goodProgram4 = true.
  Proof. equality. Qed.
  Example validate5 : validate goodProgram5 = true.
  Proof. equality. Qed.
  Example validate6 : validate goodProgram6 = true.
  Proof. equality. Qed.
  Example validate7 : validate goodProgram7 = true.
  Proof. equality. Qed.
  Example validateb1 : validate badProgram1 = false.
  Proof. equality. Qed.
  Example validateb2 : validate badProgram2 = false.
  Proof. equality. Qed.

  (* Then, add your own example of a bad program here, and check that `validate`
   * returns `false` on it: *)

  Definition badProgram3 := AddThen 1 (DivThen 100 (VidThen 1 Done)).
  Example validateb3 : validate badProgram3 = false.
  Proof. equality. Qed.
  
  (* HINTs 2-6 (see Pset1Signature.v)  *)

  (* Finally, before diving into the Coq proof, try to convince yourself that
   * your code is correct by applying induction by hand.  Can you describe the
   * high-level structure of the proof?  Which cases will you have to reason
   * about?  What do the induction hypotheses look like?  Which key lemmas do
   * you need?  Write a short (~10-20 lines) informal proof sketch before
   * proceeding. *)

  (** Proof sketch: **)
  (*At a high level, validateMinimum p m validates p given that the input to p is >= m.
    With this, the key lemma for this proof is to show that if validateMinimum p m = true,
    then runPortable p s = (true, run p s) for all s >= m. This is the inductive hypothesis.

    Inducting on p, the Done case is trivial. The AddThen and MulThen cases boil down to
    the fact that forall n, s >= m -> s + n >= m + n and s * n >= m * n, respectively.

    For the DivThen case, the inductive hypothesis validateMinimum p m = true implies that n    can't equal 0, otherwise validateMinimum p m would be false. So it suffices to show that
    s >= m -> s / n >= m / n forall n > 0.

    Similarly, the VidThen case requires that the current minimum can't be 0, so the
    hypothesis is that for p = (VidThen n next), validateMinimum next 0 = true. Using this,     the fact that s  > 0 -> n / s >= 0 satisfies this case.

    Finally, the SetThen case, p = SetThen n next is satisfied by plugging in n to the
    inductive hypothesis.

    With that key lemma, proving that validate is sound is as simple as noting that validate    is defined as validateMinimum p 0 and every natural number is >= 0.*)
  
  (* Now you're ready to write the proof in Coq: *)

  (* I used this lemma because I needed it for linear_arithmetic.*)
  Lemma ge_Sn_0: forall s, forall m, s >= S m -> s > 0.
  Proof. linear_arithmetic. Qed.

  (* This lemma is used for an impossible case. *)
  Lemma falsehood : 0 > 0 -> false = true.
    Proof. linear_arithmetic. Qed.

  Lemma validateMinimum_sound : forall p, forall m, validateMinimum p m = true ->
                                  forall s, s >= m -> runPortable p s = (true, run p s).
  Proof.
    induct p; simplify.

    equality.
    
    rewrite Nat.add_comm.
    apply IHp with (m := (m+n)).
    apply H.
    linear_arithmetic.

    rewrite Nat.mul_comm.
    apply IHp with (m := (m * n)).
    apply H.
    Search (_ * _).
    apply Nat.mul_le_mono_r.
    apply H0.

    cases n; simplify.

    equality.
    
    apply IHp with (m := m / S n).
    apply H.
    Search (_ / _).
    apply Nat.div_le_mono.
    linear_arithmetic.
    apply H0.

    cases m; simplify.

    equality.

    apply ge_Sn_0 in H0.
    cases s; simplify.
    apply falsehood in H0.
    equality.

    apply IHp with (m := 0).
    apply H.
    linear_arithmetic.
    
    apply IHp with (m := n).
    apply H.
    linear_arithmetic.

    Qed.
    
    
  Lemma validate_sound : forall p, validate p = true ->
    forall s, runPortable p s = (true, run p s).
  Proof.
    unfold validate.
    simplify.
    apply validateMinimum_sound with (m := 0).
    apply H.
    linear_arithmetic.
  Qed.

  
  (* Here is the complete list of commands used in one possible solution:
    - Search, for example Search (_ + 0).
    - induct, for example induct x
    - simplify
    - propositional
    - equality
    - linear_arithmetic
    - cases, for example cases (X ==n Y)
    - apply, for example apply H
    - apply in, for example apply H1 in H2 or apply somelemma in H1
    - apply with, for example apply H1 with (x:=2)
    - apply in with, for example apply H1 with (x:=2) in H2
    - rewrite, for example rewrite H
    - rewrite in, for example rewrite H1 in H2 or rewrite somelemma in H1
    - ;, for example simplify; propositional *)
End Impl.

(* The following line checks that your `Impl` module implements the right
   signature.  Make sure that it works, or the auto-grader will break!
   If there are mismatches, Coq will report them (`Signature components for
   label … do not match`): *)
Module ImplCorrect : Pset1Signature.S := Impl.
