(** * 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 11 *)

Require Import Frap Pset11Sig.

(* Programmers who start programming with threads and locks soon realize that it
 * is tricky to avoid *deadlocks*, where thread #1 is waiting to take a lock
 * held by thread #2, and thread #2 is waiting to take a lock held by thread #3,
 * and... thread #N is waiting to take a lock held by thread #1.  That's a wait
 * cycle, and none of the threads will ever make progress.
 *
 * The most common wisdom about avoiding deadlocks is to impose a *total order*
 * on the locks.  A thread is only allowed to acquire a lock that is *less than*
 * all locks it currently holds.  In this pset, we formalize a simple static
 * analysis checking that the total-order rule is obeyed, and we prove that any
 * program accepted by the analysis avoids deadlock. *)

(* Please start by reading the definitions in Pset11Sig.v! *)

(* Before diving into the proof hacking, it might be helpful to write a short
   sample program (in Coq) where thread 1 acquires lock 1 and then lock 2,
   while thread 2 tries to acquire lock 2 and then lock 1, and explain (in
   English) how a deadlock can happen: *)

Example bad: prog := [x <- Lock 1 ; y <- Lock 2 ; z <- Unlock 2 ; Unlock 1 ;
                      b <- Lock 2 ; b <- Lock 1 ; c <- Unlock 1 ; Unlock 2].
Compute length bad.
(* FILL IN explanation here *)

(* And now, explain why the total-order rule would reject your example by copy-pasting
   the one rule which rejects it from Pset11Sig.v and briefly describing how it would
   reject it: *)

(* FILL IN explanation here *)

(* The two questions above are not graded, but we hope they help you understand
   the material better! *)

(* Since we use the [a_useful_invariant] theorem, proving [deadlock_freedom]
   reduces to proving this lemma — the only one in this Pset!  See hints at the bottom
   of the signature file if you get stuck, and of course come to office hours if you 
   have any questions or need help. *)


Module Impl.
  (* HINT 1-5 (see Pset11Sig.v) *)

  Lemma no_locks_cmd : forall c, goodCitizen {} c {} ->
                                 forall a, c <> (Lock a).
  Proof.
    induct 1; simplify; try equality.
    sets.
  Qed.

  Lemma no_unlocks_cmd : forall c l, goodCitizen {} c l ->
                                 forall a, c <> (Unlock a).
  Proof.
    induct 1; simplify; equality.
  Qed.

  Lemma no_lock_step_bind: forall h c c2 l,
      goodCitizen {} c l ->
    exists h' l' c', step0 (h, {}, x <- c; c2 x) (h', l', c').
  Proof.
    simplify.
    induct c; simplify.
    eexists; eexists; eexists; eauto.
    invert H0.
    assert (exists (h' : heap) (l' : locks) (c' : cmd),
               step0 (h, { }, x <- c; c2 x) (h', l', c')).
    apply IHc with l2; assumption.
    cases H0; cases H0; cases H0.
    eexists; eexists; eexists; eauto.
    eexists; eexists; eexists; eauto.
    eexists; eexists; eexists; eauto.
    eexists; eexists; eexists; eauto.
    apply no_unlocks_cmd with (a := a) in H.
    equality.
Qed.    
  
Lemma no_locks_freedom :
  forall (h : heap) (p : prog'),
  locksOf p = {} ->
  Forall (fun l_c : locks * cmd => goodCitizen (fst l_c) (snd l_c) { }) p ->
  Forall finished (progOf p) \/ (exists h_l_p' : heap * locks * prog,
                                    step (h, locksOf p, progOf p) h_l_p').
Proof.
  induct 2; simplify.
  left.
  constructor.
  
  cases x.
  assert (locksOf l = { }) by sets.
  apply IHForall in H2.
  cases c; simplify.

  -
    propositional.
    left.
    assert ([Return r] ++ progOf l = Return r :: progOf l) by equality.
    rewrite <- H2.
    apply Forall_app_bwd.
    constructor.
    constructor.
    constructor.
    assumption.
    cases H3.
    right.
    apply step_cat with x.
    rewrite H.
    simplify.
    assert (locksOf l = { }) by sets.
    rewrite H3 in H2.
    assumption.
  -
    propositional.
    right.
    rewrite H.
    simplify.
    assert (exists h' l' c', step0 (h, {}, x <- c; c2 x) (h', l', c')).
    invert H0.
    assert (s = {}) by sets.
    subst.
    apply no_lock_step_bind with (l := l2); assumption.
    cases H2; cases H2; cases H2.
    eauto.
    cases H3.
    right.
    apply step_cat with x.
    rewrite H.
    simplify.
    assert (locksOf l = { }) by sets.
    rewrite H3 in H2.
    assumption.

  -
    propositional.
    right.
    rewrite H.
    simplify.
    eexists.
    apply StepThread1.
    constructor.
    cases H3.
    right.
    apply step_cat with x.
    rewrite H.
    simplify.
    assert (locksOf l = { }) by sets.
    rewrite H3 in H2.
    assumption.

  -
    propositional.
    right.
    rewrite H.
    simplify.
    eexists.
    apply StepThread1.
    constructor.
    cases H3.
    right.
    apply step_cat with x.
    rewrite H.
    simplify.
    assert (locksOf l = { }) by sets.
    rewrite H3 in H2.
    assumption.

  -
    assert (s = {}) by sets.
    rewrite H3 in H0.
    apply no_locks_cmd with (a := a) in H0.
    equality.

  -
    assert (s = {}) by sets.
    rewrite H3 in H0.
    apply no_unlocks_cmd with (a := a) in H0.
    equality.
Qed.


Lemma who_has_the_lock'' : forall h a l l1 c l2,
      goodCitizen l1 c l2
      -> a \in l1
      -> l1 \subseteq l
      -> finished c
         \/ (exists h' l' c', step0 (h, l, c) (h', l', c'))
         \/ (exists a', a' < a /\ a' \in l).
Proof.
  induct 1; simplify.
  left.
  constructor.
  
  right.
  assert (finished c1 \/
                  (exists (h' : heap) (l' : locks) (c' : cmd),
                     step0 (h, l, c1) (h', l', c')) \/
            (exists a' : nat, a' < a /\ a' \in l)).
  eauto.
  propositional.
  left.
  invert H5.
  eexists; eexists; eexists; eauto.
  left.
  cases H6; cases H4; cases H4.
  eauto.
  left.
  invert H5.
  eexists; eexists; eexists; eauto.
  left.
  cases H4; cases H4; cases H4.
  eauto.

  right; left; eauto.
  right; left; eauto.

  assert (a0 \in l \/ ~a0 \in l).
  apply Classical_Prop.classic.
  cases H2.
  right; right.
  exists a0.
  propositional.
  apply H; assumption.
  right; left.
  eauto.

  right; left.
  assert (a \in l) by sets.
  eexists; eexists; eexists; eauto.
Qed.


Lemma who_has_the_lock : forall l h a p,
    Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
    -> a \in locksOf p
    -> locksOf p \subseteq l
    -> (exists h_l_p', step (h, l, progOf p) h_l_p')
       \/ (exists a', a' < a /\ a' \in l).
Proof.
  induct 1; simplify.
  sets.
  cases x.
  assert (a \in locksOf l0 \/ ~a \in locksOf l0).
  apply Classical_Prop.classic.
  cases H3.
  apply IHForall in H3.
  propositional; cases H4.
  left.
  apply step_cat with x.
  assumption.
  sets.

  cases c; simplify; invert H.
  sets.

  apply who_has_the_lock'' with (h := h) (a := a) (l := l) in H7; sets.
  propositional.
  invert H.
  eauto.

  left.
  cases H4; cases H1; cases H1.
  eauto.

  eauto.
  eauto.
  sets.
  left.
  eexists.
  apply StepThread1.
  constructor.
  sets.
Qed.

Lemma empty_set : forall s, ~ (exists a : nat, a \in s) -> s = {}.
Proof.
  simplify.
  sets.
  apply H.
  exists x.
  assumption.
Qed.

Lemma with_locks_freedom: forall bound a h p,
    Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
    -> a \in locksOf p
    -> a < bound
    -> Forall (fun l_c => finished (snd l_c)) p
       \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
Proof.
  induct bound; simplify.
  linear_arithmetic.
  apply who_has_the_lock with (h := h) (l := locksOf p) in H0.
  propositional.
  cases H2.
  cases H0.
  apply IHbound with x.
  assumption.
  assumption.
  linear_arithmetic.
  assumption.
  sets.
Qed.

Lemma deadlock_freedom' :
  forall (h : heap) (p : prog'),
  Forall (fun l_c : locks * cmd => goodCitizen (fst l_c) (snd l_c) { }) p ->
  Forall finished (progOf p) \/ (exists h_l_p' : heap * locks * prog,
                                    step (h, locksOf p, progOf p) h_l_p').
Proof.
  simplify.
  excluded_middle (exists a, a \in locksOf p).
  cases H0.
  apply with_locks_freedom with (h := h) (bound := x + 1) in H0.
  propositional.
  left.
  eauto.
  assumption.
  linear_arithmetic.
  apply empty_set in H0.
  apply no_locks_freedom; assumption.
Qed.

(* Here's how we can use [a_useful_invariant] to go from [deadlock_freedom'] to
   [deadlock_freedom]: *)
Theorem deadlock_freedom :
  forall h p,
    Forall (fun c => goodCitizen {} c {}) p ->
    invariantFor (trsys_of h {} p) (fun h_l_p =>
                                      let '(_, _, p') := h_l_p in
                                      Forall finished p'
                                      \/ exists h_l_p', step h_l_p h_l_p').
Proof.
  (* To begin with, we strengthen the invariant to the one proved in Pset11Sig. *)
  simplify.
  eapply invariant_weaken.
  eauto using a_useful_invariant.

  (* What's left is to prove that this invariant implies deadlock-freedom. *)
  first_order.
  destruct s as [[h' ls] p'].
  invert H0.

  (* We don't actually need to use the [disjointLocks] property.  It was only
   * important in strengthening the induction to prove that other invariant. *)
  clear H6.

  (* At this point, we apply the lemma that we expect you to prove! *)
  apply deadlock_freedom'. assumption.
Qed.
End Impl.

Module ImplCorrect : Pset11Sig.S := Impl.

(* Authors:
   Adam Chlipala,
   Peng Wang,
   Samuel Gruetter *)
