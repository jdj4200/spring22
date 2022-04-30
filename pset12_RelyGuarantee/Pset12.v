(** * 6.822 Formal Reasoning About Programs, Spring 2022 - Pset 12 *)

Require Import Frap Pset12Sig.

Module Impl.
(* Part 1: read Pset12Sig.v and answer the questions below. This task is
 * ungraded, but we are assigning it in hope it helps you complete the
 * following parts.

(these are duplicative with past psets:)

- Which syntactic construct can be used to implement sequencing of two commands?

Bind

- Which step rules allow a sequenced program to make progress?

StepBindProceed

- Which step rule is used when a loop terminates?

StepLoop

- Which step rule is used when a loop continues?

StepLoop

- Why is there no step rule for Fail?

Fail doesn't make progress

(these are about the programming language in this pset:)

- Which syntactic construct is used to spawn new threads?

Par : ||

- Which step rules allow a multi-threaded program to make progress?

StepPar1, StepPar2

- How can threads in this language communicate with each other?

Reads and Writes

- What do the steps that are factored out into the astep inductive have in common?

Atomic, across threads

(these are about the program logic:)

- Which rule of the program logic handles astep commands?

- What is the meaning of the "rely" argument [R]?

- What would [R] be for a program that can run in any environment?

- What would [R] be for a program that can only run alone?

- Which constructors of [hoare_triple] change [R]? Do they make it more or less permissive?

- What is the meaning of the "guarantee" argument [G]?

- Which cases of [hoare_triple] require you to prove [G]?

- What would [G] be for a program that can run in any environment?

- What would [G] be for a program that can only run alone?

(these are about program logic tactics:)

- What syntactic forms of commands does [step] handle?

- What syntactic forms of commands does [fork] handle?

- What are the six arguments to the tactic [fork]? Classify them into two groups of three, and then (differently) classify them into three pairs.

- What syntactic forms of commands does [atomic] handle?

- What is the argument to the tactic [atomic]?
*)

(* Part 2: prove a program *)

(* Pset12Example.v contains an example verification of a non-trivial program.
 * You can use it as a reference when trying to figure out what the rules,
 * lemmas, and tactics here do, but you are not required to understand it.
 * The program in this file is much simpler. *)

(* Verify that this program manages to increase the counter value. *)
Lemma ht_increment : forall init,
  hoare_triple
    (fun h => h $! 0 = init)
    (fun _ _ => False)
    (   (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
     || (tmp <- Atomic (Read 0); Atomic (Write 0 (tmp + 1)))
    )
    (fun _ _ => True)
    (fun _ h => h $! 0 > init).
Proof.
  simp.
  fork (fun h : heap => h $! 0 >= init)
       (fun h h' : heap => h = h' \/ h' $! 0 > init)
       (fun (_ : unit) (h : heap) => h $! 0 > init)
       (fun h : heap => h $! 0 >= init)
       (fun h h' : heap => h = h' \/ h' $! 0 > init)
       (fun (_ : unit) (h : heap) => h $! 0 > init); simp.
  step.
  atomic (fun (r : nat) (h : heap) => r >= init).
  apply HtAtomic; simp.
  step.
  atomic (fun (r : nat) (h : heap) => r >= init).
  apply HtAtomic; simp.
Qed.

(* Part 3: prove soundness of the program logic *)

(* Now it remains to prove that having a [hoare_triple] actually means
 * that execution will proceed safely, and if the program terminates then the
 * postcondition will be satisfied. *)

(* If non-negligible time has passed since you read the sig file, please
 * review the definitions of [trsys_of] and [notAboutToFail] now. *)

(* Then, feel free to just skim the next lemmas, right until the final
 * theorem you are asked to prove. *)

(* Here are a few more lemmas that you may find helpful: *)

Lemma HtStrengthen : forall {t : Set} P R c G (Q : t -> _) (P' : hprop),
    hoare_triple P R c G Q
    -> (forall h, P' h -> P h)
    -> stableP P' R
    -> hoare_triple P' R c G Q.
Proof. eauto. Qed.

Lemma HtWeakenFancy : forall {t : Set} P R c G Q (G' : hrel) (Q' : t -> hprop),
    hoare_triple P R c G Q
    -> (forall v h, Q v h -> Q' v h)
    -> (forall h h', G h h' -> G' h h')
    -> hoare_triple P R c G' Q'.
Proof. eauto using always_stableP. Qed.

Lemma HtReturn' : forall {t : Set} (P : hprop) (R G : hrel) (Q : _ -> hprop) (v : t),
    stableP P R
    -> (forall h, P h -> Q v h)
    -> hoare_triple P R (Return v) G Q.
Proof.
  simplify.
  eapply HtConsequence with (P' := P) (R' := R) (G' := G); eauto.
  simplify; propositional; subst; eauto.
Qed.

Lemma stableP_self : forall h R, stableP (fun h' => R^* h h') R.
Proof. simp. eauto using trc_trans. Qed.

Lemma stableP_star : forall R h h', R^* h h' ->
    forall P, stableP P R -> P h -> P h'.
Proof. induct 1; simplify; eauto. eapply IHtrc; eauto. Qed.

Lemma stableP_weakenR : forall P R, stableP P R -> forall R' : hrel,
    (forall h1 h2, R' h1 h2 -> R h1 h2) -> stableP P R'.
Proof. simp; eauto. Qed.

Local Hint Resolve stableP_self : core.

Lemma stable_stableQ : forall (t : Set) P (Q : t -> _) R r,
  stable P Q R -> stableP (Q r) R.
Proof. unfold stable; propositional; eauto. Qed.
Local Hint Resolve stable_stableQ : core.

Lemma stable_stableP : forall (t : Set) P (Q : t -> _) R,
  stable P Q R -> stableP P R.
Proof. unfold stable; propositional; eauto. Qed.
Local Hint Resolve stable_stableP : core.

Lemma trc_imply :forall t R (s s' : t), R^* s s' ->
  forall (R':_->_->Prop), (forall s s', R s s' -> R' s s') ->
  R'^* s s'.
Proof. induct 1; simplify; eauto. Qed.

Local Hint Extern 1 (_ >= _) => linear_arithmetic : core.
Local Hint Constructors notAboutToFail : core.

Lemma progress: forall (t : Set) (c : cmd t) P R G Q,
    hoare_triple P R c G Q ->
    forall h, P h -> notAboutToFail c.
Proof.
  induct 1; simp; eauto 6.
Qed.

Lemma ht_return: forall (t : Set) (r : t) P R G Q,
    hoare_triple P R (Return r) G Q ->
    forall h, P h -> Q r h.
Proof.
  induct 1; simp.
  eauto.
Qed.

Lemma HtStrengthenR : forall {t : Set} P R c G (Q : t -> _) (R': hrel),
    hoare_triple P R c G Q
    -> (forall h h', R' h h' -> R h h')
    -> hoare_triple P R' c G Q.
Proof.
  simp.
  eapply HtConsequence; eauto.
  apply always_stableP in H.
  apply stableP_weakenR with (R := R); assumption.
Qed.

Lemma guarantee :
  forall (t : Set) P (c : cmd t) R G Q,
    hoare_triple P R c G Q ->
    forall h,
      P h ->
      forall h' c',
        step (h, c) (h', c') ->
        G^* h h'.
Proof.
  induct 1; simp.
  -
    invert H3; simp.
    apply IHhoare_triple with (c' := c1'); assumption.
    constructor.
  -
    invert H5; simp.
    assert ((G1) ^* h h').
    apply IHhoare_triple1 with (c' := c1').
    apply H2; assumption.
    assumption.
    eapply trc_imply.
    apply H5.
    propositional.

    assert ((G2) ^* h h').
    apply IHhoare_triple2 with (c' := c2').
    apply H3; assumption.
    assumption.
    eapply trc_imply.
    apply H5.
    propositional.
  -
    invert H1.
  -
    invert H3; simp.
    constructor.
    eauto.
  -
    invert H3; simp.
    constructor.
  -
    apply trc_imply with (R := G).
    eauto.
    propositional.
Qed.

Lemma preservation: forall (t : Set) (c : cmd t) P R G Q,
    hoare_triple P R c G Q ->
    forall h, P h -> forall h' c',
        step (h, c) (h', c') ->
        hoare_triple (fun h'' => R^* h' h'') R c' G Q.
Proof.
  induct 1; simp.
  -
    invert H3; simp.
    apply IHhoare_triple in H6.
    econstructor.
    apply H6.
    assumption.
    assumption.

    specialize (H0 v0).
    apply HtStrengthen with (P' := P1) in H0.
    apply HtStrengthen with (P := P1).
    simp.
    simp.
    apply always_stableP in H.
    apply stableP_star with (R := R) (h := h'); assumption.
    apply stableP_self.
    apply ht_return with (R := R) (G := G); assumption.
    apply always_stableP in H.
    assumption.
  -
    invert H5; simp.
    apply IHhoare_triple1 in H8 as H9.
    econstructor; eauto; simp.
    apply trc_imply with (R := R).
    assumption.
    propositional.
                 
    apply always_stableP in H9.
    simp.
    apply H3 in H4 as H6.
    assert (G1 ^* h h').
    eapply guarantee.
    apply H.
    apply H2; assumption.
    apply H8.
    apply always_stableP in H0.
    apply stableP_weakenR with (R' := G1) in H0 as G.
    assert (P2 h').
    apply stableP_star with (R := G1) (h := h); assumption.
    apply stableP_weakenR with (R' := R) in H0 as R_.
    apply stableP_star with (R := R) (h := h'); assumption.
    propositional.
    propositional.
    apply H2; assumption.

    apply IHhoare_triple2 in H8 as H9.
    econstructor; eauto; simp.
    assert (G2 ^* h h').
    eapply guarantee.
    apply H0.
    apply H3; assumption.
    apply H8.
    apply always_stableP in H.
    apply stableP_weakenR with (R' := G2) in H as G.
    assert (P1 h').
    apply H2 in H4.
    apply stableP_star with (R := G2) (h := h); assumption.
    apply stableP_weakenR with (R' := R) in H as R_.
    apply stableP_star with (R := R) (h := h'); propositional.
    propositional.
    propositional.
    apply trc_imply with (R := R).
    assumption.
    propositional.
    apply H3; assumption.
  -
    invert H1.
  -
    invert H3; simp.
    apply HtReturn'.
    apply stableP_self.
    simp.
    assert (Q (h' $! a1) h').
    apply H0 with (h := h').
    assumption.
    constructor.
    apply stable_stableQ with (r := (h' $! a1)) in H1.
    eapply stableP_star with (R := R) (h := h'); assumption.
    
    apply HtReturn'.
    apply stableP_self.
    simp.
    assert (Q (tt) (h $+ (a1, v0))).
    apply H0 with (h := h).
    assumption.
    constructor.
    apply stable_stableQ with (r := tt) in H1.
    eapply stableP_star with (R := R) (h := (h $+ (a1, v0))); assumption.
  -
    invert H3; simp.
    econstructor.
    specialize (H init).
    apply HtStrengthen with (P := I (Again init)).
    apply H.
    simp.
    apply stableP_star with (R := R) (h := h').
    assumption.
    apply always_stableP in H.
    assumption.
    assumption.
    apply stableP_self.

    simp.
    cases r; simp.
    apply HtReturn'.
    specialize (H1 a).
    assumption.
    propositional.
    econstructor; assumption.
  -
    apply HtWeakenFancy with (G := G) (Q := Q).
    assert (hoare_triple (fun h'' : heap => (R) ^* h' h'') R c' G Q).
    apply IHhoare_triple with (h := h).
    apply H0; assumption.
    assumption.
    apply HtStrengthen with (P := (fun h'' : heap => (R) ^* h' h'')).
    apply HtStrengthenR with (R := R).
    assumption.
    assumption.
    simp.
    apply trc_imply with (R := R').
    assumption.
    propositional.
    apply stableP_self.
    assumption.
    assumption.
Qed.
    
(* HINT 1-6 (see Pset12Sig.v) *)   
Theorem hoare_triple_sound : forall (t : Set) P (c : cmd t) Q,
  hoare_triple P (fun _ _ => False) c (fun _ _ => True) Q ->
  forall h, P h ->
  invariantFor (trsys_of h c) (fun st => notAboutToFail (snd st)).
Proof.
  simp.
  apply invariant_weaken with (invariant1 :=
                                 (fun st=> exists h', (fun h'' : heap => (fun _ _ : heap => False) ^* h' h'') (fst st) /\ hoare_triple (fun h'' : heap => (fun _ _ : heap => False) ^* h' h'') (fun _ _ : heap => False) (snd st) (fun _ _ => True) Q)).
  apply invariant_induction; simp.
  exists h.
  propositional.
  constructor.
  eapply HtStrengthen.
  apply H.
  simp.
  apply always_stableP in H.
  eapply stableP_star; eauto.
  simp.
  cases s; cases s'; simp.
  eapply preservation with (c := c0)
                          (G := (fun _ _ : heap => True))
                          (Q := Q) (h := f) (h' := f0) (c' := c1) in H4.
  exists f0.
  propositional.
  constructor.
  assumption.
  assumption.

  simp.
  eapply progress; eauto.
Qed.
End Impl.

Module ImplCorrect : Pset12Sig.S := Impl.
