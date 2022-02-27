(** * Correctness of Binary Search Trees (BSTs) *)

(* This week we'll continue proving the correctness of a binary search tree implementation.
 * BSTs are a famous data structure for finite sets, allowing fast (log-time)
 * lookup, insertion, and deletion of items. (We omit the rebalancing heuristics
 * needed to achieve worst-case log-time operations, but you will prove the
 * correctness of rotation operations these heuristics use to modify the tree.)
 * In this problem set, we show that insertion and deletion functions are
 * correctly defined by relating them to operations on functional sets. *)

(* As usual, a set of spoiler-containing hints to help you along when you 
 * get stuck with certain pset questions has been provided at the bottom of 
 * the signature file! *)

Require Import Frap Datatypes Pset4Sig.
Require Import Compare_dec.

(* We will study binary trees of natural numbers only for convenience.
   Almost everything here would also work with an arbitrary type
   [t], but with [nat] you can use [linear_arithmetic] to prove
   goals about ordering of multiple elements (e.g., transitivity). *)
Local Notation t := nat.

Module Impl.
  (* Trees are an inductive structure, where [Leaf] doesn't have any items,
   * whereas [Node] has an item and two subtrees. Note that a [tree] can
   * contain nodes in arbitrary order, so not all [tree]s are valid binary
   * search trees. *)

  (* (* Imported from Sig file: *)
  Inductive tree :=
  | Leaf (* an empty tree *)
  | Node (d : t) (l r : tree).
  *)
  (* Then a singleton is just a node without subtrees. *)
  Definition Singleton (v: t) := Node v Leaf Leaf.

  (* [bst] relates a well-formed binary search tree to the set of elements it
     contains. Note that invalid trees with misordered elements are not valid
     representations of any set. All operations on a binary tree are specified
     in terms of how they affect the set that the tree represents. That
     set is encoded as function that takes a [t] and returns the proposition "[t]
     is in this set". *)
  Fixpoint bst (tr : tree) (s : t -> Prop) :=
    match tr with
    | Leaf => forall x, not (s x) (* s is empty set *)
    | Node d l r =>
        s d /\
        bst l (fun x => s x /\ x < d) /\
        bst r (fun x => s x /\ d < x)
    end.

  (* [member] computes whether [a] is in [tr], but to do so it *relies* on the
     [bst] property -- if [tr] is not a valid binary search tree, [member]
     will (and should, for performance) give arbitrarily incorrect answers. *)
  Fixpoint member (a: t) (tr: tree) : bool :=
    match tr with
    | Leaf => false
    | Node v lt rt =>
      match compare a v with
      | Lt => member a lt
      | Eq => true
      | Gt => member a rt
      end
    end.

  (* Here is a typical insertion routine for BSTs.
   * From a given value, we recursively compare the value with items in
   * the tree from the root, until we find a leaf whose place the new value can take. *)
  Fixpoint insert (a: t) (tr: tree) : tree :=
    match tr with
    | Leaf => Singleton a
    | Node v lt rt =>
      match compare a v with
      | Lt => Node v (insert a lt) rt
      | Eq => tr
      | Gt => Node v lt (insert a rt)
      end
    end.

  (* Helper functions for [delete] below. The *main task* in this pset
     is to understand, specify, and prove these helpers. *)

  (* [rightmost] finds the value of the rightmost node in [tr] or None if [tr] is a Leaf.
     This does not rely on the bst property; it works on any tree.*)
  Fixpoint rightmost (tr: tree) : option t :=
    match tr with
    | Leaf => None
    | Node v _ rt =>
      match rightmost rt with
      | None => Some v
      | r => r
      end
    end.

  (* A simple helper function that returns if [tr] is a Leaf node. *)
  Definition is_leaf (tr : tree) : bool :=
    match tr with Leaf => true | _ => false end.

  (* [delete_rightmost] deletes the rightmost node in [tr] or does nothing  if [tr] is a Leaf.
     This does not rely on the bst property; it works on any tree.*)
  Fixpoint delete_rightmost (tr: tree) : tree :=
    match tr with
    | Leaf => Leaf
    | Node v lt rt =>
      if is_leaf rt
      then lt
      else Node v lt (delete_rightmost rt)
    end.
  
  Definition merge_ordered lt rt :=
    match rightmost lt with
    | Some rv => Node rv (delete_rightmost lt) rt
    | None => rt
    end.

  (* [delete] searches for an element by its value and removes it if it is found.
     Removing an element from a leaf is degenerate (nothing to do), and
     removing the value from a node with no other children (both Leaf) can be done
     by replacing the node itself with a Leaf. Deleting a non-leaf node is
     substantially trickier because the type of [tree] does not allow for a Node
     with two subtrees but no value -- merging two trees is nontrivial. The
     implementation here removes the value anyway and then moves the rightmost
     node of the left subtree up to replace the removed value. This is equivalent
     to using rotations to move the value to be removed into leaf position and
     removing it there. *)
  Fixpoint delete (a: t) (tr: tree) : tree :=
    match tr with
    | Leaf => Leaf
    | Node v lt rt =>
      match compare a v with
      | Lt => Node v (delete a lt) rt
      | Eq => merge_ordered lt rt
      | Gt => Node v lt (delete a rt)
      end
    end.

  (* Here is a lemma that you will almost definitely want to use. *)
  Example bst_iff : forall tr P Q, bst tr P -> (forall x, P x <-> Q x) -> bst tr Q.
  Proof.
    induct tr; simplify.
    { rewrite <- H0. apply H with (x:=x). }
    rewrite H0 in H.
    propositional.
    { apply IHtr1 with (P:=(fun x : t => (fun d => P x /\ x < d) d));
        propositional; cycle 1.
      { rewrite H0; trivial. }
      { rewrite <-H0; trivial. } }
    { apply IHtr2 with (P:=(fun x : t => (fun d => P x /\ d < x) d));
      propositional; cycle 2.
      { rewrite <-H0; trivial. }
      { rewrite H0; trivial. } }
  Qed.

  (* You may want to call these tactics to use the previous lemma. *)
  (* They are just a means to save some typing of [apply ... with]. *)
  Ltac use_bst_iff known_bst :=
    lazymatch type of known_bst with
    | bst ?tree2 ?set2 =>
        lazymatch goal with
        | |- bst ?tree1 ?set1 =>
            apply bst_iff with (P:=set2) (Q := set1);
            lazymatch goal with
            |- bst tree2 set2 => apply known_bst
            | _ => idtac
            end
        end
    end.

  Ltac use_bst_iff_assumption :=
    match goal with
    | H : bst ?t _ |- bst ?t _ =>
      use_bst_iff H
    end.

  (* If you are comfortable with it, [eapply bst_iff] followed by careful
   * application of other [bst] facts (e.g., inductive hypotheses) can
   * save typing in some places where this tactic does not apply, though
   * keep in mind that forcing an incorrect choice for a ?unification
   * variable can make the goal false. *)

  (* It may also be useful to know that you can switch to proving [False] by
   * calling [exfalso]. This, for example, enables you to apply lemmas that end in
   * [-> False]. Of course, only do this if the hypotheses are contradictory. *)

  (* Other tactics used in our solution: apply, apply with, apply with in
   * (including multiple "with" clauses like in [use_bst_iff]), cases, propositional,
     linear_arithmetic, simplify, trivial, try, induct, equality, rewrite, assert. *)

  (* Warm-up exercise: rebalancing rotations *)

  (* Transcribe and prove one of the two rotations shown in [rotation1.svg] and [rotation2.svg].
     The AA-tree rebalancing algorithm applies these only if the annotations of relevant
     subtrees are in violation of a performance-critical invariant, but the rotations
     themselves are correct regardless. (These are straight from
     https://en.wikipedia.org/wiki/AA_tree#Balancing_rotations.) *)
  (* Each one can be written as a simple non-recursive definition
     containing two "match" expressions that returns the original
     tree in cases where the expected structure is not present. *)
  
  (* HINT 1 (see Pset4Sig.v) *)
  Definition rotate (T : tree) : tree :=
    match T with
    | Leaf => Leaf
    | Node v lt rt =>
        match lt with
        | Leaf => T
        | Node lv llt lrt => Node lv llt (Node v lrt rt)
        end
    end.

  Lemma bst_rotate T s (H : bst T s) : bst (rotate T) s.
  Proof.
    cases T; simplify.
    apply H.
    propositional.
    cases T1; simplify.
    propositional.
    split.
    apply H.
    split.
    apply bst_iff with (fun x : t => (s x /\ x < d) /\ x < d0).
    apply H.
    propositional.
    linear_arithmetic.
    propositional.
    apply bst_iff with (fun x : t => (s x /\ x < d) /\ d0 < x).
    apply H5.
    simplify.
    equality.
    apply bst_iff with (fun x : t => s x /\ d < x).
    assumption.
    simplify.
    propositional.
    linear_arithmetic.
  Qed.

  (* There is a hint in the signature file that completely gives away the proofs
   * of these rotations. We recommend you study that code after completing this
   * exercise to see how we did it, maybe picking up a trick or two to use below. *)

  Lemma bst_insert : forall tr s a, bst tr s ->
    bst (insert a tr) (fun x => s x \/ x = a).
  Proof.
    simplify.
    induct tr; simplify; propositional.
    apply H with x.
    assumption.
    contradict H0.
    linear_arithmetic.
    apply H with x.
    assumption.
    contradict H0.
    linear_arithmetic.

    cases (compare a d); simplify; propositional.
    apply bst_iff with (fun x : t => (s x /\ x < d) \/ x = a).
    apply IHtr1.
    assumption.
    propositional.
    linear_arithmetic.
    apply bst_iff with (fun x : t => s x /\ d < x).
    assumption.
    propositional.
    contradict H1.
    linear_arithmetic.
    apply bst_iff with (fun x : t => s x /\ x < d).
    assumption.
    propositional.
    equality.
    apply bst_iff with (fun x : t => s x /\ d < x).
    assumption.
    propositional.
    equality.
    apply bst_iff with (fun x : t => s x /\ x < d).
    assumption.
    propositional.
    contradict H1.
    linear_arithmetic.
    apply bst_iff with (fun x : t => (s x /\ d < x) \/ x = a).
    apply IHtr2.
    assumption.
    propositional.
    linear_arithmetic.
  Qed.

  (* To prove [bst_delete], you will need to write specifications for its helper
     functions, find suitable statements for proving correctness by induction, and use
     proofs of some helper functions in proofs of other helper functions. The hints
     in the signature file provide examples and guidance but no longer ready-to-prove
     lemma statements. For time-planning purposes: you are not halfway done yet.
     (The Sig file also has a rough point allocation between problems.)

     It is up to you whether to use one lemma per function, multiple lemmas per
     function, or (when applicable) one lemma per multiple functions. However,
     the lemmas you prove about one function need to specify everything a caller
     would need to know about this function. *)

  (*Lemma bst_if_member: forall tr s,
      (forall x, member x tr  = true <-> s x) <-> bst tr s.
  Proof.
    induct tr; simplify.
    propositional.
    assert (false = true <-> s x).
    apply H.
    propositional.
    equality.
    equality.
    assert (s x -> False).
    apply H.
    propositional.

    propositional.
    assert (match compare d d with
      | inleft (left _) => member d tr1
      | inleft (right _) => true
      | inright _ => member d tr2
      end = true <-> s d).
    apply H.
    cases (compare d d); simplify.
    linear_arithmetic.
    propositional.
    linear_arithmetic.
    apply IHtr1.
    intros.
    assert (match compare x d with
      | inleft (left _) => member x tr1
      | inleft (right _) => true
      | inright _ => member x tr2
            end = true <-> s x).
    apply H.
    cases (compare x d); simplify.
    propositional.
    propositional.
    propositional.*)

  Lemma bst_member: forall tr s d, bst tr s -> member d tr = true -> s d.
  Proof.
    induct tr; simplify.
    equality.

    propositional.
    
    cases (compare d0 d).

    assert (d0 < d \/ d0 = d \/ d0 > d).  
    apply Nat.lt_total.
    cases H2.

    assert (member d0 tr1 = true -> (fun x : t => s x /\ x < d) d0).
    apply IHtr1 with (s := (fun x : t => s x /\ x < d)).
    assumption.
    propositional.
    apply H5.
    propositional.
    equality.

    linear_arithmetic.
    equality.

    assert (member d0 tr2 = true -> (fun x : t => s x /\ d < x) d0).
    apply IHtr2 with (s := (fun x : t => s x /\ d < x)).
    assumption.
    propositional.
    apply H4.
  Qed.

  Lemma rightmost_member: forall tr s d, bst tr s ->
                                         rightmost tr = Some d -> member d tr = true.
  Proof.
    induct tr; simplify.
    equality.

    cases (compare d0 d); simplify.
    propositional.

    cases (rightmost tr2).

    assert (member d0 tr2 = true).
    apply IHtr2 with (fun x : t => s x /\ d < x).
    assumption.
    assumption.
    apply bst_member with (tr := tr2) (d := d0) (s := (fun x : t => s x /\ d < x)) in H2.
    propositional.
    linear_arithmetic.
    assumption.

    assert (d = d0) by equality.
    linear_arithmetic.
    equality.

    cases (rightmost tr2); simplify.
    propositional.
    apply IHtr2 with (fun x : t => s x /\ d < x).
    assumption.
    assumption.

    assert (d = d0) by equality.
    linear_arithmetic.
  Qed.

  Lemma rightmost_not_leaf: forall tr d, rightmost tr = Some d -> is_leaf tr = false.
  Proof.
    simplify.
    cases tr; simplify.
    equality.
    propositional.
  Qed.

  Lemma rightmost_leaf: forall tr, rightmost tr = None -> is_leaf tr = true.
  Proof.
    simplify.
    cases tr; simplify.
    equality.
    cases (rightmost tr2); simplify.
    equality.
    equality.
  Qed.

  Lemma rightmost_greatest: forall tr s n, bst tr s -> rightmost tr = Some n ->
                                           bst tr (fun x : t => s x /\ x <= n).
  Proof.
    induct tr; simplify.
    equality.
    propositional.
    cases (rightmost tr2); simplify.

    apply bst_member with (s:= (fun x : t => s x /\ d < x))(d := n) in H3.
    linear_arithmetic.
    apply rightmost_member with (s:= (fun x : t => s x /\ d < x)).
    assumption.
    rewrite H0 in Heq.
    assumption.

    assert (d = n) by equality.
    linear_arithmetic.

    cases (rightmost tr2); simplify.
    apply bst_iff with (P := (fun x : t => s x /\ x < d)).
    assumption.
    propositional.
    apply bst_member with (s:= (fun x : t => s x /\ d < x))(d := n) in H3.
    linear_arithmetic.
    apply rightmost_member with (s:= (fun x : t => s x /\ d < x)).
    assumption.
    rewrite H0 in Heq.
    assumption.

    assert (d = n) by equality.
    apply bst_iff with (P := (fun x : t => s x /\ x < d)).
    assumption.
    propositional.
    linear_arithmetic.

    cases (rightmost tr2); simplify.
    remember (fun x : t => s x /\ d < x).
    assert (bst tr2 (fun x : t => P x /\ x <= n)).
    apply IHtr2.
    assumption.
    assumption.
    apply bst_iff with (P := (fun x : t => P x /\ x <= n)).
    assumption.
    rewrite HeqP.
    propositional.

    cases tr2; simplify.
    propositional.
    apply H3 with x.
    propositional.

    cases (rightmost tr2_2); equality.
  Qed.

  Lemma bst_false: forall tr, bst tr (fun x : t => False) -> is_leaf tr = true.
  Proof.
    simplify.
    cases tr; simplify.
    equality.
    equality.
  Qed.
  
  Lemma bst_delete_rightmost: forall tr s d, bst tr s -> rightmost tr = Some d ->
                                   bst (delete_rightmost tr) (fun x : t => s x /\ x < d).
  Proof.
    induct tr; simplify.
    equality.

    propositional.
    cases (is_leaf tr2); simplify.
    
    cases (rightmost tr2); simplify.
    apply rightmost_not_leaf in Heq0.
    equality.

    assert (d = d0) by equality.
    subst.
    assumption.

    propositional.
    cases (rightmost tr2); simplify.
    apply rightmost_member with (s := (fun x : t => s x /\ d < x)) in Heq0.
    apply bst_member with (s := (fun x : t => s x /\ d < x)) in Heq0.
    assert (n = d0) by equality.
    linear_arithmetic.
    assumption.
    assumption.

    apply rightmost_leaf in Heq0.
    equality.

    cases (rightmost tr2); simplify.
    apply rightmost_member with (s := (fun x : t => s x /\ d < x)) in Heq0.
    apply bst_member with (s := (fun x : t => s x /\ d < x)) in Heq0.
    assert (n = d0) by equality.
    assert (d < d0) by linear_arithmetic.

    apply bst_iff with (P := (fun x : t => s x /\ x < d)).
    assumption.
    propositional.
    linear_arithmetic.
    assumption.
    assumption.

    assert (d = d0) by equality.
    apply bst_iff with (P := (fun x : t => s x /\ x < d)).
    assumption.
    propositional.
    linear_arithmetic.

    cases (rightmost tr2); simplify.
    remember (fun x : t => s x /\ d < x).
    assert (bst (delete_rightmost tr2) (fun x : t => P x /\ x < d0)).
    apply IHtr2.
    assumption.
    assumption.
    apply bst_iff with (P := (fun x : t => P x /\ x < d0)).
    assumption.
    propositional.
    rewrite HeqP in H5.
    propositional.
    rewrite HeqP in H5.
    propositional.
    rewrite HeqP.
    propositional.

    apply rightmost_leaf in Heq0.
    equality.
  Qed.

  Lemma bst_delete_rightmost': forall tr ltr rtr s d n,
      bst (delete_rightmost tr) (fun x : t => s x /\ x < d) ->
      rightmost tr = Some d -> tr = Node n ltr rtr -> bst tr s.
  Proof.
    induct tr; simplify.
    equality.

    cases (rightmost tr2); simplify.
    cases (is_leaf tr2); simplify.
    apply rightmost_not_leaf in Heq.
    equality.

    propositional.
    apply bst_iff with (P := (fun x : t => (s x /\ x < d0) /\ x < d)).
    assumption.
    propositional.
    linear_arithmetic.

    cases tr2.
    simplify.
    equality.
    
    apply IHtr2 with (d := d0) (ltr := tr2_1) (rtr := tr2_2) (n := d1).
    apply bst_iff with (P := (fun x : t => (s x /\ x < d0) /\ d < x)).
    assumption.
    propositional.
    assumption.
    equality.

    cases (is_leaf tr2); simplify.
    propositional.
Admitted.    
  
  Lemma merge_ordered_equiv_not_leaf: forall llt rlt rt d, is_leaf rlt = false ->
      rotate (merge_ordered (Node d llt rlt) rt) =
       Node d llt (merge_ordered rlt rt).
  Proof.
    simplify.
    unfold merge_ordered.
    simplify.

    cases (rightmost rlt); simplify.
    cases (is_leaf rlt); simplify.
    apply rightmost_not_leaf in Heq.
    equality.
    equality.

    cases (is_leaf rlt); simplify.
    cases llt; simplify.
    equality.
    equality.
    apply rightmost_leaf in Heq.
    equality.
  Qed.

  Lemma merge_ordered_equiv_leaf: forall llt rt d,
                merge_ordered (Node d llt Leaf) rt = Node d llt (merge_ordered Leaf  rt).
  Proof.
    simplify.
    unfold merge_ordered.
    simplify.
    equality.
  Qed.

  Lemma rightmost_singleton: forall tr n, rightmost tr = Some n
                                          -> delete_rightmost tr = Leaf -> tr = Node n Leaf Leaf.
  Proof.
    simplify.
    cases tr; simplify.
    equality.
    cases (rightmost tr2); simplify.
    cases (is_leaf tr2); simplify.
    apply rightmost_not_leaf in Heq.
    equality.
    equality.
    cases (is_leaf tr2); simplify.
    cases tr2; simplify; equality.
    apply rightmost_leaf in Heq.
    equality.
  Qed.
  
  Lemma bst_merge_ordered_leaf: forall tr s, bst (merge_ordered tr Leaf) s -> bst tr s.
  Proof.
    induct tr; simplify.
    apply H.
    propositional.
    unfold merge_ordered in H.
    cases (rightmost (Node d tr1 tr2)); simplify.
    cases (rightmost tr2); simplify.
    cases (is_leaf tr2); simplify.
    apply rightmost_not_leaf in Heq0 as H1.
    equality.
    propositional.
    assert (n = d) by equality.
    subst.
    apply H.
    cases (rightmost tr2); simplify; equality.

    unfold merge_ordered in H.
    cases (rightmost (Node d tr1 tr2)); simplify.
    cases (rightmost tr2); simplify.
    cases (is_leaf tr2); simplify.
    apply rightmost_not_leaf in Heq0 as H1.
    equality.
    propositional.
    apply bst_iff with (P := (fun x : t => (s x /\ x < n) /\ x < d)).
    assumption.
    propositional.
    linear_arithmetic.
    cases (is_leaf tr2); simplify.
    propositional.
    apply bst_iff with (P := (fun x : t => s x /\ x < n)).
    assumption.
    propositional.
    assert (n = d) by equality.
    subst.
    assumption.
    assert (n = d) by equality.
    subst.
    assumption.
    propositional.
    apply bst_iff with (P := (fun x : t => (s x /\ x < n) /\ x < d)).
    assumption.
    propositional.
    linear_arithmetic.
    cases (rightmost tr2); simplify; equality.

    unfold merge_ordered in H.
    cases (rightmost (Node d tr1 tr2)); simplify.
    cases (rightmost tr2); simplify.
    cases (is_leaf tr2); simplify.
    apply rightmost_not_leaf in Heq0 as H1.
    equality.
    propositional.
    
    cases (delete_rightmost).
    simplify.
    assert ( tr2 = Node n Leaf Leaf).
    apply rightmost_singleton.
    equality.
    assumption.
    subst.
    simplify.
    propositional.
    apply H5 with x.
    propositional.
    apply H2 with x.
    propositional.
    cases tr2; simplify.
    equality.
    propositional.

    propositional.

    (* Focus 2.
    cases (is_leaf tr2); simplify.
    propositional.
    cases tr2; simplify.
    assert (d = n) by equality.
    subst.
    propositional.
    apply H2 with x.
    propositional.
    equality.

    apply rightmost_leaf in Heq0.
    equality.

    Focus 2.
    cases (rightmost tr2); simplify; equality. *)
      
   (* apply bst_iff with (P := (fun x : t => (s x /\ x < n) /\ x < d)).
    assumption.
    propositional.
    linear_arithmetic.
    cases (is_leaf tr2); simplify.
    propositional.
    apply bst_iff with (P := (fun x : t => s x /\ x < n)).
    assumption.
    propositional.
    assert (n = d) by equality.
    subst.
    assumption.
    assert (n = d) by equality.
    subst.
    assumption.
    propositional.
    apply bst_iff with (P := (fun x : t => (s x /\ x < n) /\ x < d)).
    assumption.
    propositional.
    linear_arithmetic.
    cases (rightmost tr2); simplify; equality.*)

  Admitted.
  
    
 (* Lemma bst_merge_ordered: forall lt rt s d, bst lt (fun x : t => s x /\ x < d) ->
                                             bst rt (fun x : t => s x /\ d < x) ->
                             bst (merge_ordered lt rt) (fun x : t => s x /\ x <> d).
  Proof.
    simplify.
    induct lt; simplify.
    unfold merge_ordered.
    simplify.
    apply bst_iff with (fun x : t => s x /\ d < x).
    assumption.
    simplify.
    assert (~ (s x /\ x < d)).
    apply H.
    propositional.
    linear_arithmetic.
    assert (x < d \/ x = d \/ x > d).  
    apply Nat.lt_total.
    propositional.

    propositional.
    apply bst_iff with (Q := (fun x : t => (s x /\ d < x) /\ x < d0)) in H4.
    assert (bst (merge_ordered lt2 rt) (fun x : t => (s x /\ d < x) /\ (x = d0 -> False))).
    apply IHlt2.
    assumption.
    apply bst_iff with (P := (fun x : t => s x /\ d0 < x)).
    assumption.
    propositional.
    linear_arithmetic.

    apply bst_iff with (Q := (fun x : t => (s x /\ x < d) /\ x < d0)) in H1.
    assert (bst (merge_ordered lt1 Leaf)
                (fun x : t => (s x /\ x < d) /\ (x = d0 -> False))).
    apply IHlt1.
    assumption.
    unfold bst.
    propositional.
    linear_arithmetic.
    

   (* cases lt2.
    
    assert bst (Node d lt1 merge_ordered Leaf
    
    rewrite merge_ordered_equiv_leaf in H2.
    





    
    unfold merge_ordered.
    simplify.
    cases (rightmost lt2); simplify.
    propositional.
    apply rightmost_member with (s:= (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    apply bst_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    propositional.
    assumption.
    assumption.

    apply rightmost_member with (s:= (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    apply bst_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    propositional.
    linear_arithmetic.
    assumption.
    assumption.

    cases (is_leaf lt2); simplify.
    apply rightmost_not_leaf in Heq.
    equality.

    propositional.
    linear_arithmetic.
    apply rightmost_member with (s:= (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    apply bst_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    propositional.
    assumption.
    assumption.

    apply bst_iff with (P := (fun x : t => (s x /\ x < d0) /\ x < d)).
    assumption.
    propositional.
    linear_arithmetic.
    apply rightmost_member with (s:= (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    apply bst_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    propositional.
    linear_arithmetic.
    assumption.
    assumption.
    linear_arithmetic.

    apply bst_delete_rightmost with (d := n) in H4 as H5.
    apply bst_iff with (P := (fun x : t => ((s x /\ x < d0) /\ d < x) /\ x < n)).
    assumption.
    propositional.
    linear_arithmetic.
    apply rightmost_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    apply bst_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    propositional.
    linear_arithmetic.
    assumption.
    assumption.
    assumption.

    apply rightmost_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    apply bst_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    propositional.
    Search and.

    apply bst_iff with (P := (fun x : t => s x /\ d0 < x)).
    assumption.
    propositional.
    linear_arithmetic.
    linear_arithmetic.*)
  *)

  Lemma rightmost_none: forall tr s n, bst tr s -> rightmost tr = Some n -> (forall x, ~ (s x /\ x > n)).
  Proof.
    induct tr; simplify.
    equality.
    cases (rightmost tr2); simplify.
    propositional.
    assert (n0 = n) by equality.
    subst.
    apply rightmost_member with (s := (fun x : t => s x /\ d < x)) in Heq.
    apply bst_member with (s := (fun x : t => s x /\ d < x)) in Heq.
    apply IHtr2 with (s := (fun x : t => s x /\ d < x)) (n := n) (x := x).
    assumption.
    assumption.
    propositional.
    linear_arithmetic.
    assumption.
    assumption.

    propositional.
    cases tr2.
    simplify.
    assert (n = d) by equality.
    subst.
    apply H5 with x.
    propositional.

    assert (is_leaf (Node d0 tr2_1 tr2_2) = false) by equality.
    apply rightmost_leaf in Heq.
    equality.
  Qed.
  
  Lemma bst_merge_ordered: forall lt rt s d, bst lt (fun x : t => s x /\ x < d) ->
                                             bst rt (fun x : t => s x /\ d < x) ->
                             bst (merge_ordered lt rt) (fun x : t => s x /\ x <> d).
  Proof.
    simplify.
    induct lt; simplify.
    unfold merge_ordered.
    simplify.
    apply bst_iff with (fun x : t => s x /\ d < x).
    assumption.
    simplify.
    assert (~ (s x /\ x < d)).
    apply H.
    propositional.
    linear_arithmetic.
    assert (x < d \/ x = d \/ x > d).  
    apply Nat.lt_total.
    propositional.

    propositional.
    unfold merge_ordered.
    simplify.
    cases (rightmost lt2); simplify.
    propositional.
    apply rightmost_member with (s:= (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    apply bst_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    propositional.
    assumption.
    assumption.

    apply rightmost_member with (s:= (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    apply bst_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    propositional.
    linear_arithmetic.
    assumption.
    assumption.

    cases (is_leaf lt2); simplify.
    apply rightmost_not_leaf in Heq.
    equality.

    propositional.
    linear_arithmetic.
    apply rightmost_member with (s:= (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    apply bst_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    propositional.
    assumption.
    assumption.

    apply bst_iff with (P := (fun x : t => (s x /\ x < d0) /\ x < d)).
    assumption.
    propositional.
    linear_arithmetic.
    apply rightmost_member with (s:= (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    apply bst_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    propositional.
    linear_arithmetic.
    assumption.
    assumption.
    linear_arithmetic.

    apply bst_delete_rightmost with (d := n) in H4 as H5.
    apply bst_iff with (P := (fun x : t => ((s x /\ x < d0) /\ d < x) /\ x < n)).
    assumption.
    propositional.
    linear_arithmetic.
    apply rightmost_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    apply bst_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq.
    propositional.
    linear_arithmetic.
    assumption.
    assumption.
    assumption.

    apply rightmost_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x))
      in Heq as Heq1.
    apply bst_member with (s := (fun x : t => (s x /\ x < d0) /\ d < x)) in Heq1.
    propositional.

    apply bst_iff with (P := (fun x : t => s x /\ d0 < x)).
    assumption.
    propositional.
    linear_arithmetic.
    linear_arithmetic.

    apply rightmost_none with (s:= (fun x : t => (s x /\ x < d0) /\ d < x)) (x := x) in Heq.
    propositional.
    linear_arithmetic.
    assumption.
    assumption.
    assumption.

    propositional.
    linear_arithmetic.
    cases (is_leaf lt2); simplify.
    apply bst_iff with (P := (fun x : t => (s x /\ x < d0) /\ x < d)).
    assumption.
    propositional.
    linear_arithmetic.
    linear_arithmetic.

    apply rightmost_leaf in Heq.
    equality.

    cases lt2.
    simplify.
    propositional.
    apply bst_iff with (P := (fun x : t => s x /\ d0 < x)).
    assumption.
    propositional.
    linear_arithmetic.
    linear_arithmetic.
    assert ((s x /\ x < d0) /\ d < x -> False).
    apply H4.
    propositional.
    linear_arithmetic.
    apply rightmost_leaf in Heq.
    assert (is_leaf (Node d1 lt2_1 lt2_2) = false) by equality.
    equality.
  Qed.
  
  (* HINT 2-5 (see Pset4Sig.v) *)
  Lemma bst_delete : forall tr s a, bst tr s ->
    bst (delete a tr) (fun x => s x /\ x <> a).
  Proof.
    induct tr; simplify.
    propositional.
    apply H with x.
    assumption.

    propositional.
    cases (compare a d); simplify; propositional.
    linear_arithmetic.

    apply bst_iff with (fun x : t => ((s x /\ x < d) /\ (x = a -> False))).
    apply IHtr1 with (a := a) ( s := (fun x : t => s x /\ x < d)).
    assumption.
    propositional.

    apply bst_iff with (fun x : t => (s x /\ d < x)).
    assumption.
    propositional.
    linear_arithmetic.
    subst.

    apply bst_merge_ordered.
    assumption.
    assumption.

    linear_arithmetic.

    apply bst_iff with (fun x : t => (s x /\ x < d)).
    assumption.
    propositional.
    linear_arithmetic.

    apply bst_iff with (fun x : t => ((s x /\ d < x) /\ (x = a -> False))).
    apply IHtr2 with (a := a) ( s := (fun x : t => s x /\ d < x)).
    assumption.
    propositional.
  Qed.

  (* Great job! Now you have proven all tree-structure-manipulating operations
     necessary to implement a balanced binary search tree. Rebalancing heuristics
     that achieve worst-case-logarithmic running time maintain annotations on
     nodes of the tree (and decide to rebalance based on these). The implementation
     here omits them, but as the rotation operations are correct regardless of
     the annotations, any way of calling them from heuristic code would result in a
     functionally correct binary tree. *)
End Impl.

Module ImplCorrect : Pset4Sig.S := Impl.

(* Authors:
 * Joonwon Choi
 * Adam Chlipala
 * Benjamin Sherman
 * Andres Erbsen
 * Amanda Liu
 *)
