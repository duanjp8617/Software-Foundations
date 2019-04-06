(** * IndProp: Inductively Defined Propositions *)

(* Set Warnings "-notation-overridden,-parsing". *)
From LF Require Export Logic.
Require Coq.omega.Omega.

(* ################################################################# *)
(** * Inductively Defined Propositions *)

(** In the [Logic] chapter, we looked at several ways of writing
    propositions, including conjunction, disjunction, and existential
    quantification.  In this chapter, we bring yet another new tool
    into the mix: _inductive definitions_. *)

(** In past chapters, we have seen two ways of stating that a number
    [n] is even: We can say

      (1) [evenb n = true], or

      (2) [exists k, n = double k].

    Yet another possibility is to say that [n] is even if we can
    establish its evenness from the following rules:

       - Rule [ev_0]: The number [0] is even.
       - Rule [ev_SS]: If [n] is even, then [S (S n)] is even. *)

(** To illustrate how this new definition of evenness works,
    let's imagine using it to show that [4] is even. By rule [ev_SS],
    it suffices to show that [2] is even. This, in turn, is again
    guaranteed by rule [ev_SS], as long as we can show that [0] is
    even. But this last fact follows directly from the [ev_0] rule. *)

(** We will see many definitions like this one during the rest
    of the course.  For purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: 

                              ------------             (ev_0)
                                 even 0

                                 even n
                            ----------------          (ev_SS)
                             even (S (S n))
*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [ev_SS] says that, if [n]
    satisfies [even], then [S (S n)] also does.  If a rule has no
    premises above the line, then its conclusion holds
    unconditionally.

    We can represent a proof using these rules by combining rule
    applications into a _proof tree_. Here's how we might transcribe
    the above proof that [4] is even: 

                             --------  (ev_0)
                              even 0
                             -------- (ev_SS)
                              even 2
                             -------- (ev_SS)
                              even 4
*)

(** (Why call this a "tree" (rather than a "stack", for example)?
    Because, in general, inference rules can have multiple premises.
    We will see examples of this shortly. *)

(* ================================================================= *)
(** ** Inductive Definition of Evenness *)

(** Putting all of this together, we can translate the definition of
    evenness into a formal Coq definition using an [Inductive]
    declaration, where each constructor corresponds to an inference
    rule: *)

Inductive even : nat -> Prop :=
| ev_0 : even 0
| ev_SS (n : nat) (H : even n) : even (S (S n)).

(** This definition is different in one crucial respect from previous
    uses of [Inductive]: the thing we are defining is not a [Type],
    but rather a function from [nat] to [Prop] -- that is, a property
    of numbers.  We've already seen other inductive definitions that
    result in functions -- for example, [list], whose type is [Type ->
    Type].  What is really new here is that, because the [nat]
    argument of [even] appears to the _right_ of the colon, it is
    allowed to take different values in the types of different
    constructors: [0] in the type of [ev_0] and [S (S n)] in the type
    of [ev_SS].

    In contrast, the definition of [list] names the [X] parameter
    _globally_, to the _left_ of the colon, forcing the result of
    [nil] and [cons] to be the same ([list X]).  Had we tried to bring
    [nat] to the left in defining [even], we would have seen an
    error: *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS : wrong_ev n -> wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]"
        as 1st argument in "[wrong_ev 0]". *)

(** In an [Inductive] definition, an argument to the type
    constructor on the left of the colon is called a "parameter",
    whereas an argument on the right is called an "index".

    For example, in [Inductive list (X : Type) := ...], [X] is a
    parameter; in [Inductive even : nat -> Prop := ...], the
    unnamed [nat] argument is an index. *)

(** We can think of the definition of [even] as defining a Coq
    property [even : nat -> Prop], together with primitive theorems
    [ev_0 : even 0] and [ev_SS : forall n, even n -> even (S (S n))]. *)

(** That definition can also be written as follows...

  Inductive even : nat -> Prop :=
  | ev_0 : even 0
  | ev_SS : forall n, even n -> even (S (S n)).
*)

(** ... making explicit the type of the rule [ev_SS]. *)

(** Such "constructor theorems" have the same status as proven
    theorems.  In particular, we can use Coq's [apply] tactic with the
    rule names to prove [even] for particular numbers... *)

Theorem ev_4 : even 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ... or we can use function application syntax: *)

Theorem ev_4' : even 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** We can also prove theorems that have hypotheses involving [even]. *)

Theorem ev_plus4 : forall n, even n -> even (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** **** Exercise: 1 star, standard (ev_double)  *)
Theorem ev_double : forall n,
  even (double n).
Proof.
  intros.
  induction n as [|n' IHn'].
  -
    simpl. apply ev_0.
  -
    simpl.
    apply ev_SS.
    apply IHn'.
Qed.

(** [] *)

(* ################################################################# *)
(** * Using Evidence in Proofs *)

(** Besides _constructing_ evidence that numbers are even, we can also
    _reason about_ such evidence.

    Introducing [even] with an [Inductive] declaration tells Coq not
    only that the constructors [ev_0] and [ev_SS] are valid ways to
    build evidence that some number is even, but also that these two
    constructors are the _only_ ways to build evidence that numbers
    are even (in the sense of [even]). *)

(** In other words, if someone gives us evidence [E] for the assertion
    [even n], then we know that [E] must have one of two shapes:

      - [E] is [ev_0] (and [n] is [O]), or
      - [E] is [ev_SS n' E'] (and [n] is [S (S n')], where [E'] is
        evidence for [even n']). *)

(** This suggests that it should be possible to analyze a
    hypothesis of the form [even n] much as we do inductively defined
    data structures; in particular, it should be possible to argue by
    _induction_ and _case analysis_ on such evidence.  Let's look at a
    few examples to see what this means in practice. *)

(* ================================================================= *)
(** ** Inversion on Evidence *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [even n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence that [even n] _directly_. As
    a tool, we can prove our characterization of evidence for
    [even n], using [destruct]. *)

Theorem ev_inversion :
  forall (n : nat), even n ->
    (n = 0) \/ (exists n', n = S (S n') /\ even n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - (* E = ev_0 : even 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : even (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** The following theorem can easily be proved using [destruct] on
    evidence. *)

Theorem ev_minus2 : forall n,
  even n -> even (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** However, this variation cannot easily be handled with [destruct]. *)

Theorem evSS_ev : forall n,
  even (S (S n)) -> even n.
(** Intuitively, we know that evidence for the hypothesis cannot
    consist just of the [ev_0] constructor, since [O] and [S] are
    different constructors of the type [nat]; hence, [ev_SS] is the
    only case that applies.  Unfortunately, [destruct] is not smart
    enough to realize this, and it still generates two subgoals.  Even
    worse, in doing so, it keeps the final goal unchanged, failing to
    provide any useful information for completing the proof.  *)
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0. *)
    (* We must prove that [n] is even from no assumptions! *)
Abort.

(** What happened, exactly?  Calling [destruct] has the effect of
    replacing all occurrences of the property argument by the values
    that correspond to each constructor.  This is enough in the case
    of [ev_minus2] because that argument [n] is mentioned directly
    in the final goal. However, it doesn't help in the case of
    [evSS_ev] since the term that gets replaced ([S (S n)]) is not
    mentioned anywhere. *)

(** We could patch this proof by replacing the goal [even n],
    which does not mention the replaced term [S (S n)], by the
    equivalent goal [even (pred (pred (S (S n))))], which does mention
    this term, after which [destruct] can make progress. But it is
    more straightforward to use our inversion lemma. *)

Theorem evSS_ev : forall n, even (S (S n)) -> even n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm.
   intro Heq. rewrite Heq. apply Hev.
Qed.

(** Coq provides a tactic called [inversion], which does the work of
    our inversion lemma and more besides. *)

(** The [inversion] tactic can detect (1) that the first case
    ([n = 0]) does not apply and (2) that the [n'] that appears in the
    [ev_SS] case must be the same as [n].  It has an "[as]" variant
    similar to [destruct], allowing us to assign names rather than
    have Coq choose them. *)

Theorem evSS_ev' : forall n,
  even (S (S n)) -> even n.
Proof.
  intros n E.
  inversion E as [| n' E'].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductive
    properties, something that takes a bit more work using our
    inversion lemma. For example: *)
Theorem one_not_even : ~ even 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ even 1.
  intros H. inversion H. Qed.

(** **** Exercise: 1 star, standard (inversion_practice)  

    Prove the following result using [inversion].  For extra practice,
    prove it using the inversion lemma. *)

Theorem SSSSev__even : forall n,
  even (S (S (S (S n)))) -> even n.
Proof.
  intros.
  inversion H.
  inversion H1.
  apply H3.
Qed.

  
(** [] *)

(** **** Exercise: 1 star, standard (even5_nonsense)  

    Prove the following result using [inversion]. *)

Theorem even5_nonsense :
  even 5 -> 2 + 2 = 9.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H3.
Qed.

(** [] *)

(** The [inversion] tactic does quite a bit of work. When
    applied to equalities, as a special case, it does the work of both
    [discriminate] and [injection]. In addition, it carries out the
    [intros] and [rewrite]s that are typically necessary in the case
    of [injection]. It can also be applied, more generally, to analyze
    evidence for inductively defined propositions.  As examples, we'll
    use it to reprove some theorems from [Tactics.v]. *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** Here's how [inversion] works in general.  Suppose the name
    [H] refers to an assumption [P] in the current context, where [P]
    has been defined by an [Inductive] declaration.  Then, for each of
    the constructors of [P], [inversion H] generates a subgoal in which
    [H] has been replaced by the exact, specific conditions under
    which this constructor could have been used to prove [P].  Some of
    these subgoals will be self-contradictory; [inversion] throws
    these away.  The ones that are left represent the cases that must
    be proved to establish the original goal.  For those, [inversion]
    adds all equations into the proof context that must hold of the
    arguments given to [P] (e.g., [S (S n') = n] in the proof of
    [evSS_ev]). *)

(** The [ev_double] exercise above shows that our new notion of
    evenness is implied by the two earlier ones (since, by
    [even_bool_prop] in chapter [Logic], we already know that
    those are equivalent to each other). To show that all three
    coincide, we just need the following lemma. *)

Lemma ev_even_firsttry : forall n,
  even n -> exists k, n = double k.
Proof.
(* WORKED IN CLASS *)

(** We could try to proceed by case analysis or induction on [n].  But
    since [even] is mentioned in a premise, this strategy would
    probably lead to a dead end, as in the previous section.  Thus, it
    seems better to first try [inversion] on the evidence for [even].
    Indeed, the first case can be solved trivially. *)

  intros n E. inversion E as [| n' E'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.

(** Unfortunately, the second case is harder.  We need to show [exists
    k, S (S n') = double k], but the only available assumption is
    [E'], which states that [even n'] holds.  Since this isn't
    directly useful, it seems that we are stuck and that performing
    case analysis on [E] was a waste of time.

    If we look more closely at our second goal, however, we can see
    that something interesting happened: By performing case analysis
    on [E], we were able to reduce the original result to a similar
    one that involves a _different_ piece of evidence for [even]:
    namely [E'].  More formally, we can finish our proof by showing
    that

        exists k', n' = double k',

    which is the same as the original statement, but with [n'] instead
    of [n].  Indeed, it is not difficult to convince Coq that this
    intermediate result suffices. *)

    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I. (* reduce the original goal to the new one *)

Abort.

(* ================================================================= *)
(** ** Induction on Evidence *)

(** If this looks familiar, it is no coincidence: We've
    encountered similar problems in the [Induction] chapter, when
    trying to use case analysis to prove results that required
    induction.  And once again the solution is... induction!

    The behavior of [induction] on evidence is the same as its
    behavior on data: It causes Coq to generate one subgoal for each
    constructor that could have used to build that evidence, while
    providing an induction hypotheses for each recursive occurrence of
    the property in question.

    To prove a property of [n] holds for all numbers for which [even
    n] holds, we can use induction on [even n]. This requires us to
    prove two things, corresponding to the two ways in which [even n]
    could have been constructed. If it was constructed by [ev_0], then
    [n=0], and the property must hold of [0]. If it was constructed by
    [ev_SS], then the evidence of [even n] is of the form [ev_SS n'
    E'], where [n = S (S n')] and [E'] is evidence for [even n']. In
    this case, the inductive hypothesis says that the property we are
    trying to prove holds for [n']. *)

(** Let's try our current lemma again: *)

Lemma ev_even : forall n,
  even n -> exists k, n = double k.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       with IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

(** Here, we can see that Coq produced an [IH] that corresponds
    to [E'], the single recursive occurrence of [even] in its own
    definition.  Since [E'] mentions [n'], the induction hypothesis
    talks about [n'], as opposed to [n] or some other number. *)

(** The equivalence between the second and third definitions of
    evenness now follows. *)

Theorem ev_even_iff : forall n,
  even n <-> exists k, n = double k.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** As we will see in later chapters, induction on evidence is a
    recurring technique across many areas, and in particular when
    formalizing the semantics of programming languages, where many
    properties of interest are defined inductively. *)

(** The following exercises provide simple examples of this
    technique, to help you familiarize yourself with it. *)

(** **** Exercise: 2 stars, standard (ev_sum)  *)
Theorem ev_sum : forall n m, even n -> even m -> even (n + m).
Proof.
  intros n m H.
  generalize dependent m.
  induction H as [| n' E' IH].
  -
    intros. simpl. apply H.
  -
    intros.
    simpl.
    apply ev_SS.
    apply IH in H.
    apply H.
Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced, optional (even'_ev)  

    In general, there may be multiple ways of defining a
    property inductively.  For example, here's a (slightly contrived)
    alternative definition for [even]: *)

Inductive even' : nat -> Prop :=
| even'_0 : even' 0
| even'_2 : even' 2
| even'_sum n m (Hn : even' n) (Hm : even' m) : even' (n + m).

(** Prove that this definition is logically equivalent to the old
    one.  (You may want to look at the previous theorem when you get
    to the induction step.) *)

Theorem even'_ev : forall n, even' n <-> even n.
Proof.
  split.
  -
    intros.
    induction H as [].
    +
      apply ev_0.
    +
      apply ev_SS. apply ev_0.
    +
      apply ev_sum.
      *
        apply IHeven'1.
      *
        apply IHeven'2.
  -
    intros.
    induction H as [| n' E' IH].
    +
      apply even'_0.
    +
      apply (even'_sum 2 n' even'_2 IH).
Qed.  
    
(** [] *)

(** **** Exercise: 3 stars, advanced, recommended (ev_ev__ev)  

    Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  even (n+m) -> even n -> even m.
Proof.
  intros.
  induction H0 as [| n' E IH].
  -
    simpl in H. apply H.
  -
    apply IH.
    simpl in H.
    inversion H.
    apply H1.
Qed.

      
(** [] *)

(** **** Exercise: 3 stars, standard, optional (ev_plus_plus)  

    This exercise just requires applying existing lemmas.  No
    induction or even case analysis is needed, though some of the
    rewriting may be tedious. *)

Lemma ev_plus_plus_helper: forall n:nat,
    n + n = double n.
Proof.
  induction n as [| n' IHn'].
  -
    reflexivity.
  -
    simpl.
    rewrite -> plus_comm.
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem ev_plus_plus : forall n m p,
  even (n+m) -> even (n+p) -> even (m+p).
Proof.
  intros.
  apply (ev_sum (n+m) (n+p) H) in H0.
  rewrite -> plus_assoc in H0.
  assert (H': n + m + n = double n + m).
  {
    rewrite <- plus_comm.
    rewrite -> plus_assoc.
    rewrite -> ev_plus_plus_helper.
    reflexivity.
  }
  rewrite H' in H0.
  rewrite <- plus_assoc in H0.
  apply (ev_ev__ev (double n) (m+p)) in H0.
  -
    apply H0.
  -
    apply ev_double.
Qed.

  (** [] *)

(* ################################################################# *)
(** * Inductive Relations *)

(** A proposition parameterized by a number (such as [even])
    can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module Playground.

(** One useful example is the "less than or equal to" relation on
    numbers. *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n n : le n n
  | le_S n m (H : le n m) : le n (S m). (* forall n m, le n m -> le n (S m) *)

Notation "m <= n" := (le m n).

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [even] above. We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [(2 <= 1) ->
    2+2=5].) *)

(** Here are some sanity checks on the definition.  (Notice that,
    although these are the same kind of simple "unit tests" as we gave
    for the testing functions we wrote in the first few lectures, we
    must construct their proofs explicitly -- [simpl] and
    [reflexivity] don't do the job, because the proofs aren't just a
    matter of simplifying computations.) *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* WORKED IN CLASS *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* WORKED IN CLASS *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H2.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
  | ne_1 n (H: even (S n)) : next_even n (S n)
  | ne_2 n (H : even n) : next_even n (S (S n)).

(** **** Exercise: 2 stars, standard, optional (total_relation)  

    Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat -> Prop:=
  | tr : forall n m, total_relation n m.

(* FILL IN HERE 

    [] *)

(** **** Exercise: 2 stars, standard, optional (empty_relation)  

    Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)

Inductive empty_relation : nat -> nat -> Prop:=
  | er : forall n m, empty_relation n m.

(* FILL IN HERE 

    [] *)

(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n']. 
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** **** Exercise: 3 stars, standard, optional (le_exercises)  

    Here are a number of facts about the [<=] and [<] relations that
    we are going to need later in the course.  The proofs make good
    practice exercises. *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2.
  induction H2 as [].
  -
    apply H1.
  -
    apply (le_S) in IHle.
    apply IHle.
Qed.
  
Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n as [|n' IHn'].
  -
    apply (le_n 0).
  -
    apply (le_S 0 n').
    apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros.
  induction H.
  -
    apply le_n.
  -
    apply le_S.
    apply IHle.
Qed.


Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros.
  inversion H.
  -
    apply le_n.
  -
    assert (H2: n <= S n).
    {
      apply le_S. apply le_n.
    }
    apply (le_trans _ _ _ H2) in H1.
    apply H1.
Qed.


Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros.
  induction b as [|b' IHb'].
  -
    rewrite -> plus_comm. simpl.
    apply le_n.
  -
    rewrite -> plus_comm. simpl.
    apply le_S. rewrite -> plus_comm. apply IHb'.
Qed.


Lemma plus_lt_helper: forall n m,
    S (n + m) = S n + m.
Proof.
  intros.
  destruct m.
  -
    rewrite -> plus_comm.
    simpl.
    rewrite -> plus_comm.
    simpl.
    reflexivity.
  -
    rewrite -> plus_comm.
    simpl.
    assert(H: n + S m = S m + n).
    {
      rewrite -> plus_comm. reflexivity.
    }
    rewrite -> H.
    simpl.
    reflexivity.
Qed.

    
Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
 unfold lt.
 intros.
 split.
 -
   induction n2 as [].
   +
     rewrite -> plus_comm in H.
     simpl in H.
     apply H.
   +
     rewrite -> plus_comm in H.
     simpl in H.
     assert (H': S (n1+n2) <= S (n1+n2) +1).
     {
       apply (le_plus_l (S (n1 + n2)) 1).
     }
     assert (H'': S (n1 + n2) + 1 = 1 + S (n1 + n2) ).
     {
       rewrite -> plus_comm. reflexivity.
     }
     rewrite -> H'' in H'.
     simpl in H'.
     rewrite -> plus_comm in H.
     apply (le_trans (S (n1 + n2)) (S (S (n1 + n2))) m H') in H.
     apply IHn2 in H.
     apply H.
 -
   rewrite -> plus_comm in H.
   rewrite -> plus_lt_helper in H.
   assert (H': S n2 <= S n2 + n1).
   {
     apply le_plus_l.
   }
   apply (le_trans (S n2) (S n2 + n1) m H') in H.
   apply H.
Qed.


     
Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  unfold lt.
  intros.
  apply le_S.
  apply H.
Qed.

Lemma leb_complete_helper: forall n m,
    (n <=? m) = true -> (n <=? S m) = true.
Proof.
  intros n.
  induction n as [| n' IHn'].
  -
    intros.
    simpl.
    reflexivity.
  -
    intros.
    simpl in H.
    destruct m.
    +
      discriminate.
    +
      simpl.
      apply IHn' in H.
      apply H.
Qed.
    
Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n.
  induction n as [| n' IHn'].
  -
    intros.
    apply O_le_n.
  -
    intros.
    simpl in H.
    destruct m.
    +
      discriminate.
    +
      apply IHn' in H.
      apply n_le_m__Sn_le_Sm.
      apply H.
Qed.        

(** Hint: The next one may be easiest to prove by induction on [m]. *)

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m' IHm'].
  -
    intros.
    destruct n.
    +
      reflexivity.
    +
      inversion H.
  -
    intros.
    inversion H.
    +
      simpl. symmetry. apply leb_refl.
    +
      apply IHm' in H1.
      apply leb_complete_helper.
      apply H1.
Qed.
  
(** Hint: This one can easily be proved without using [induction]. *)

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros.
  apply leb_complete in H.
  apply leb_complete in H0.
  apply leb_correct.
  apply (le_trans n m o).
  -
    apply H.
  -
    apply H0.
Qed.

  (** [] *)

(** **** Exercise: 2 stars, standard, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  split.
  -
    apply leb_complete.
  -
    apply leb_correct.
Qed.

(** [] *)

Module R.

(** **** Exercise: 3 stars, standard, recommended (R_provability)  

    We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2] This one
      - [R 2 2 6] This one not provable

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer. No, because we can exchange the sequence 
      when exectuing c2 and c3.

    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer. No, c4 can be constructed from c2 and c3.

(* FILL IN HERE *)
*)

(* Do not modify the following line: *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (R_fact)  

    The relation [R] above actually encodes a familiar function.
    Figure out which function; then state and prove this equivalence
    in Coq? *)

Definition fR : nat -> nat -> nat := fun m n => m + n.

Theorem R_equiv_fR_helper: forall n, R 0 n n.
Proof.
  induction n as [|n' IHn'].
  -
    apply c1.
  -
    apply c3.
    apply IHn'.
Qed.


Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  split.
  -
    intros.
    unfold fR.
    induction H.
    +
      reflexivity.
    +
      rewrite <- IHR.
      simpl.
      reflexivity.
    +
      rewrite <- IHR.
      rewrite -> plus_comm.
      simpl.
      rewrite -> plus_comm. reflexivity.
    +
      simpl in IHR.
      injection IHR.
      intros.
      rewrite -> plus_comm in H0.
      simpl. injection H0.
      intros.
      rewrite -> plus_comm. apply H1.
    +
      rewrite -> plus_comm.
      apply IHR.
  -
    unfold fR.
    generalize dependent n.
    generalize dependent o.
    induction m as [| m' IHm'].
    +
      intros.
      simpl in H.
      rewrite <- H.
      apply R_equiv_fR_helper.
    +
      intros.
      rewrite <- H.
      simpl.
      apply c2.
      destruct o.
      *
        simpl in H. discriminate.
      *
        simpl in H. injection H.
        intros.
        apply IHm' in H0.
        injection H.
        intros.
        rewrite <- H1 in H0.
        apply H0.
Qed.
      
(** [] *)

End R.

(** **** Exercise: 2 stars, advanced (subsequence)  

    A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,

      [1;2;3]

    is a subsequence of each of the lists

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    but it is _not_ a subsequence of any of the lists

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove [subseq_refl] that subsequence is reflexive, that is,
      any list is a subsequence of itself.

    - Prove [subseq_app] that for any lists [l1], [l2], and [l3],
      if [l1] is a subsequence of [l2], then [l1] is also a subsequence
      of [l2 ++ l3].

    - (Optional, harder) Prove [subseq_trans] that subsequence is
      transitive -- that is, if [l1] is a subsequence of [l2] and [l2]
      is a subsequence of [l3], then [l1] is a subsequence of [l3].
      Hint: choose your induction carefully! *)

Inductive subseq {X:Type} : list X -> list X -> Prop :=
| eq (l : list X) : subseq l l
| mismt (x:X) (l1 l2 : list X) (H: subseq l1 l2) : subseq l1 (x :: l2)
| mt (x:X) (l1 l2 : list X) (H: subseq l1 l2) : subseq (x :: l1) (x :: l2)
.

(* Nothing too special, but remember, when defining an inductive proposition, 
   be sure tha we can use inversion and apply to reduce to a certain condition.
   A good way to test whether our definition is correct is to test some examples.
   Check whether we can trivially prove some simple example. *)

Example em1 : subseq [1;2;3] [1;1;1;2;2;3].
Proof.
  apply mt. apply mismt. apply mismt. apply mt. apply mismt. apply eq.
Qed.

Example em2 : subseq [1;2;3] [5;6;1;9;9;2;7;3;8].
Proof.
  apply mismt. apply mismt. apply mt. apply mismt. apply mismt.
  apply mt. apply mismt. apply mt. apply mismt. apply eq.
Qed.

Example em3 : ~ subseq [1;2;3] [1;2].
Proof.
  unfold not. intros.
  inversion H.
  -
    inversion H2. inversion H6.
  -
    inversion H1.
    +
      inversion H6.
    +
      inversion H5.
Qed.

Example em4 : ~ subseq [1;2;3] [5;6;2;1;7;3;8].
Proof.
  unfold not.
  intros.
  inversion H.
  inversion H2.
  inversion H6.
  inversion H10.
  -
    inversion H14.
    inversion H18.
    inversion H22.
    inversion H26.
  -
    inversion H13.
    inversion H18.
    inversion H22.
    inversion H26.
Qed.
    
Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  apply eq.
Qed.

Theorem subseq_nil_always : forall (l : list nat), subseq [] l.
Proof.
  induction l as [| x' l' IHl'].
  -
    apply eq.
  -
    apply mismt.
    apply IHl'.
Qed.

(* Inductive subseq : list nat -> list nat -> Prop := *)
(* | eq (l : list nat) : subseq l l *)
(* | mismt (x:nat) (l1 l2 : list nat) (H: subseq l1 l2) : subseq l1 (x :: l2) *)
(* | mt (x:nat) (l1 l2 : list nat) (H: subseq l1 l2) : subseq (x :: l1) (x :: l2) *)
(* . *)

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros.
  generalize dependent l3.
  induction H.
  -
    intros.
    induction l as [| x l' IHl'].
    +
      simpl. apply subseq_nil_always.
    +
      simpl. apply mt. apply IHl'.
  -
    intros.
    simpl. apply mismt. apply IHsubseq.
  -
    intros.
    simpl. apply mt. apply IHsubseq.
Qed.
    
Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros.
  generalize dependent l1.
  induction H0.
  -
    intros. apply H.
  -
    intros. apply mismt. apply IHsubseq in H. apply H.
  -
    intros.
    inversion H.
    +
      apply mt. apply H0.
    +
      apply mismt.  apply IHsubseq in H3. apply H3.
    +
      apply mt. apply IHsubseq in H3. apply H3.
Qed.  
  
(** [] *)

(** **** Exercise: 2 stars, standard, optional (R_provability2)  

    Suppose we give Coq the following definition:

    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.

    Which of the following propositions are provable?

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(* FILL IN HERE 

    [] *)

(* ################################################################# *)
(** * Case Study: Regular Expressions *)

(** The [even] property provides a simple example for
    illustrating inductive definitions and the basic techniques for
    reasoning about them, but it is not terribly exciting -- after
    all, it is equivalent to the two non-inductive definitions of
    evenness that we had already seen, and does not seem to offer any
    concrete benefit over them.

    To give a better sense of the power of inductive definitions, we
    now show how to use them to model a classic concept in computer
    science: _regular expressions_. *)

(** Regular expressions are a simple language for describing sets of
    strings.  Their syntax is defined as follows: *)

Inductive reg_exp {T : Type} : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp)
  | Union (r1 r2 : reg_exp)
  | Star (r : reg_exp).

(** Note that this definition is _polymorphic_: Regular
    expressions in [reg_exp T] describe strings with characters drawn
    from [T] -- that is, lists of elements of [T].

    (We depart slightly from standard practice in that we do not
    require the type [T] to be finite.  This results in a somewhat
    different theory of regular expressions, but the difference is not
    significant for our purposes.) *)

(** We connect regular expressions and strings via the following
    rules, which define when a regular expression _matches_ some
    string:

      - The expression [EmptySet] does not match any string.

      - The expression [EmptyStr] matches the empty string [[]].

      - The expression [Char x] matches the one-character string [[x]].

      - If [re1] matches [s1], and [re2] matches [s2],
        then [App re1 re2] matches [s1 ++ s2].

      - If at least one of [re1] and [re2] matches [s],
        then [Union re1 re2] matches [s].

      - Finally, if we can write some string [s] as the concatenation
        of a sequence of strings [s = s_1 ++ ... ++ s_k], and the
        expression [re] matches each one of the strings [s_i],
        then [Star re] matches [s].

        As a special case, the sequence of strings may be empty, so
        [Star re] always matches the empty string [[]] no matter what
        [re] is. *)

(** We can easily translate this informal definition into an
    [Inductive] one as follows: *)

Inductive exp_match {T} : list T -> reg_exp -> Prop :=
  | MEmpty : exp_match [] EmptyStr
  | MChar x : exp_match [x] (Char x)
  | MApp s1 re1 s2 re2
             (H1 : exp_match s1 re1)
             (H2 : exp_match s2 re2) :
             exp_match (s1 ++ s2) (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : exp_match s1 re1) :
                exp_match s1 (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : exp_match s2 re2) :
                exp_match s2 (Union re1 re2)
  | MStar0 re : exp_match [] (Star re)
  | MStarApp s1 s2 re
                 (H1 : exp_match s1 re)
                 (H2 : exp_match s2 (Star re)) :
                 exp_match (s1 ++ s2) (Star re).

(** Again, for readability, we can also display this definition using
    inference-rule notation.  At the same time, let's introduce a more
    readable infix notation. *)

Notation "s =~ re" := (exp_match s re) (at level 80).

(**

                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re
*)

(** Notice that these rules are not _quite_ the same as the
    informal ones that we gave at the beginning of the section.
    First, we don't need to include a rule explicitly stating that no
    string matches [EmptySet]; we just don't happen to include any
    rule that would have the effect of some string matching
    [EmptySet].  (Indeed, the syntax of inductive definitions doesn't
    even _allow_ us to give such a "negative rule.")

    Second, the informal rules for [Union] and [Star] correspond
    to two constructors each: [MUnionL] / [MUnionR], and [MStar0] /
    [MStarApp].  The result is logically equivalent to the original
    rules but more convenient to use in Coq, since the recursive
    occurrences of [exp_match] are given as direct arguments to the
    constructors, making it easier to perform induction on evidence.
    (The [exp_match_ex1] and [exp_match_ex2] exercises below ask you
    to prove that the constructors given in the inductive declaration
    and the ones that would arise from a more literal transcription of
    the informal rules are indeed equivalent.)

    Let's illustrate these rules with a few examples. *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

(** (Notice how the last example applies [MApp] to the strings
    [[1]] and [[2]] directly.  Since the goal mentions [[1; 2]]
    instead of [[1] ++ [2]], Coq wouldn't be able to figure out how to
    split the string on its own.)

    Using [inversion], we can also show that certain strings do _not_
    match a regular expression: *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** We can define helper functions for writing down regular
    expressions. The [reg_exp_of_list] function constructs a regular
    expression that matches exactly the list that it receives as an
    argument: *)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** We can also prove general facts about [exp_match].  For instance,
    the following lemma shows that every string [s] that matches [re]
    also matches [Star re]. *)

Lemma MStar1 :
  forall T s (re : @reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(** (Note the use of [app_nil_r] to change the goal of the theorem to
    exactly the same shape expected by [MStarApp].) *)

(** **** Exercise: 3 stars, standard (exp_match_ex1)  

    The following lemmas show that the informal matching rules given
    at the beginning of the chapter can be obtained from the formal
    inductive definition. *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Lemma MUnion' : forall T (s : list T) (re1 re2 : @reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros.
  destruct H as [H1|H2].
  -
    apply MUnionL.
    apply H1.
  -
    apply MUnionR.
    apply H2.
Qed.

(** The next lemma is stated in terms of the [fold] function from the
    [Poly] chapter: If [ss : list (list T)] represents a sequence of
    strings [s1, ..., sn], then [fold app ss []] is the result of
    concatenating them all together. *)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  induction ss as [|t ss' IHss'].
  -
    intros. simpl. apply MStar0.
  -
    intros. simpl. apply MStarApp.
    +
      apply H.
      simpl.  left. reflexivity.
    +
      apply IHss'.
      intros. apply H. simpl. right. apply H0.
Qed.

(** [] *)

(** **** Exercise: 4 stars, standard, optional (reg_exp_of_list_spec)  

    Prove that [reg_exp_of_list] satisfies the following
    specification: *)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  split.
  -
    generalize dependent s2.
    induction s1 as [| t s1' IHs1'].
    +
      intros.
      induction s2 as [| u s2' IHs2'].
      *
        reflexivity.
      *
        simpl in H.
        inversion H.
        assert (H' : s1 ++ s2 = [] -> s1 = []).
        {
          destruct s1.
          -
            intros. reflexivity.
          -
            intros. simpl in H5. inversion H5.
        }
        apply H' in H1.
        rewrite H1 in H3.
        inversion H3.
    +
      intros.
      destruct s2 as [| u s2' IHs2'].
      *
        simpl in H. inversion H.
      *
        (* We are doing nothing too special. By inversion on H, we 
           can see that t = u and s1' = s2'. But the inversion generate
           differnt terms, we need some rewrite to convert these terms. *)
        simpl in H. inversion H.
        inversion H3.
        rewrite <- H5 in H1.
        simpl in H1.
        inversion H1.
        rewrite H9 in H4.
        apply IHs1' in H4.
        rewrite H4.
        reflexivity.
  -
    intros.
    generalize dependent s2.
    induction s1 as [| t s1' IHs1'].
    +
      intros.
      destruct s2.
      *
        simpl. apply MEmpty.
      *
        inversion H.
    +
      intros.
      destruct s2 as [| u s2' IHs2'].
      *
        inversion H.
      *
        simpl.
        assert (H': t :: s1' = [t] ++ s1').
        {
          simpl. reflexivity.
        }
        rewrite H'.
        apply MApp.
        {
          inversion H.
          apply MChar.
        }
        {
          inversion H.
          apply IHs1' in H2.
          inversion H.
          rewrite H4 in H2.
          apply H2.
        }
Qed.

    (** [] *)

(** Since the definition of [exp_match] has a recursive
    structure, we might expect that proofs involving regular
    expressions will often require induction on evidence. *)

(** For example, suppose that we wanted to prove the following
    intuitive result: If a regular expression [re] matches some string
    [s], then all elements of [s] must occur as character literals
    somewhere in [re].

    To state this theorem, we first define a function [re_chars] that
    lists all characters that occur in a regular expression: *)

Fixpoint re_chars {T} (re : reg_exp) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** We can then phrase our theorem as follows: *)

(* T : Type *)
(* s : list T *)
(* re : reg_exp *)
(* x : T *)
(* Hmatch : s =~ re *)
(* Hin : In x s *)
(* ============================ *)
(* In x (re_chars re) *)

(* Inductive exp_match (T : Type) : list T -> reg_exp -> Prop := *)
(*     MEmpty : [ ] =~ EmptyStr *)
(*   | MChar : forall x : T, [x] =~ Char x *)
(*   | MApp : forall (s1 : list T) (re1 : reg_exp) (s2 : list T) (re2 : reg_exp), *)
(*            s1 =~ re1 -> s2 =~ re2 -> s1 ++ s2 =~ App re1 re2 *)
(*   | MUnionL : forall (s1 : list T) (re1 re2 : reg_exp), s1 =~ re1 -> s1 =~ Union re1 re2 *)
(*   | MUnionR : forall (re1 : reg_exp) (s2 : list T) (re2 : reg_exp), *)
(*               s2 =~ re2 -> s2 =~ Union re1 re2 *)
(*   | MStar0 : forall re : reg_exp, [ ] =~ Star re *)
(*   | MStarApp : forall (s1 s2 : list T) (re : reg_exp), *)
(*                s1 =~ re -> s2 =~ Star re -> s1 ++ s2 =~ Star re *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* WORKED IN CLASS *)
  - (* MEmpty *)
    apply Hin.
  - (* MChar *)
    apply Hin.
  - simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.

(** Something interesting happens in the [MStarApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re]), and a second one that applies when [x]
    occurs in [s2] (which matches [Star re]).  This is a good
    illustration of why we need induction on evidence for [exp_match],
    rather than induction on the regular expression [re]: The latter
    would only provide an induction hypothesis for strings that match
    [re], which would not allow us to reason about the case [In x
    s2]. *)

  - (* MStarApp *)
    simpl. rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** Exercise: 4 stars, standard (re_not_empty)  

    Write a recursive function [re_not_empty] that tests whether a
    regular expression matches some string. Prove that your function
    is correct. *)

Fixpoint re_not_empty {T : Type} (re : @reg_exp T) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => true
  | App re1 re2 => andb (re_not_empty re1) (re_not_empty re2)
  | Union re1 re2 => orb (re_not_empty re1) (re_not_empty re2)
  | Star _ => true
  end.

Lemma re_not_empty_correct : forall T (re : @reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  split.
  -
    intros.
    destruct H.
    induction H as [|x'|s1 re1 s2 re2 Hm1 IH1 Hm2 IH2
                    |s1 re1 re2 Hm IH | re1 s2 re2 Hm IH | re
                    | s1 s2 re Hm1 IH1 Hm2 IH2].
    +
      reflexivity.
    +
      reflexivity.
    +
      simpl. rewrite IH1. rewrite IH2. reflexivity.
    +
      simpl. rewrite IH. reflexivity.
    +
      simpl. rewrite IH.
      destruct (re_not_empty re1).
      *
        reflexivity.
      *
        reflexivity.
    +
      reflexivity.
    +
      reflexivity.
  -
    intros.
    induction re as [ | |x'|re1 IH1 re2 IH2|re1 IH1 re2 IH2|re IH].
    +
      simpl in H. discriminate.
    +
      exists []. apply MEmpty.
    +
      exists [x']. apply MChar.
    +
      simpl in H. 
      apply andb_true_iff in H.
      destruct H.
      apply IH1 in H.
      apply IH2 in H0.
      destruct H.
      destruct H0.
      exists (x ++ x0).
      apply MApp.
      *
        apply H.
      *
        apply H0.
    +
      simpl in H. apply orb_true_iff in H.
      destruct H.
      *
        apply IH1 in H.
        destruct H.
        exists x.
        apply MUnionL.
        apply H.
      *
        apply IH2 in H.
        destruct H.
        exists x.
        apply MUnionR.
        apply H.
    +
      exists [].
      apply MStar0.
Qed.    
(** [] *)

(* ================================================================= *)
(** ** The [remember] Tactic *)

(** One potentially confusing feature of the [induction] tactic is
    that it will let you try to perform an induction over a term that
    isn't sufficiently general.  The effect of this is to lose
    information (much as [destruct] without an [eqn:] clause can do),
    and leave you unable to complete the proof.  Here's an example: *)

  (* T : Type *)
  (* s1, s2 : list T *)
  (* re : reg_exp *)
  (* H1 : s1 =~ Star re *)
  (* ============================ *)
  (* s2 =~ Star re -> s1 ++ s2 =~ Star re *)

(* Inductive exp_match (T : Type) : list T -> reg_exp -> Prop := *)
(*     MEmpty : [ ] =~ EmptyStr *)
(*   | MChar : forall x : T, [x] =~ Char x *)
(*   | MApp : forall (s1 : list T) (re1 : reg_exp) (s2 : list T) (re2 : reg_exp), *)
(*            s1 =~ re1 -> s2 =~ re2 -> s1 ++ s2 =~ App re1 re2 *)
(*   | MUnionL : forall (s1 : list T) (re1 re2 : reg_exp), s1 =~ re1 -> s1 =~ Union re1 re2 *)
(*   | MUnionR : forall (re1 : reg_exp) (s2 : list T) (re2 : reg_exp), *)
(*               s2 =~ re2 -> s2 =~ Union re1 re2 *)
(*   | MStar0 : forall re : reg_exp, [ ] =~ Star re *)
(*   | MStarApp : forall (s1 s2 : list T) (re : reg_exp), *)
(*                s1 =~ re -> s2 =~ Star re -> s1 ++ s2 =~ Star re *)

Lemma star_app: forall T (s1 s2 : list T) (re : @reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** Just doing an [inversion] on [H1] won't get us very far in
    the recursive cases. (Try it!). So we need induction (on
    evidence!). Here is a naive first attempt: *)

  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** But now, although we get seven cases (as we would expect from the
    definition of [exp_match]), we have lost a very important bit of
    information from [H1]: the fact that [s1] matched something of the
    form [Star re].  This means that we have to give proofs for _all_
    seven constructors of this definition, even though all but two of
    them ([MStar0] and [MStarApp]) are contradictory.  We can still
    get the proof to go through for a few constructors, such as
    [MEmpty]... *)

  - (* MEmpty *)
    simpl. intros H. apply H.

(** ... but most cases get stuck.  For [MChar], for instance, we
    must show that

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    which is clearly impossible. *)

  - (* MChar. Stuck... *)
Abort.

(** The problem is that [induction] over a Prop hypothesis only works
    properly with hypotheses that are completely general, i.e., ones
    in which all the arguments are variables, as opposed to more
    complex expressions, such as [Star re].

    (In this respect, [induction] on evidence behaves more like
    [destruct]-without-[eqn:] than like [inversion].)

    An awkward way to solve this problem is "manually generalizing" 
    over the problematic expressions by adding explicit equality 
    hypotheses to the lemma: *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** We can now proceed by performing induction over evidence directly,
    because the argument to the first hypothesis is sufficiently
    general, which means that we can discharge most cases by inverting
    the [re' = Star re] equality in the context.

    This idiom is so common that Coq provides a tactic to
    automatically generate such equations for us, avoiding thus the
    need for changing the statements of our theorems. *)

Abort.

(** The tactic [remember e as x] causes Coq to (1) replace all
    occurrences of the expression [e] by the variable [x], and (2) add
    an equation [x = e] to the context.  Here's how we can use it to
    show the above result: *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** We now have [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** The [Heqre'] is contradictory in most cases, allowing us to
    conclude immediately. *)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** The interesting cases are those that correspond to [Star].  Note
    that the induction hypothesis [IH2] on the [MStarApp] case
    mentions an additional premise [Star re'' = Star re'], which
    results from the equality generated by [remember]. *)

  - (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. apply H.

  - (* MStarApp *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.

(** **** Exercise: 4 stars, standard, optional (exp_match_ex2)  *)

(** The [MStar''] lemma below (combined with its converse, the
    [MStar'] exercise above), shows that our definition of [exp_match]
    for [Star] is equivalent to the informal one given previously. *)

Lemma MStar'' : forall T (s : list T) (re : reg_exp),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros.
  remember (Star re) as re'.
  generalize dependent re.
  induction H as [| x | s1 re1 s2 re2 Hm1 IH1 Hm2 IH2 
                  | s1 re1 re2 H IH | re1 s2 re2 H IH | re1
                  | s1 s2 re1 Hm1 IH1 Hm2 IH2].
  -
    discriminate.
  -
    discriminate.
  -
    discriminate.
  -
    discriminate.
  -
    discriminate.
  -
    exists [].
    split.
    +
      reflexivity.
    +
      intros.
      destruct H.
  -
    (* For this case, first inversion Heqre' to obtain an equality proposition.
       Then use one of the inductive hypothesis to continue. Select (s1 :: ss) 
       as the existance quantity. Then perform some rewriting and we are done. *)
    intros.
    inversion Heqre'.
    apply IH2 in Heqre'.
    destruct Heqre' as [ss].
    destruct H as [H1 H2].
    exists (s1 :: ss).
    split.
    *
      simpl. rewrite -> H1. reflexivity.
    *
      intros.
      simpl in H.
      destruct H as [H3 | H4].
      {
        rewrite -> H3 in Hm1. rewrite H0 in Hm1. apply Hm1.
      }
      {
        apply H2 in H4. apply H4.
      }
Qed.  

    (** [] *)

Lemma Nonsense: forall X:Type, (exists l: list X, l = []) -> forall l : list X, l = l ++ [].
Proof.
  intros.
  destruct H as [[]].
  -
    rewrite app_nil_r.
    reflexivity.
  -
Abort.    

(** **** Exercise: 5 stars, advanced (pumping)  

    One of the first really interesting theorems in the theory of
    regular expressions is the so-called _pumping lemma_, which
    states, informally, that any sufficiently long string [s] matching
    a regular expression [re] can be "pumped" by repeating some middle
    section of [s] an arbitrary number of times to produce a new
    string also matching [re].

    To begin, we need to define "sufficiently long."  Since we are
    working in a constructive logic, we actually need to be able to
    calculate, for each regular expression [re], the minimum length
    for strings [s] to guarantee "pumpability." *)

Module Pumping.

Fixpoint pumping_constant {T} (re : @reg_exp T) : nat :=
  match re with
  | EmptySet => 0
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star _ => 1
  end.

(** Next, it is useful to define an auxiliary function that repeats a
    string (appends it to itself) some number of times. *)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

(** Now, the pumping lemma itself says that, if [s =~ re] and if the
    length of [s] is at least the pumping constant of [re], then [s]
    can be split into three substrings [s1 ++ s2 ++ s3] in such a way
    that [s2] can be repeated any number of times and the result, when
    combined with [s1] and [s3] will still match [re].  Since [s2] is
    also guaranteed not to be the empty string, this gives us
    a (constructive!) way to generate strings matching [re] that are
    as long as we like. *)

Lemma pumping : forall T (re : @reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** To streamline the proof (which you are to fill in), the [omega]
    tactic, which is enabled by the following [Require], is helpful in
    several places for automatically completing tedious low-level
    arguments involving equalities or inequalities over natural
    numbers.  We'll return to [omega] in a later chapter, but feel
    free to experiment with it now if you like.  The first case of the
    induction gives an example of how it is used. *)

Import Coq.omega.Omega.

(* The solution to pumping lemma is quite simple as long as you
   convert the le inductive proposition into leb representation.
   With leb representation, we can destruct the parameters of leb function
   to do the proper case analysis. The proof is quite long, but the
   idea is quite simple if you can find out the conversion. *)

Lemma pumping_fuck_fuck_fuck: forall a b c, a <= b -> (a + c) <= (b + c).
Proof.
  intros.
  induction H as [| b Hmatch IH].
  -
    apply le_n.
  -
    simpl. apply le_S. apply IH.
Qed.      

Lemma pumping_fuck_fuck: forall a b c d, (a < c) -> (b < d) -> (a + b < c + d).
Proof.
  unfold lt. intros. remember (S b) as b'.
  induction H0 as [| d Hmatch IH].
  -
    rewrite plus_comm. rewrite <- plus_Sn_m. rewrite <- Heqb'. rewrite -> plus_comm.
    apply pumping_fuck_fuck_fuck.
    assert (H': a <= S a).
    {
      apply le_S. apply le_n.
    }
    apply (le_trans _ _ _ H') in H.
    apply H.
  -
    assert(H': c + (S d) = S(c + d)).
    {
      rewrite -> plus_comm. simpl. rewrite -> plus_comm. reflexivity.
    }
    rewrite H'. apply le_S. apply IH.
Qed.    
                                                                       
Lemma pumping_fuck: forall a b c d, (a + b <=? c + d) = Datatypes.true -> (a <=? c) = Datatypes.false -> (b <=? d) = Datatypes.true.
Proof.
  intros.
  destruct (b <=? d) as [] eqn:E.
  -
    reflexivity.
  -
    apply leb_iff_conv in H0.
    apply leb_iff_conv in E.
    apply (pumping_fuck_fuck _ _ _ _ H0) in E.
    apply leb_iff_conv in E.
    rewrite E in H.
    discriminate.
Qed.

Lemma pumping_fuck2: forall (X:Type) (l: list X), (1 <=? length l) = Datatypes.false -> l = [].
Proof.
  intros.
  destruct l as [] eqn:E.
  -
    reflexivity.
  -
    simpl in H. discriminate.
Qed.

Lemma pumping_fuck3: forall (X:Type) (l: list X), (1 <= length l) -> l <> [].
Proof.
  intros. unfold not. intros. rewrite H0 in H. simpl in H. inversion H.
Qed.

Lemma pumping_fuck4: forall T m s (re: @reg_exp T), s =~ re -> napp m s =~ Star re.
Proof.
  intros T m.
  induction m as [| m'].
  -
    intros. simpl. apply MStar0.
  -
    intros. simpl. apply MStarApp.
    +
      apply H.
    +
      apply IHm' in H. apply H.
Qed.

Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. omega.
  -
    simpl. intros. omega.
  -
    intros.
    destruct (pumping_constant re1 <=? length s1) as [] eqn:E'.
    +
      apply leb_iff in E'.
      apply IH1 in E'.
      destruct E' as [s2' [s3' [s4']]].
      destruct H0 as [H0_1 [H0_2 H0_3]].
      exists s2'. exists s3'. exists (s4' ++ s2).
      split.
      {
        rewrite H0_1. rewrite <- app_assoc.
        assert (H': (s3' ++ s4') ++ s2 = s3' ++ s4' ++ s2).
        {
          rewrite <- app_assoc. reflexivity.
        }
        rewrite -> H'.
        reflexivity.
      }
      {
        split.
        -
          apply H0_2.
        -
          intros.
          assert(H': s2' ++ napp m s3' ++ s4' ++ s2 = (s2' ++ napp m s3' ++ s4') ++ s2).
          {
            rewrite <- app_assoc.
            assert(H': (napp m s3' ++ s4') ++ s2 = napp m s3' ++ s4' ++ s2).
            {
              rewrite -> app_assoc. reflexivity.
            }
            rewrite -> H'. reflexivity.
          }
          rewrite H'. apply MApp.
          + apply H0_3.
          + apply Hmatch2.
      }
    +
      simpl in H. rewrite app_length in H. apply leb_iff in H.
      apply (pumping_fuck _ _ _ _ H) in E'.
      apply leb_iff in E'.
      apply IH2 in E'.
      destruct E' as [s1' [s3' [s4']]].
      destruct H0 as [H0_1 [H0_2 H0_3]].
      exists (s1 ++ s1'). exists s3'. exists s4'.
      split.
      {
        rewrite H0_1. rewrite <- app_assoc.
        reflexivity.
      }
      {
        split.
        -
          apply H0_2.
        -
          intros.
          rewrite <- app_assoc.
          apply MApp.
          + apply Hmatch1.
          + apply H0_3.
      }        
  -
    intros. simpl in H. 
    assert(H': pumping_constant re1 <= pumping_constant re1 + pumping_constant re2).
    {
      apply le_plus_l.
    }
    apply (le_trans _ _ _ H') in H.
    apply IH in H.
    destruct H as [s2 [s3 [s4]]].
    destruct H as [H1 [H2 H3]].
    exists s2. exists s3. exists s4.
    split.
    + apply H1.
    + split.
      {
        apply H2.
      }
      {
        intros.
        remember (s2 ++ napp m s3 ++ s4) as s'.
        apply MUnionL.
        rewrite Heqs'.
        apply H3.
      }
  -
    intros. simpl in H.
    assert(H': pumping_constant re2 <= pumping_constant re1 + pumping_constant re2).
    {
      rewrite plus_comm.
      apply le_plus_l.
    }
    apply (le_trans _ _ _ H') in H.
    apply IH in H.
    destruct H as [s1 [s3 [s4]]].
    destruct H as [H1 [H2 H3]].
    exists s1. exists s3. exists s4.
    split.
    + apply H1.
    + split.
      {
        apply H2.
      }
      {
        intros.
        remember (s1 ++ napp m s3 ++ s4) as s'.
        apply MUnionR.
        rewrite Heqs'.
        apply H3.
      }
  -
    intros. simpl in H. inversion H.
  -
    intros. simpl in H. simpl in IH2.
    destruct (1 <=? length s2) as [] eqn:E'.
    +
      apply leb_iff in E'.
      apply IH2 in E'.
      destruct E' as [s1' [s3' [s4']]].
      destruct H0 as [H0_1 [H0_2 H0_3]].
      exists (s1 ++ s1'). exists s3'. exists s4'.
      split.
      * rewrite H0_1. rewrite -> app_assoc. reflexivity.
      *
        split.
        {
          apply H0_2.
        }
        {
          intros. rewrite <- app_assoc. apply MStarApp.
          - apply Hmatch1.
          - apply H0_3.
        }
    +
      apply pumping_fuck2 in E'.
      rewrite E' in H. rewrite app_nil_r in H. 
      apply pumping_fuck3 in H.
      exists []. exists s1. exists [].
      split.
      * simpl. rewrite -> E'. reflexivity.
      *
        split.
        {
          apply H.
        }
        {
          simpl. intros. rewrite app_nil_r.
          apply pumping_fuck4. apply Hmatch1.
        }
Qed.                                                
    (* FILL IN HERE *) 

End Pumping.
(** [] *)

(* ################################################################# *)
(** * Case Study: Improving Reflection *)

(** We've seen in the [Logic] chapter that we often need to
    relate boolean computations to statements in [Prop].  But
    performing this conversion as we did it there can result in
    tedious proof scripts.  Consider the proof of the following
    theorem: *)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** In the first branch after [destruct], we explicitly apply
    the [eqb_eq] lemma to the equation generated by
    destructing [n =? m], to convert the assumption [n =? m
    = true] into the assumption [n = m]; then we had to [rewrite]
    using this assumption to complete the case. *)

(** We can streamline this by defining an inductive proposition that
    yields a better case-analysis principle for [n =? m].
    Instead of generating an equation such as [(n =? m) = true],
    which is generally not directly useful, this principle gives us
    right away the assumption we really need: [n = m]. *)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H :   P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

(** The [reflect] property takes two arguments: a proposition
    [P] and a boolean [b].  Intuitively, it states that the property
    [P] is _reflected_ in (i.e., equivalent to) the boolean [b]: that
    is, [P] holds if and only if [b = true].  To see this, notice
    that, by definition, the only way we can produce evidence for
    [reflect P true] is by showing [P] and then using the [ReflectT]
    constructor.  If we invert this statement, this means that it
    should be possible to extract evidence for [P] from a proof of
    [reflect P true].  Similarly, the only way to show [reflect P
    false] is by combining evidence for [~ P] with the [ReflectF]
    constructor.

    It is easy to formalize this intuition and show that the
    statements [P <-> b = true] and [reflect P b] are indeed
    equivalent.  First, the left-to-right implication: *)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* WORKED IN CLASS *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(** Now you prove the right-to-left implication: *)

(** **** Exercise: 2 stars, standard, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros.
  destruct b.
  -
    inversion H. split.
    + intros. reflexivity.
    + intros. apply H0.
  -
    inversion H. split.
    + intros. apply H0 in H1. destruct H1.
    + intros. discriminate.
Qed.  
      
(** [] *)

(** The advantage of [reflect] over the normal "if and only if"
    connective is that, by destructing a hypothesis or lemma of the
    form [reflect P b], we can perform case analysis on [b] while at
    the same time generating appropriate hypothesis in the two
    branches ([P] in the first subgoal and [~ P] in the second). *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** A smoother proof of [filter_not_empty_In] now goes as follows.
    Notice how the calls to [destruct] and [apply] are combined into a
    single call to [destruct]. *)

(** (To see this clearly, look at the two proofs of
    [filter_not_empty_In] with Coq and observe the differences in
    proof state at the beginning of the first case of the
    [destruct].) *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** Exercise: 3 stars, standard, recommended (eqbP_practice)  

    Use [eqbP] as above to prove the following: *)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros.
  induction l as [| x l' IHl'].
  -
    unfold not. simpl. intros. apply H0.
  -
    simpl. unfold not. intros. destruct H0.
    +
      rewrite H0 in H. simpl in H. rewrite <-eqb_refl in H.
      discriminate.
    +
      destruct (eqbP (count n l') 0) as [H1 | H1].
      *
        apply IHl' in H1. apply H1 in H0. destruct H0.
      *
        simpl in H.
        destruct (eqbP n x) as [H2 | H2].
        {
          discriminate.
        }
        {
          apply H1 in H. destruct H.
        }
Qed.
        
        (** [] *)

(** This small example shows how reflection gives us a small gain in
    convenience; in larger developments, using [reflect] consistently
    can often lead to noticeably shorter and clearer proof scripts.
    We'll see many more examples in later chapters and in _Programming
    Language Foundations_.

    The use of the [reflect] property has been popularized by
    _SSReflect_, a Coq library that has been used to formalize
    important results in mathematics, including as the 4-color theorem
    and the Feit-Thompson theorem.  The name SSReflect stands for
    _small-scale reflection_, i.e., the pervasive use of reflection to
    simplify small proof steps with boolean computations. *)

(* ################################################################# *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars, standard, recommended (nostutter_defn)  

    Formulating inductive definitions of properties is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all.

    We say that a list "stutters" if it repeats the same element
    consecutively.  (This is different from not containing duplicates:
    the sequence [[1;4;1]] repeats the element [1] but does not
    stutter.)  The property "[nostutter mylist]" means that [mylist]
    does not stutter.  Formulate an inductive definition for
    [nostutter]. *)

Inductive nostutter {X:Type} : list X -> Prop :=
(* | NoStuNil : nostutter [] *)
(* | NoStuFst (x: X) : nostutter [x] *)
(* | NoStuSnd (x y z: X) (H1: nostutter [x;y])  *)
(* | NoStuSnd (x y: X) (l: list X) (H1: nostutter [x;y]) (H2: nostutter (y::l)) : nostutter (x :: (y :: l)) *)
| ns_unequal : forall (x y:X), x <> y -> nostutter [x;y]
| ns_nil : nostutter []
| ns_single (x: X) : nostutter [x]
| ns_long (x y: X) (l: list X) (H1: x <> y) (H2: nostutter (y::l)) : nostutter (x :: (y :: l))
.
(** Make sure each of these tests succeeds, but feel free to change
    the suggested proof (in comments) if the given one doesn't work
    for you.  Your definition might be different from ours and still
    be correct, in which case the examples might need a different
    proof.  (You'll notice that the suggested proofs use a number of
    tactics we haven't talked about, to make them more robust to
    different possible ways of defining [nostutter].  You can probably
    just uncomment and use them as-is, but you can also prove each
    example with more basic tactics.)  *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
(*   apply ns_long. *)
(*   - apply ns_unequal. discriminate. *)
(*   - *)
(*     apply ns_long. *)
(*     + *)
(*       apply ns_unequal. discriminate. *)
(*     + *)
(*       apply ns_long. *)
(*       * apply ns_unequal. discriminate. *)
(*       * apply ns_long. *)
(*         { *)
(*           apply ns_unequal. discriminate. *)
(*         } *)
(*         { *)
(*           apply ns_unequal. discriminate. *)
(*         } *)
(* Qed. *)     
       
(* FILL IN HERE *) 
 
repeat constructor; apply eqb_neq; auto.
Qed.


Example test_nostutter_2:  nostutter (@nil nat).
(* FILL IN HERE *) 

Proof. repeat constructor; apply eqb_neq; auto.
Qed.


Example test_nostutter_3:  nostutter [5].
(* FILL IN HERE *) 
Proof. repeat constructor; apply eqb_false; auto. Qed.


Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof.
  unfold not. intros. inversion H. inversion H4.
  assert(H': 1 = 1). { reflexivity. } apply H7 in H'. destruct H'.
Qed.
    
(* FILL IN HERE *)  
(* Proof. intro. *)
(*        repeat match goal with *)
(*                 h: nostutter _ |- _ => inversion h; clear h; subst *)
(*               end. *)
(*        contradiction Hneq0; auto. Qed. *)


(* Do not modify the following line: *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge)  

    Let's prove that our definition of [filter] from the [Poly]
    chapter matches an abstract specification.  Here is the
    specification, written out informally in English:

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example,

    [1;4;6;2;3]

    is an in-order merge of

    [1;6;2]

    and

    [4;3].

    Now, suppose we have a set [X], a function [test: X->bool], and a
    list [l] of type [list X].  Suppose further that [l] is an
    in-order merge of two lists, [l1] and [l2], such that every item
    in [l1] satisfies [test] and no item in [l2] satisfies test.  Then
    [filter test l = l1].

    Translate this specification into a Coq theorem and prove
    it.  (You'll need to begin by defining what it means for one list
    to be a merge of two others.  Do this with an inductive relation,
    not a [Fixpoint].)  *)

Inductive in_order_merge {X:Type}: list X -> list X -> list X -> Prop :=
| iom_empty : in_order_merge [] [] []
| iom_left (x:X) (l1 l2 l3: list X) (H: in_order_merge l1 l2 l3):
    in_order_merge (x::l1) l2 (x::l3)
| iom_right (x:X) (l1 l2 l3: list X) (H: in_order_merge l1 l2 l3):
    in_order_merge l1 (x::l2) (x::l3)
.                   

Example iom_e1: in_order_merge [1;6;2] [4;3] [1;4;6;2;3].
Proof.
  apply iom_left. apply iom_right. apply iom_left.
  apply iom_left. apply iom_right. apply iom_empty.
Qed.

Example iom_e2: in_order_merge [1;1;3;7;4] [1;4;5;6] [1;1;1;3;7;4;4;5;6].
Proof.
  apply iom_right. apply iom_left. apply iom_left. apply iom_left.
  apply iom_left. apply iom_right. apply iom_left. apply iom_right.
  apply iom_right. apply iom_empty.
Qed.

Example iom_e3: ~ in_order_merge [6;4;3] [1;3;4] [7;0;5;2;2;1;1].
Proof.
  unfold not. intros. inversion H. Qed.

Example iom_e4: ~ in_order_merge [7;2;3] [7;5;1;1] [7;7;5;3;2;1;1].
Proof.
  unfold not. intros. inversion H.
  -
    inversion H3. inversion H7. inversion H12.
  -
    inversion H2. inversion H8. inversion H12.
Qed.

Lemma filter_challenge_helper_2_1: forall (X:Type) (x:X) (l:list X) (test:X->bool),
    length (filter test l) <= length l.
Proof.
  intros. induction l as [| x' l' IHl'].
  -
    simpl. apply le_n.
  -
    simpl. destruct (test x') as [] eqn:E.
    +
      simpl. apply (Pumping.pumping_fuck_fuck_fuck _ _ 1) in IHl'.
      rewrite plus_comm in IHl'. simpl in IHl'. rewrite plus_comm in IHl'. simpl in IHl'.
      apply IHl'.
    +
      apply le_S. apply IHl'.
Qed.

Theorem filter_challenge_helper_2_2: forall n, ~(S n <= n).
Proof.
  intros.
  assert(H: n < S n).
  {
    unfold lt. apply le_n.
  }
  assert(H': S n > n).
  {
    unfold gt. apply H.
  }
  apply Gt.gt_not_le in H'.
  apply H'.
Qed.

Lemma filter_challenge_helper_2: forall (X:Type) (x:X) (l:list X) (test:X->bool),
    length (filter test l) <> length (x :: l).
Proof.
  simpl. unfold not. intros. assert(H': length (filter test l) <= length l).
  {
    apply (filter_challenge_helper_2_1 X x l test).
  }
  rewrite H in H'. apply (filter_challenge_helper_2_2 _) in H'. destruct H'.
Qed.  

Lemma filter_challenge_helper_1: forall (X:Type) (l1 l2: list X), length l1 <> length l2 -> l1 <> l2.
Proof.
  unfold not.
  intros. assert(H': length l1 = length l2).
  {
    rewrite H0. reflexivity.
  }
  apply H in H'. destruct H'.
Qed.

Theorem filter_challenge_helper: forall (X:Type) (x:X) (l:list X) (test:X->bool),
    filter test l <> x :: l.
  intros.
  apply filter_challenge_helper_1. apply filter_challenge_helper_2.
Qed.

Theorem filter_challenge: forall (X:Type) (l1 l2 l: list X) (test: X -> bool),
    in_order_merge l1 l2 l ->
    filter test l1 = l1 ->
    filter test l2 = [] ->
    filter test l = l1.
Proof.
  intros X l1 l2 l test H.
  induction H as [| x' l1' l2' l3' Hmatch IH | x' l1' l2' l3' Hmatch IH].
  -
    intros. reflexivity.
  -
    intros. simpl in H. destruct (test x') as [] eqn:E.
    +
      inversion H. apply (IH H2) in H0. simpl. rewrite E. rewrite H0. rewrite H2.
      reflexivity.
    +
      simpl. rewrite E. apply filter_challenge_helper in H. destruct H.
  -
    intros. simpl in H0. destruct (test x') as [] eqn:E.
    +
      inversion H0.
    +
      apply (IH H) in H0. simpl. rewrite E. apply H0.
Qed.

(* Do not modify the following line: *)
Definition manual_grade_for_filter_challenge : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2)  

    A different way to characterize the behavior of [filter] goes like
    this: Among all subsequences of [l] with the property that [test]
    evaluates to [true] on all their members, [filter test l] is the
    longest.  Formalize this claim and prove it. *)

Theorem filter_challenge_2: forall (X:Type) (l1 l:list X) (test:X->bool),
    subseq l1 l -> filter test l1 = l1 -> length l1 <= length (filter test l).
Proof.
  intros X l1 l test H.
  induction H as [l' | x' l1' l2' Hmatch IH | x' l1' l2' Hmatch IH].
  -
    intros. rewrite -> H. apply le_n.
  -
    intros. apply IH in H. simpl. destruct (test x') as [] eqn:E.
    +
      simpl. apply le_S in H. apply H.
    +
      apply H.
  -
    intros. simpl in H. destruct (test x') as [] eqn:E.
    +
      inversion H. rewrite H1. apply IH in H1. simpl. rewrite E. simpl.
      apply (Pumping.pumping_fuck_fuck_fuck _ _ 1) in H1.
      rewrite plus_comm in H1. simpl in H1. rewrite plus_comm in H1. simpl in H1.
      apply H1.
    +
      apply filter_challenge_helper in H. destruct H.
Qed.
  
(* FILL IN HERE 

    [] *)

(** **** Exercise: 4 stars, standard, optional (palindromes)  

    A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor like

        c : forall l, l = rev l -> pal l

      may seem obvious, but will not work very well.)

    - Prove ([pal_app_rev]) that

       forall l, pal (l ++ rev l).

    - Prove ([pal_rev] that)

       forall l, pal l -> l = rev l.
*)

Inductive pal {X:Type}: list X -> Prop :=
| pal_nil: pal []
| pal_single (x:X): pal [x]
| pal_reflect (x:X) (l: list X) (H: pal l): pal ( (x :: l) ++ [x])
.

Theorem pal_app_rev: forall (X:Type) (l:list X),
    pal (l ++ rev l).
Proof.
  intros. induction l as [| x' l' IH].
  -
    simpl. apply pal_nil.
  -
    simpl. rewrite app_assoc.
    apply pal_reflect. apply IH.
Qed.

Theorem pal_rev: forall (X:Type) (l:list X), pal l -> l = rev l.
Proof.
  intros X l H.
  induction H as [| x | x l' Hmatch IH].
  -
    simpl. reflexivity.
  -
    reflexivity.
  -
    simpl. assert (H': rev (l' ++ [x]) = rev [x] ++ rev l').
    {
      apply rev_app_distr.
    }
    simpl in H'. rewrite H'. rewrite <- IH. reflexivity.
Qed.

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_pal_pal_app_rev_pal_rev : option (nat*string) := None.
(** [] *)

(** **** Exercise: 5 stars, standard, optional (palindrome_converse)  

    Again, the converse direction is significantly more difficult, due
    to the lack of evidence.  Using your definition of [pal] from the
    previous exercise, prove that

     forall l, l = rev l -> pal l.
 *)

(* This problem is extremely hard to tackel if we directly do induction on l. 
   Induction on l leads to the following proof: prove that when x :: l = rev (x :: l), 
   we have l = rev l, which is clearly false. To tackle this problem, we need to induct
   on a new structure, that adds new elements to both head and tail of the list.
   In this case, we can rely on pal_reflect to simplify the goal, and use properties
   of rev to proceed, leading to a feasible proof.

   What we do here is to define a new type called blist. blist is a binary version 
   of the original list definition. It adds elements to both head and tail 
   using the bcons constructor. 

   However, in order to transform the list l appeared in the original theorem into
   a blist, we need to prove that there exists some blist bl, such that 
   l = blist_to_list bl. With this lemma, we can turn the orignal list into blist and
   do induction over blist. 

   Doing induction over blist leads to a very straightforward proof of the 
   panlindrome_converse theorem. 

   The hard part is actually how to prove the lemma for transforming list into blist.
   The tricky part is to do induction on the list first, and then do induction on 
   blist. After doing induction on list, we will proceed to a situation where we can't
   make any more progress. Then we can see that, if we do induction on blist, we can 
   actually continue the proof and complete the final proof of the lemma.
*)

Inductive blist {X:Type} : Type :=
| bnil
| bone (x:X)
| bcons (x:X) (bl: blist) (y:X).

Fixpoint blist_to_list {X:Type} (bl:blist) : list X :=
  match bl with
  | bnil => []
  | bone x => [x]
  | bcons x bl' y => x :: (blist_to_list bl') ++ [y]
  end.


Theorem panlindrome_helper_2:
  forall (X:Type) (x y:X) (l1 l2:list X),
    l1 ++ [x] = l2 ++ [y] -> l1 = l2 /\ x = y.
Proof.
  intros.
  split.
  -
    generalize dependent x.
    generalize dependent y.
    generalize dependent l2.
    induction l1 as [| x' l1' IHl1'].
    +
      simpl. intros.
      destruct l2.
      { reflexivity. }
      { simpl in H. inversion H.
        destruct l2.
        - simpl in H2. inversion H2.
        - simpl in H2. inversion H2.
      }
    +
      intros.
      destruct l2.
      {
        simpl in H. inversion H.
        simpl in H2. 
        destruct l1'.
        + simpl in H2. inversion H2.
        + simpl in H2. inversion H2.
      }
      {
        simpl in H. inversion H.
        apply IHl1' in H2. rewrite H2. reflexivity.
      }
  -
    generalize dependent x.
    generalize dependent y.
    generalize dependent l2.
    induction l1 as [| x' l1' IHl1'].
    +
      simpl. intros.
      destruct l2.
      { inversion H. reflexivity. }
      { simpl in H. inversion H.
        destruct l2.
        - simpl in H2. inversion H2.
        - simpl in H2. inversion H2.
      }
    +
      intros.
      destruct l2.
      {
        simpl in H. inversion H.
        simpl in H2. 
        destruct l1'.
        + simpl in H2. inversion H2.
        + simpl in H2. inversion H2.
      }
      {
        simpl in H. inversion H.
        apply IHl1' in H2. rewrite H2. reflexivity.
      }
Qed.          
          
Theorem panlindrome_helper_3:
  forall (X:Type) (x:X) (l:list X),
    rev(l++[x]) = x::(rev l).
Proof.
  intros. generalize dependent x.
  induction l as [| x' l' IHl'].
  -
    simpl. intros. reflexivity.
  -
    intros. simpl. rewrite IHl'. simpl. reflexivity.
Qed.

Theorem panlindorme_helper_1:
  forall (X:Type) (l:list X), (exists (bl:blist), l = blist_to_list bl).
Proof.
  intros.
  induction l as [| x' l' IH].
  -
    exists bnil. reflexivity.
  -
    destruct IH as [bl'].
    generalize dependent l'. generalize dependent x'.
    induction bl' as [| hd | hd' bl'' IH tl'].
    +
      intros. simpl in H. rewrite H. exists (bone x'). reflexivity.
    +
      intros. simpl in H. rewrite H. exists (bcons x' bnil hd). reflexivity.
    +
      intros.
      destruct l' as [|x_tmp l_tmp].
      {
        simpl in H. inversion H.
      }
      {
        destruct l_tmp as [|y_tmp l_tmp].
        -
          simpl in H. inversion H. destruct (blist_to_list bl'').
          + inversion H2.
          + simpl in H2. inversion H2.
        -
          assert(H': y_tmp::l_tmp = rev(rev(y_tmp::l_tmp))).
          {
            rewrite rev_involutive. reflexivity.
          }
          rewrite H' in H.
          destruct (rev (y_tmp :: l_tmp)) as [|rev_hd rev_tl].
          +
            simpl in H'. inversion H'.
          +
            simpl in H. inversion H as [H1].
            apply panlindrome_helper_2 in H0. destruct H0 as [H0_1 H0_2].
            rewrite H'. simpl.
            apply (IH hd' (rev rev_tl)) in H0_1.
            destruct H0_1 as [bl_fuck].
            assert(H_fuck: x' :: hd' :: rev rev_tl ++ [rev_hd] = x' :: (hd' :: rev rev_tl) ++ [rev_hd]).
            {
              simpl. reflexivity.
            }
            rewrite H_fuck. rewrite H0.
            exists (bcons x' bl_fuck rev_hd).
            simpl. reflexivity.
      }
Qed.            
            
Theorem palindrome_converse: forall (X:Type) (l:list X), l = rev l -> pal l.
Proof.
  intros X l.
  assert(H': exists (bl:blist), l = blist_to_list bl).
  {
    apply (panlindorme_helper_1 X l).
  }
  destruct H' as [bl]. rewrite H.
  intros. generalize dependent l. induction bl as [| x' | x' bl'' IH y'].
  -
    simpl. intros. apply pal_nil.
  -
    simpl. intros. apply pal_single.
  -
    intros. simpl in H0. rewrite panlindrome_helper_3 in H0.
    inversion H0. apply panlindrome_helper_2 in H3. destruct H3 as [HFUCK HSHIT].
    simpl. apply pal_reflect.
    (* Here comes the most important step, which is to prove that
       we have some l' so that l' = blist_to_list bl'' *)
    simpl in H. destruct l as [| hd tl].
    +
      inversion H.
    +
      destruct tl as [| hd' tl'].
      {
        inversion H.
        destruct (blist_to_list bl'').
        -  simpl in H4. inversion H4.
        -  simpl in H4. inversion H4.
      }
      {
        assert(H': hd' :: tl' = rev (rev (hd' :: tl'))).
        {
          rewrite rev_involutive. reflexivity.
        }
        rewrite H' in H.
        destruct (rev (hd' :: tl')) as [| hd'' tl''] eqn:E.
        - simpl in H'. inversion H'.
        - simpl in H. inversion H. 
          apply panlindrome_helper_2 in H4. destruct H4.
          apply (IH HFUCK) in H1. apply H1.
      }
Qed.        
        
(** **** Exercise: 4 stars, advanced, optional (NoDup)  

    Recall the definition of the [In] property from the [Logic]
    chapter, which asserts that a value [x] appears at least once in a
    list [l]: *)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** Your first task is to use [In] to define a proposition [disjoint X
    l1 l2], which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in
    common. *)

Fixpoint disjoint (X:Type) (l1 l2: list X) : Prop :=
  match l1 with
  | [] => True
  | hd :: tl => (~(In hd l2)) /\ (disjoint X tl l2)
  end.

(** Next, use [In] to define an inductive proposition [NoDup X
    l], which should be provable exactly when [l] is a list (with
    elements of type [X]) where every member is different from every
    other.  For example, [NoDup nat [1;2;3;4]] and [NoDup
    bool []] should be provable, while [NoDup nat [1;2;1]] and
    [NoDup bool [true;true]] should not be.  *)

Inductive NoDup (X:Type) : (list X) -> Prop :=
| nd_nil : NoDup X []
| nd_single (x:X) : NoDup X [x]
| nd_long (x:X) (l: list X) (H1: ~(In x l)) (H2: NoDup X l) : NoDup X (x :: l). 


(* FILL IN HERE *)

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [NoDup] and [++] (list append).  *)

Theorem nodup_fucker_helper_1 : forall (X:Type) (l1 l2:list X),
    [] = l1 ++ l2 -> l1 = [] /\ l2 = [].
Proof.
  intros. split.
  -
    destruct l1.
    +
      reflexivity.
    +
      simpl in H. inversion H.
  -
    destruct l2.
    +
      reflexivity.
    +
      destruct l1.
      {
        simpl in H. inversion H.
      }
      {
        simpl in H. inversion H.
      }
Qed.

Theorem nodup_fucker_helper_2 : forall (X:Type) (l:list X),
    disjoint X l [].
Proof.
  intros. induction l as [| x' l' IH].
  -
    simpl. apply I.
  -
    simpl. split.
    +
      unfold not. intros. destruct H.
    +
      apply IH.
Qed.

Theorem nodup_fucker_3 : forall (X:Type) (x:X) (l1 l2:list X),
    ~ In x (l1 ++ l2) -> ~ In x l2.
Proof.
  intros. rewrite In_app_iff in H.
  unfold not. unfold not in H. intros H'. apply H. right. apply H'.
Qed.
    
Theorem nodup_fucker: forall (X:Type) (l1 l2: list X),
    NoDup X (l1 ++ l2) -> disjoint X l1 l2.
Proof.
  intros X l1 l2.
  remember (l1 ++ l2) as l.
  intros H. generalize dependent l1. generalize dependent l2.
  induction H as [| x' | x' l' Hmatch1 Hmatch2 IH2].
  -
    intros. apply nodup_fucker_helper_1 in Heql.
    destruct Heql as [H1 H2]. rewrite H1. rewrite H2. simpl.
    apply I.
  -
    intros.
    destruct l1 as [| l1_h l1_tl].
    +
      simpl. apply I.
    +
      destruct l2 as [| l2_h l2_tl].
      {
        rewrite app_nil_r in Heql. inversion Heql.
        simpl. split.
        - unfold not. intros. destruct H.
        - apply I.
      }
      {
        simpl in Heql. destruct l1_tl.
        - simpl in Heql. inversion Heql.
        - simpl in Heql. inversion Heql.
      }
  -
    intros.
    destruct l1 as [| l1_h l1_tl].
    +
      simpl. apply I.
    +
      simpl in Heql. inversion Heql.
      assert(H2: l' = l1_tl ++ l2). { apply H1. }
      apply IH2 in H1. simpl. split.
      {
        apply (nodup_fucker_3 X l1_h l1_tl l2).
        rewrite <- H2. rewrite <- H0. apply Hmatch1.
      }
      {
        apply H1.
      }
Qed.                          

(* FILL IN HERE *)

(* Do not modify the following line: *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** Exercise: 4 stars, advanced, optional (pigeonhole_principle)  

    The _pigeonhole principle_ states a basic fact about counting: if
    we distribute more than [n] items into [n] pigeonholes, some
    pigeonhole must contain at least two items.  As often happens, this
    apparently trivial fact about numbers requires non-trivial
    machinery to prove, but we now have enough... *)

(** First prove an easy useful lemma. *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l. generalize dependent x.
  induction l as [| x l' IHl].
  -
    intros. simpl in H. destruct H.
  -
    intros. simpl in H. destruct H.
    +
      exists []. exists l'. rewrite H. simpl. reflexivity.
    +
      apply IHl in H. destruct H as [l1' [l2']].
      exists (x::l1'). exists l2'.
      rewrite H. simpl. reflexivity.
Qed.
      
(** Now define a property [repeats] such that [repeats X l] asserts
    that [l] contains at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
| rep_fst (x:X) (l:list X) (H2: repeats l) : repeats (x :: l) 
| rep_snd (x:X) (l:list X) (H: In x l) : repeats (x :: l)
.

Example rp_e1: ~ (repeats [1]).
Proof.
  unfold not. intros. inversion H.
  -
    inversion H0.
  -
    simpl in H1. destruct H1.
Qed.

Example rp_e2: ~ (repeats [1;2]).
Proof.
  unfold not. intros. inversion H.
  -
    simpl in H0. inversion H0.
    +
      inversion H4.
    +
      inversion H4.
  -
    simpl in H1. destruct H1.
    +
      inversion H1.
    +
      destruct H1.
Qed.

(** Now, here's a way to formalize the pigeonhole principle.  Suppose
    list [l2] represents a list of pigeonhole labels, and list [l1]
    represents the labels assigned to a list of items.  If there are
    more items than labels, at least two items must have the same
    label -- i.e., list [l1] must contain repeats.

    This proof is much easier if you use the [excluded_middle]
    hypothesis to show that [In] is decidable, i.e., [forall x l, (In x
    l) \/ ~ (In x l)].  However, it is also possible to make the proof
    go through _without_ assuming that [In] is decidable; if you
    manage to do this, you will not need the [excluded_middle]
    hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
   -
     intros. destruct l2.
     +
       simpl in H1. inversion H1.
     +
       simpl in H1. inversion H1.
   -
     intros.
     unfold excluded_middle in H.
     destruct (H (In x l1')) as [H' | H''].
     +
       apply rep_snd. apply H'.
     +
       unfold not in H''.
Abort.
         

(* Do not modify the following line: *)
Definition manual_grade_for_check_repeats : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** Extended Exercise: A Verified Regular-Expression Matcher *)

(** We have now defined a match relation over regular expressions and
    polymorphic lists. We can use such a definition to manually prove that
    a given regex matches a given string, but it does not give us a
    program that we can run to determine a match autmatically.

    It would be reasonable to hope that we can translate the definitions
    of the inductive rules for constructing evidence of the match relation
    into cases of a recursive function reflects the relation by recursing
    on a given regex. However, it does not seem straightforward to define
    such a function in which the given regex is a recursion variable
    recognized by Coq. As a result, Coq will not accept that the function
    always terminates.

    Heavily-optimized regex matchers match a regex by translating a given
    regex into a state machine and determining if the state machine
    accepts a given string. However, regex matching can also be
    implemented using an algorithm that operates purely on strings and
    regexes without defining and maintaining additional datatypes, such as
    state machines. We'll implemement such an algorithm, and verify that
    its value reflects the match relation. *)

(** We will implement a regex matcher that matches strings represented
    as lists of ASCII characters: *)
Require Export Coq.Strings.Ascii.

Definition string := list ascii.

(** The Coq standard library contains a distinct inductive definition
    of strings of ASCII characters. However, we will use the above
    definition of strings as lists as ASCII characters in order to apply
    the existing definition of the match relation.

    We could also define a regex matcher over polymorphic lists, not lists
    of ASCII characters specifically. The matching algorithm that we will
    implement needs to be able to test equality of elements in a given
    list, and thus needs to be given an equality-testing
    function. Generalizing the definitions, theorems, and proofs that we
    define for such a setting is a bit tedious, but workable. *)

(** The proof of correctness of the regex matcher will combine
    properties of the regex-matching function with properties of the
    [match] relation that do not depend on the matching function. We'll go
    ahead and prove the latter class of properties now. Most of them have
    straightforward proofs, which have been given to you, although there
    are a few key lemmas that are left for you to prove. *)

(** Each provable [Prop] is equivalent to [True]. *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** Each [Prop] whose negation is provable is equivalent to [False]. *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] matches no string. *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] only matches the empty string. *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] matches no non-empty string. *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] matches no string that starts with a non-[a] character. *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** If [Char a] matches a non-empty string, then the string's tail is empty. *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] matches string [s] iff [s = s0 ++ s1], where [s0]
    matches [re0] and [s1] matches [re1]. *)
Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** Exercise: 3 stars, standard, optional (app_ne)  

    [App re0 re1] matches [a::s] iff [re0] matches the empty string
    and [a::s] matches [re1] or [s=s0++s1], where [a::s0] matches [re0]
    and [s1] matches [re1].

    Even though this is a property of purely the match relation, it is a
    critical observation behind the design of our regex matcher. So (1)
    take time to understand it, (2) prove it, and (3) look for how you'll
    use it later. *)
Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([ ] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  split.
  -
    intros. inversion H. destruct s1 as [| s1_h s1_tl].
    +
      left. simpl. split.
      * apply H3. * apply H4.
    +
      simpl in H1. inversion H1. right.
      exists s1_tl, s2. split.
      * reflexivity.
      * split.
        { rewrite <- H6. apply H3. }
        { apply H4. }
  -
    intros. destruct H.
    +
      destruct H as [H1 H2].
      apply (MApp [] re0 (a::s) re1 H1 H2).
    +
      destruct H as [s0 [s1]].
      destruct H as [H1 [H2 H3]].
      rewrite H1.
      apply (MApp (a::s0) re0 s1 re1 H2) in H3.
      simpl in H3. apply H3.
Qed.
      
(** [] *)

(** [s] matches [Union re0 re1] iff [s] matches [re0] or [s] matches [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** Exercise: 3 stars, standard, optional (star_ne)  

    [a::s] matches [Star re] iff [s = s0 ++ s1], where [a::s0] matches
    [re] and [s1] matches [Star re]. Like [app_ne], this observation is
    critical, so understand it, prove it, and keep it in mind.

    Hint: you'll need to perform induction. There are quite a few
    reasonable candidates for [Prop]'s to prove by induction. The only one
    that will work is splitting the [iff] into two implications and
    proving one by induction on the evidence for [a :: s =~ Star re]. The
    other implication can be proved without induction.

    In order to prove the right property by induction, you'll need to
    rephrase [a :: s =~ Star re] to be a [Prop] over general variables,
    using the [remember] tactic.  *)

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  split.
  -
    intros. remember (a :: s) as l. remember (Star re) as re'.
    induction H as [| x' | s1' re1' s2' re2' Hmatch1 IH1 Hmatch2 IH2
                    | s1' re1' re2' H IH | re1' s2' re2' H IH
                    | re' | s1' s2' re' Hmatch1 IH1 Hmatch2 IH2].
    +
      inversion Heql.
    +
      inversion Heqre'.
    +
      inversion Heqre'.
    +
      inversion Heqre'.
    +
      inversion Heqre'.
    +
      inversion Heql.
    +
      destruct s1' as [| s1'_h s1'_tl].
      *
        simpl in Heql. apply (IH2 Heql) in Heqre'.
        apply Heqre'.
      *
        simpl in Heql. inversion Heql.
        exists s1'_tl, s2'.
        split.
        { reflexivity. }
        { split.
          - rewrite H0 in Hmatch1. inversion Heqre'. rewrite <- H2.
            apply Hmatch1.
          - apply Hmatch2.
        }
  -
    intros. destruct H as [s0 [s1]].
    destruct H as [H1 [H2 H3]].
    rewrite H1. assert(H': a::s0++s1 = (a::s0) ++ s1).
    {
      reflexivity.
    }
    rewrite H'. apply MStarApp.
    + apply H2.
    + apply H3.
Qed.                                         
    
(** [] *)

(** The definition of our regex matcher will include two fixpoint
    functions. The first function, given regex [re], will evaluate to a
    value that reflects whether [re] matches the empty string. The
    function will satisfy the following property: *)
Definition refl_matches_eps m :=
  forall re : @reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** Exercise: 2 stars, standard, optional (match_eps)  

    Complete the definition of [match_eps] so that it tests if a given
    regex matches the empty string: *)
Fixpoint match_eps (re: @reg_exp ascii) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => false
  | App re1 re2 => andb (match_eps re1) (match_eps re2)
  | Union re1 re2 => orb (match_eps re1) (match_eps re2)
  | Star _ => true
  end.

  
(** [] *)

(** **** Exercise: 3 stars, standard, optional (match_eps_refl)  

    Now, prove that [match_eps] indeed tests if a given regex matches
    the empty string.  (Hint: You'll want to use the reflection lemmas
    [ReflectT] and [ReflectF].) *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps. intros.
  destruct (match_eps re) as [] eqn:E.
  -
    apply ReflectT.
    induction re as [| | x | re1 IH1 re2 IH2 | re1 IH1 re2 IH2 | re1 IH1].
    +
      simpl in E. discriminate.
    +
      apply MEmpty.
    +
      simpl in E. discriminate.
    +
      simpl in E.
      destruct (match_eps re1) as [].
      *
        destruct (match_eps re2) as [].
        {
          assert(H': true = true).
          {
            reflexivity.
          }
          assert(H'': true = true).
          {
            reflexivity.
          }
          apply IH1 in H'.
          apply IH2 in H''.
          assert(H''':  forall X:Type, @nil X = @nil X ++ @nil X).
          {
            reflexivity.
          }
          rewrite H'''. apply MApp.
          - apply H'.
          - apply H''.
        }
        simpl in E. discriminate.
      *
        simpl in E. discriminate.
    +
      simpl in E.
      destruct (match_eps re1).
      *
        assert(H: true = true).
        {
          reflexivity.
        }
        apply IH1 in H. apply MUnionL. apply H.
      *
        destruct (match_eps re2).
        {
          assert(H: true = true).
          {
            reflexivity.
          }
          apply IH2 in H. apply MUnionR. apply H.
        }
        {
          simpl in E. discriminate.
        }
    +
      apply MStar0.
  -
    apply ReflectF. unfold not. intros.
    remember [] as s.
    induction H as [| x' | s1' re1' s2' re2' Hmatch1 IH1 Hmatch2 IH2
                    | s1' re1' re2' H IH | re1' s2' re2' H IH
                    | re' | s1' s2' re' Hmatch1 IH1 Hmatch2 IH2].
    +
      simpl in E. discriminate.
    +
      inversion Heqs.
    +
      Abort.
            
(** [] *)

(** We'll define other functions that use [match_eps]. However, the
    only property of [match_eps] that you'll need to use in all proofs
    over these functions is [match_eps_refl]. *)

(** The key operation that will be performed by our regex matcher will
    be to iteratively construct a sequence of regex derivatives. For each
    character [a] and regex [re], the derivative of [re] on [a] is a regex
    that matches all suffixes of strings matched by [re] that start with
    [a]. I.e., [re'] is a derivative of [re] on [a] if they satisfy the
    following relation: *)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** A function [d] derives strings if, given character [a] and regex
    [re], it evaluates to the derivative of [re] on [a]. I.e., [d]
    satisfies the following property: *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** Exercise: 3 stars, standard, optional (derive)  

    Define [derive] so that it derives strings. One natural
    implementation uses [match_eps] in some cases to determine if key
    regex's match the empty string. *)
Fixpoint derive (a : ascii) (re : @reg_exp ascii) : @reg_exp ascii
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** The [derive] function should pass the following tests. Each test
    establishes an equality between an expression that will be
    evaluated by our regex matcher and the final value that must be
    returned by the regex matcher. Each test is annotated with the
    match fact that it reflects. *)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 4 stars, standard, optional (derive_corr)  

    Prove that [derive] in fact always derives strings.

    Hint: one proof performs induction on [re], although you'll need
    to carefully choose the property that you prove by induction by
    generalizing the appropriate terms.

    Hint: if your definition of [derive] applies [match_eps] to a
    particular regex [re], then a natural proof will apply
    [match_eps_refl] to [re] and destruct the result to generate cases
    with assumptions that the [re] does or does not match the empty
    string.

    Hint: You can save quite a bit of work by using lemmas proved
    above. In particular, to prove many cases of the induction, you
    can rewrite a [Prop] over a complicated regex (e.g., [s =~ Union
    re0 re1]) to a Boolean combination of [Prop]'s over simple
    regex's (e.g., [s =~ re0 \/ s =~ re1]) using lemmas given above
    that are logical equivalences. You can then reason about these
    [Prop]'s naturally using [intro] and [destruct]. *)
Lemma derive_corr : derives derive.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** We'll define the regex matcher using [derive]. However, the only
    property of [derive] that you'll need to use in all proofs of
    properties of the matcher is [derive_corr]. *)

(** A function [m] matches regexes if, given string [s] and regex [re],
    it evaluates to a value that reflects whether [s] is matched by
    [re]. I.e., [m] holds the following property: *)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** Exercise: 2 stars, standard, optional (regex_match)  

    Complete the definition of [regex_match] so that it matches
    regexes. *)
Fixpoint regex_match (s : string) (re : @reg_exp ascii) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.
(** [] *)

(** **** Exercise: 3 stars, standard, optional (regex_refl)  

    Finally, prove that [regex_match] in fact matches regexes.

    Hint: if your definition of [regex_match] applies [match_eps] to
    regex [re], then a natural proof applies [match_eps_refl] to [re]
    and destructs the result to generate cases in which you may assume
    that [re] does or does not match the empty string.

    Hint: if your definition of [regex_match] applies [derive] to
    character [x] and regex [re], then a natural proof applies
    [derive_corr] to [x] and [re] to prove that [x :: s =~ re] given
    [s =~ derive x re], and vice versa. *)
Theorem regex_refl : matches_regex regex_match.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(* Wed Jan 9 12:02:45 EST 2019 *)
