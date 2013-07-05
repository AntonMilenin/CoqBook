(** * Logic: Logic in Coq *)

(* $Date: 2012-07-22 18:36:58 -0400 (Sun, 22 Jul 2012) $ *)
Require Import LibTactics.
Require Export "Prop". 

(** Coq's built-in logic is extremely small: only [Inductive]
    definitions, universal quantification ([forall]), and
    implication ([->]) are primitive, while all the other familiar
    logical connectives -- conjunction, disjunction, negation,
    existential quantification, even equality -- can be defined using
    just these. *)

(* ########################################################### *)
(** * Quantification and Implication *)

(** In fact, [->] and [forall] are the _same_ primitive!  Coq's [->]
    notation is actually just a shorthand for [forall].  The [forall]
    notation is more general, because it allows us to _name_ the
    hypothesis. *)

(** For example, consider this proposition: *)

Definition funny_prop1 := 
  forall n, forall (E : beautiful n), beautiful (n+3).

(** If we had a proof term inhabiting this proposition, it would
    be a function with two arguments: a number [n] and some evidence
    that [n] is beautiful.  But the name [E] for this evidence is not
    used in the rest of the statement of [funny_prop1], so it's a bit
    silly to bother making up a name.  We could write it like this
    instead, using the dummy identifier [_] in place of a real
    name: *)

Definition funny_prop1' := 
  forall n, forall (_ : beautiful n), beautiful (n+3).

(** Or, equivalently, we can write it in more familiar notation: *)

Definition funny_prop1'' := 
  forall n, beautiful n -> beautiful (n+3). 

(** This illustrates that "[P -> Q]" is just syntactic sugar for
    "[forall (_:P), Q]". *)

(* ########################################################### *)
(** * Conjunction *)

(** The logical conjunction of propositions [P] and [Q] can be
    represented using an [Inductive] definition with one
    constructor. *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

(** Note that, like the definition of [ev] in the previous
    chapter, this definition is parameterized; however, in this case,
    the parameters are themselves propositions, rather than numbers. *)

(** The intuition behind this definition is simple: to
    construct evidence for [and P Q], we must provide evidence
    for [P] and evidence for [Q].  More precisely:

    - [conj p q] can be taken as evidence for [and P Q] if [p]
      is evidence for [P] and [q] is evidence for [Q]; and

    - this is the _only_ way to give evidence for [and P Q] --
      that is, if someone gives us evidence for [and P Q], we
      know it must have the form [conj p q], where [p] is
      evidence for [P] and [q] is evidence for [Q]. 

   Since we'll be using conjunction a lot, let's introduce a more
   familiar-looking infix notation for it. *)

Notation "P /\ Q" := (and P Q) : type_scope.

(** (The [type_scope] annotation tells Coq that this notation
    will be appearing in propositions, not values.) *)

(** Consider the "type" of the constructor [conj]: *)

Check conj.
(* ===>  forall P Q : Prop, P -> Q -> P /\ Q *)

(** Notice that it takes 4 inputs -- namely the propositions [P]
    and [Q] and evidence for [P] and [Q] -- and returns as output the
    evidence of [P /\ Q]. *)

(** Besides the elegance of building everything up from a tiny
    foundation, what's nice about defining conjunction this way is
    that we can prove statements involving conjunction using the
    tactics that we already know.  For example, if the goal statement
    is a conjuction, we can prove it by applying the single
    constructor [conj], which (as can be seen from the type of [conj])
    solves the current goal and leaves the two parts of the
    conjunction as subgoals to be proved separately. *)

Theorem and_example : 
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
  (* Case "left". *) apply b_0.
  (* Case "right". *) apply b_3.  Qed.

(** Let's take a look at the proof object for the above theorem. *)

Print and_example. 
(* ===>  conj (beautiful 0) (beautiful 3) b_0 b_3
            : beautiful 0 /\ beautiful 3 *)

(** Note that the proof is of the form
    conj (beautiful 0) (beautiful 3) 
         (...pf of beautiful 3...) (...pf of beautiful 3...)
    as you'd expect, given the type of [conj]. *)

(** Just for convenience, we can use the tactic [split] as a shorthand for
    [apply conj]. *)

Theorem and_example' : 
  (ev 0) /\ (ev 4).
Proof.
  split.
    Case "left". apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0.  Qed.

(** Conversely, the [inversion] tactic can be used to take a
    conjunction hypothesis in the context, calculate what evidence
    must have been used to build it, and add variables representing
    this evidence to the proof context. *)

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  apply HP.  Qed.

(** **** Exercise: 1 star, optional (proj2) *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  apply HQ.  Qed.
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HP HQ]. 
  split.  
    (* Case "left". *) apply HQ. 
    (* Case "right".*) apply HP.  Qed.
  
(** Once again, we have commented out the [Case] tactics to make the
    proof object for this theorem easy to understand.  Examining it
    shows that all that is really happening is taking apart a record
    containing evidence for [P] and [Q] and rebuilding it in the
    opposite order: *)

Print and_commut.
(* ===>
   and_commut = 
     fun (P Q : Prop) (H : P /\ Q) =>
     let H0 := match H with
               | conj HP HQ => conj Q P HQ HP
               end 
     in H0
     : forall P Q : Prop, P /\ Q -> Q /\ P *)

(** **** Exercise: 2 stars (and_assoc) *)
(** In the following proof, notice how the _nested pattern_ in the
    [inversion] breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP: P], [HQ : Q], and [HR : R].  Finish the proof from there: *)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.  
     Case "left".  
       split.
       SCase "lleft".
         apply HP.
       SCase "lright".
         apply HQ.
     Case "right". apply HR.  Qed.

(** [] *)

(** **** Exercise: 2 stars, recommended (even__ev) *)
(** Now we can prove the other direction of the equivalence of [even]
   and [ev], which we left hanging in chapter [Prop].  Notice that the
   left-hand conjunct here is the statement we are actually interested
   in; the right-hand conjunct is needed in order to make the
   induction hypothesis strong enough that we can carry out the
   reasoning in the inductive step.  (To see why this is needed, try
   proving the left conjunct by itself and observe where things get
   stuck.) *)

Theorem even__ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  intros.
    induction n as [| n'].
    split.
      Case "n = 0".
      intros.
      SearchAbout ev.
      apply ev_0.
      intros.
      inversion H.
      SearchAbout ev.
      split.
      apply IHn'.
      SearchAbout ev.
      intros.
      apply ev_SS.
      apply IHn'.
      inversion H.
      apply H1.
Qed.
      
  
(** [] *)

(** **** Exercise: 2 stars, optional (conj_fact) *)
(** Construct a proof object demonstrating the following proposition. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
fun (P Q R :Prop) (H1:P /\ Q) (H2:Q /\ R) => conj P R (proj1 P Q H1) (proj2 Q R H2).
(** [] *)

(* ###################################################### *)
(** ** Iff *)

(** The familiar logical "if and only if" is just the
    conjunction of two implications. *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.  
  intros P Q H. 
  inversion H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop, 
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. 
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.

(** **** Exercise: 1 star, optional (iff_properties) *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. 
  intros.
  split.
  intros.
  apply H.
  intros.
  apply H.
Qed.

Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof. 
  intros.
  split.
  inversion H as [H'1 H'2].
  inversion H0 as [H0'1 H0'2].
  intros.
  apply H0'1.
  apply H'1.
  apply H1.
  intros.
  inversion H as [H'1 H'2].
  inversion H0 as [H0'1 H0'2].
  apply H'2.
  apply H0'2.
  apply H1.
Qed.

(** Hint: If you have an iff hypothesis in the context, you can use
    [inversion] to break it into two separate implications.  (Think
    about why this works.) *)
(** [] *)

(** **** Exercise: 2 stars, optional (beautiful_iff_gorgeous) *)

(** We have seen that the families of propositions [beautiful] and
    [gorgeous] actually characterize the same set of numbers.
    Prove that [beautiful n <-> gorgeous n] for all [n].  Just for
    fun, write your proof as an explicit proof object, rather than
    using tactics. (_Hint_: if you make use of previously defined
    theorems, you should only need a single line!) *)
SearchAbout beautiful.
Definition beautiful_iff_gorgeous :
  forall n, beautiful n <-> gorgeous n :=
  fun n=>conj (beautiful n -> gorgeous n) (gorgeous n -> beautiful n) (beautiful__gorgeous n) (gorgeous__beautiful n).
(** [] *)

(** Some of Coq's tactics treat [iff] statements specially, thus
    avoiding the need for some low-level manipulation when reasoning
    with them.  In particular, [rewrite] can be used with [iff]
    statements, not just equalities. *)

(* ############################################################ *)
(** * Disjunction *)

(** Disjunction ("logical or") can also be defined as an
    inductive proposition. *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

(** Consider the "type" of the constructor [or_introl]: *)

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

(** It takes 3 inputs, namely the propositions [P], [Q] and
    evidence of [P], and returns, as output, the evidence of [P \/ Q].
    Next, look at the type of [or_intror]: *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

(** It is like [or_introl] but it requires evidence of [Q]
    instead of evidence of [P]. *)

(** Intuitively, there are two ways of giving evidence for [P \/ Q]:

    - give evidence for [P] (and say that it is [P] you are giving
      evidence for -- this is the function of the [or_introl]
      constructor), or

    - give evidence for [Q], tagged with the [or_intror]
      constructor. *)

(** Since [P \/ Q] has two constructors, doing [inversion] on a
    hypothesis of type [P \/ Q] yields two subgoals. *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

(** From here on, we'll use the shorthand tactics [left] and [right]
    in place of [apply or_introl] and [apply or_intror]. *)

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ.  Qed.

(** **** Exercise: 2 stars, optional (or_commut'') *)
(** Try to write down an explicit proof object for [or_commut] (without
    using [Print] to peek at the ones we already defined!). *)

Definition or_commut_obj: forall P Q : Prop,
  P \/ Q  -> Q \/ P :=
  fun (P Q:Prop) (H:P \/ Q) => match H with
           | or_introl P1 => (or_intror Q P P1)
           | or_intror Q1 => (or_introl Q P Q1)
           end.

(** [] *)

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof. 
  intros P Q R. intros H. inversion H as [HP | [HQ HR]]. 
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

(** **** Exercise: 2 stars, recommended (or_distributes_over_and_2) *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros.
  inversion H.
  inversion H0.
  Case "left".
    left.
    apply H2.
  Case "right".
    inversion H1.
    SCase "left". left. apply H3.
    SCase "right". right. split. apply H2. apply H3.  Qed.
(** [] *)

(** **** Exercise: 1 star, optional (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
  Case "->".
    intros.
    inversion H.
    SCase "left".
      split.
      SSCase "lleft".
        left.
        apply H0.
      SSCase "lright".
        left.
        apply H0.
    SCase "right".
      split.
      SSCase "rleft".
        inversion H0.
          right.
          apply H1.
      SSCase "rright".
        inversion H0.
          right.
          apply H2.
  Case "<-".
    intros.
    inversion H.
    inversion H0.
    SCase "left".
      left.
      apply H2.
    SCase "right".
      inversion H1.
      SSCase "rleft".
        left.
        apply H3.
      SSCase "rright".
        right.
        split.
        SSSCase "rrleft".
          apply H2.
        SSSCase "rrright".
          apply H3.
Qed.
  
      
  
(** [] *)

(* ################################################### *)
(** ** Relating [/\] and [\/] with [andb] and [orb] *)

(** We've already seen several places where analogous structures
    can be found in Coq's computational ([Type]) and logical ([Prop])
    worlds.  Here is one more: the boolean operators [andb] and [orb]
    are clearly analogs of the logical connectives [/\] and [\/].
    This analogy can be made more precise by the following theorems,
    which show how to translate knowledge about [andb] and [orb]'s
    behaviors on certain inputs into propositional facts about those
    inputs. *)

Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

(** **** Exercise: 2 stars (bool_prop) *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. 
  intros.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". inversion H.
      SCase "c = false". right. reflexivity.
    Case "b = false". left. reflexivity.  Qed.

Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros.
  destruct b.
    Case "b = true".
      left. reflexivity.
    Case "b = false".
     destruct c.
      SCase "c = true". right. reflexivity. 
      SCase "c = false". inversion H.  Qed.
  

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  intros.
  destruct b.
    Case "b = true".
      inversion H.
    Case "b = false".
     destruct c.
      SCase "c = true". inversion H.
      SCase "c = false". split.
        SSCase "left". reflexivity. 
        SSCase "right". reflexivity. Qed.
  
(** [] *)

(* ################################################### *)
(** * Falsehood *)

(** Logical falsehood can be represented in Coq as an inductively
    defined proposition with no constructors. *)

Inductive False : Prop := . 

(** Intuition: [False] is a proposition for which there is no way
    to give evidence. *)

(** **** Exercise: 1 star (False_ind_principle) *)
(** Can you predict the induction principle for falsehood? *)

(* Check False_ind. *)
(** [] *)

(** Since [False] has no constructors, inverting an assumption
    of type [False] always yields zero subgoals, allowing us to
    immediately prove any goal. *)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof. 
  intros contra.
  inversion contra.  Qed. 

(** How does this work? The [inversion] tactic breaks [contra] into
    each of its possible cases, and yields a subgoal for each case.
    As [contra] is evidence for [False], it has _no_ possible cases,
    hence, there are no possible subgoals and the proof is done. *)

(** Conversely, the only way to prove [False] is if there is already
    something nonsensical or contradictory in the context: *)

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

(** Actually, since the proof of [False_implies_nonsense]
    doesn't actually have anything to do with the specific nonsensical
    thing being proved; it can easily be generalized to work for an
    arbitrary [P]: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from
    falsehood follows whatever you please."  This theorem is also
    known as the _principle of explosion_. *)

(* #################################################### *)
(** ** Truth *)

(** Since we have defined falsehood in Coq, one might wonder whether
    it is possible to define truth in the same way.  We can. *)

(** **** Exercise: 2 stars, optional (True_induction) *)
(** Define [True] as another inductively defined proposition.  What
    induction principle will Coq generate for your definition?  (The
    intution is that [True] should be a proposition for which it is
    trivial to give evidence.  Alternatively, you may find it easiest
    to start with the induction principle and work backwards to the
    inductive definition.) *)
(*Inductive True :Prop:= 
tr:True.
Truth_ind: forall (P:Truth->Prop), P(t) -> forall t : Truth , P m  
*)(** [] *)

(** However, unlike [False], which we'll use extensively, [True] is
    just a theoretical curiosity: it is trivial (and therefore
    uninteresting) to prove as a goal, and it carries no useful
    information as a hypothesis. *)

(* #################################################### *)
(** * Negation *)

(** The logical complement of a proposition [P] is written [not
    P] or, for shorthand, [~P]: *)

Definition not (P:Prop) := P -> False.

(** The intuition is that, if [P] is not true, then anything at
    all (even [False]) follows from assuming [P]. *)

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

(** It takes a little practice to get used to working with
    negation in Coq.  Even though you can see perfectly well why
    something is true, it can be a little hard at first to get things
    into the right configuration so that Coq can see it!  Here are
    proofs of a few familiar facts about negation to get you warmed
    up. *)

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. 
  (* WORKED IN CLASS *)
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA. 
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, recommended (double_neg_inf) *)
(** Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_:
(* FILL IN HERE *)
   []
*)

(** **** Exercise: 2 stars, recommended (contrapositive) *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H.
  unfold not.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.
(** [] *)

(** **** Exercise: 1 star (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  intros P.
  unfold not.
  intros.
  inversion H.
  apply H1.
  apply H0.
Qed.
(** [] *)

(** **** Exercise: 1 star (informal_not_PNP) *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(* FILL IN HERE *)
(** [] *)

Theorem five_not_even :  
  ~ ev 5.
Proof. 
  (* WORKED IN CLASS *)
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn]. 
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.  Qed.

(** **** Exercise: 1 star (ev_not_ev_S) *)
(** Theorem [five_not_even] confirms the unsurprising fact that five
    is not an even number.  Prove this more interesting fact: *)

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
  unfold not. intros n H. induction H. (* not n! *)
  intros.
  inversion H.
  intros.
  apply IHev.
  inversion H0.
  apply H2.
Qed.
(** [] *)

(** Note that some theorems that are true in classical logic are _not_
    provable in Coq's (constructive) logic.  E.g., let's look at how
    this proof gets stuck... *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H. 
  (* But now what? There is no way to "invent" evidence for [P]. *) 
  Admitted.

(** **** Exercise: 5 stars, optional (classical_axioms) *)
(** For those who like a challenge, here is an exercise
    taken from the Coq'Art book (p. 123).  The following five
    statements are often considered as characterizations of
    classical logic (as opposed to constructive logic, which is
    what is "built in" to Coq).  We can't prove them in Coq, but
    we can consistently add any one of them as an unproven axiom
    if we wish to work in classical logic.  Prove that these five
    propositions are equivalent. *)

Definition peirce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
  ~~P -> P.
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
  ~(~P/\~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
  (P->Q) -> (~P\/Q). 
 
Theorem peirce_classic: peirce -> classic.
Proof.
  unfold peirce, classic, not.
  intros.
  assert ((P -> False) -> P) as P_False_P.
  intros P_False.
  apply H0 in P_False.
  inversion P_False.
  apply H in P_False_P.
  apply P_False_P.
Qed.

Theorem classic_excluded_middle: classic->excluded_middle.
Proof.
  unfold classic, excluded_middle, not.
  intros.
  apply H.
  intros.
  assert ((P -> False) -> False) as P_False_False.
  intros.
  apply H0.
  right.
  apply H1.
  apply H in P_False_False.
  apply or_introl with (Q:=(P -> False)) in P_False_False.
  apply H0.
  apply P_False_False.
Qed.

Theorem excluded_middle_de_morgan_not_and_not:
  excluded_middle->de_morgan_not_and_not.
Proof.
  unfold de_morgan_not_and_not, excluded_middle, not.
  intros.
  assert (P\/~P) as exc.
   unfold not. apply H.
  inversion exc.
   left. apply H1.
   unfold not in H1.
   assert (Q\/~Q) as exc1.
    unfold not.
    apply H.
   inversion exc1.
   right. apply H2.
   unfold not in H2. apply ex_falso_quodlibet. apply H0. intuition.
Qed.

Theorem de_morgan_not_and_not_implies_to_or: 
  de_morgan_not_and_not->implies_to_or.
Proof.
  unfold de_morgan_not_and_not.
  unfold implies_to_or.
  unfold not.
  intros.
  apply H.
  intros.
  inversion H1.
  apply H2.
  intros.
  apply H3.
  apply H0.
  apply H4.
Qed.

Theorem implies_to_or_excluded_middle: 
  implies_to_or->excluded_middle.
Proof.
  unfold excluded_middle.
  unfold implies_to_or.
  unfold not.
  intros.
  SearchAbout or.
  apply or_commut.
  apply H.
  intros.
  apply H0.
Qed.


Theorem excluded_middle_peirce:
  excluded_middle->peirce.
Proof.
  unfold peirce, excluded_middle, not.
  intros.
  apply H0.
  intros.
  assert ((P->Q)\/~(P->Q)) as exc.
   unfold not. apply H.
  inversion exc.
   apply H2.
   apply H1.
   unfold not in H2.
  assert ((P -> False) -> P) as P_False_P.
  intros.
  apply H1.
  Unfold H
   
   left. apply H1.
   unfold not in H1.
   assert (Q\/~Q) as exc1.
    unfold not.
    apply H.
   inversion exc1.
   right. apply H2.
   unfold not in H2. apply ex_falso_quodlibet. apply H0. intuition.
Qed.

(** [] *)
(* ########################################################## *)
(** ** Inequality *)

(** Saying [x <> y] is just the same as saying [~(x = y)]. *)

Notation "x <> y" := (~ (x = y)) : type_scope.

(** Since inequality involves a negation, it again requires
    a little practice to be able to work with it fluently.  Here
    is one very useful trick.  If you are trying to prove a goal
    that is nonsensical (e.g., the goal state is [false = true]),
    apply the lemma [ex_falso_quodlibet] to change the goal to
    [False].  This makes it easier to use assumptions of the form
    [~P] that are available in the context -- in particular,
    assumptions of the form [x<>y]. *)

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.  
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.

(** **** Exercise: 2 stars, recommended (not_eq_beq_false) *)
Theorem not_eq_beq_false : forall n n' : nat,
     n <> n' ->
     beq_nat n n' = false.
Proof. 
  unfold not.
  intros.
  SearchAbout beq_nat.
  remember (beq_nat n n') as be.
  destruct be.
  apply ex_falso_quodlibet.
  apply H.
  SearchAbout beq_nat.
  apply beq_nat_eq.
  apply Heqbe.
  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (beq_false_not_eq) *)
Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  unfold not.
  intros.
  rewrite H0 in H.
  SearchAbout beq_nat.
  replace (beq_nat m m) with true in H.
  inversion H.
  apply beq_nat_refl.
Qed.
  
(** [] *)

(* ############################################################ *)
(** * Existential Quantification *)

(** Another critical logical connective is _existential
    quantification_.  We can capture what this means with the
    following definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

    For example, consider this existentially quantified proposition: *)

Definition some_nat_is_even : Prop := 
  ex nat ev.

(** To prove this proposition, we need to choose a particular number
    as witness -- say, 4 -- and give some evidence that that number is
    even. *)

Definition snie : some_nat_is_even := 
  ex_intro _ ev 4 (ev_SS 2 (ev_SS 0 ev_0)).

(** Coq's notation definition facility can be used to introduce
    more familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** We can use the same set of tactics as always for
    manipulating existentials.  For example, if to prove an
    existential, we [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note, again, that we have to explicitly give the witness. *)

(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, 
  n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm]. 
  exists (2 + m).  
  apply Hm.  Qed. 

(** **** Exercise: 1 star, optional (english_exists) *)
(** In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean? *)

(* Exists natural number n that beautiful (S n) provable. *)

(** Complete the definition of the following proof object: *)

Definition p : ex nat (fun n => beautiful (S n)) :=
ex_intro nat (fun n => beautiful (S n)) 2 b_3 .
  
  
(** [] *)

(** **** Exercise: 1 star (dist_not_exists) *)
(** Prove that "[P] holds for all [x]" and "there is no [x] for
    which [P] does not hold" are equivalent assertions. *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  unfold not.
  intros.
  inversion H0.
  apply H1.
  apply H.
Qed. 
(** [] *)

(** **** Exercise: 3 stars, optional (not_exists_dist) *)
(** The other direction requires the classical "law of the excluded
    middle": *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  unfold not.
  intros.
  assert (P x \/ ~P x).
  apply H.
  inversion H1.
  Case "P x".
    apply H2.
  Case "~P x".
    unfold not in H2.
    apply ex_falso_quodlibet.
    apply H0. 
    exists (x).  
    unfold not in H2.
    apply H2.
Qed.
  
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or) *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros.
  split.
  Case "->".
    intros.
    inversion H.
    inversion H0.
    SCase "P witness".
      left.
      exists witness.
      apply H1.
    SCase "Q witness".
      right.
      exists witness.
      apply H1.
  Case "->".
    intros.
    inversion H.
    SCase "exists x : X, P x".
      inversion H0.
      exists witness.
      left.
      apply H1.
    SCase "exists x : X, Q x".
      inversion H0.
      exists witness.
      right.
      apply H1.
Qed.
(** [] *)

(* Print dist_exists_or. *)



(* ###################################################### *)
(** * Equality *)

(** Even Coq's equality relation is not built in.  It has
    roughly the following inductive definition.  (We enclose the
    definition in a module to avoid confusion with the standard
    library equality, which we have used extensively already.) *)

Module MyEquality.

Inductive eq (X:Type) : X -> X -> Prop :=
  refl_equal : forall x, eq X x x.

(** Standard infix notation (using Coq's type argument synthesis): *)

Notation "x = y" := (eq _ x y) 
                    (at level 70, no associativity) : type_scope.

(** This is a bit subtle.  The way to think about it is that, given a
    set [X], it defines a _family_ of propositions "[x] is equal to
    [y]," indexed by pairs of values ([x] and [y]) from [X].  There is
    just one way of constructing evidence for members of this family:
    applying the constructor [refl_equal] to a type [X] and a value [x
    : X] yields evidence that [x] is equal to [x]. *)

(** Here is a slightly different definition -- the one that actually
    appears in the Coq standard library. *)

Inductive eq' (X:Type) (x:X) : X -> Prop :=
    refl_equal' : eq' X x x.

Notation "x =' y" := (eq' _ x y) 
                     (at level 70, no associativity) : type_scope.

(** **** Exercise: 3 stars, optional (two_defs_of_eq_coincide) *)
(** Verify that the two definitions of equality are equivalent. *)

Theorem two_defs_of_eq_coincide : forall (X:Type) (x y : X),
  x = y <-> x =' y.
Proof.
  intros.
  split.
  intros.
  destruct H.
  apply refl_equal'.
  intros.
  destruct H.
  apply refl_equal.
Qed.
(** [] *)

(** The advantage of the second definition is that the induction
    principle that Coq derives for it is precisely the familiar
    principle of _Leibniz equality_: what we mean when we say "[x] and
    [y] are equal" is that every property on [P] that is true of [x]
    is also true of [y].  *)

Check eq'_ind.
(* ===> 
     forall (X : Type) (x : X) (P : X -> Prop),
       P x -> forall y : X, x =' y -> P y 

   ===>  (i.e., after a little reorganization)
     forall (X : Type) (x : X) forall y : X, 
       x =' y -> 
       forall P : X -> Prop, P x -> P y *)

(** One important consideration remains.  Clearly, we can use
    [refl_equal] to construct evidence that, for example, [2 = 2].
    Can we also use it to construct evidence that [1 + 1 = 2]?  Yes:
    indeed, it is the very same piece of evidence!  The reason is that
    Coq treats as "the same" any two terms that are _convertible_
    according to a simple set of computation rules.  These rules,
    which are similar to those used by [Eval simpl], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.
    
    In tactic-based proofs of equality, the conversion rules are
    normally hidden in uses of [simpl] (either explicit or implicit in
    other tactics such as [reflexivity]).  But you can see them
    directly at work in the following explicit proof objects: *)

Definition four : 2 + 2 = 1 + 3 :=  
  refl_equal nat 4. 

Definition singleton : forall (X:Set) (x:X), []++[x] = x::[]  :=
  fun (X:Set) (x:X) => refl_equal (list X) [x]. 

End MyEquality.

(* ####################################################### *)
(** ** Inversion, Again *)

(** We've seen [inversion] used with both equality hypotheses and
    hypotheses about inductively defined propositions.  Now that we've
    seen that these are actually the same thing, we're in a position
    to take a closer look at how [inversion] behaves...

    In general, the [inversion] tactic

    - takes a hypothesis [H] whose type [P] is inductively defined,
      and

    - for each constructor [C] in [P]'s definition,

      - generates a new subgoal in which we assume [H] was
        built with [C],

      - adds the arguments (premises) of [C] to the context of
        the subgoal as extra hypotheses,

      - matches the conclusion (result type) of [C] against the
        current goal and calculates a set of equalities that must
        hold in order for [C] to be applicable,
        
      - adds these equalities to the context (and, for convenience,
        rewrites them in the goal), and

      - if the equalities are not satisfiable (e.g., they involve
        things like [S n = O]), immediately solves the subgoal. *)

(** _Example_: If we invert a hypothesis built with [or], there are two
   constructors, so two subgoals get generated.  The
   conclusion (result type) of the constructor ([P \/ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.

   _Example_: If we invert a hypothesis built with [and], there is
   only one constructor, so only one subgoal gets generated.  Again,
   the conclusion (result type) of the constructor ([P /\ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.  The
   constructor does have two arguments, though, and these can be seen
   in the context in the subgoal.

   _Example_: If we invert a hypothesis built with [eq], there is
   again only one constructor, so only one subgoal gets generated.
   Now, though, the form of the [refl_equal] constructor does give us
   some extra information: it tells us that the two arguments to [eq]
   must be the same!  The [inversion] tactic adds this fact to the
   context.  *)

(* ####################################################### *)
(** * Relations as Propositions *)

(** A proposition parameterized by a number (such as [ev] or
    [beautiful]) can be thought of as a _property_ -- i.e., it defines
    a subset of [nat], namely those numbers for which the proposition
    is provable.  In the same way, a two-argument proposition can be
    thought of as a _relation_ -- i.e., it defines a set of pairs for
    which the proposition is provable. *)

Module LeFirstTry.  

(** We've already seen an inductive definition of one
    fundamental relation: equality.  Another useful one is the "less
    than or equal to" relation on numbers: *)

(** The following definition should be fairly intuitive.  It
    says that there are two ways to give evidence that one number is
    less than or equal to another: either observe that they are the
    same number, or give evidence that the first is less than or equal
    to the predecessor of the second. *)

Inductive le : nat -> nat -> Prop :=
  | le_n : forall n, le n n
  | le_S : forall n m, (le n m) -> (le n (S m)).

End LeFirstTry.

(** This is a reasonable definition of the [<=] relation, but we
    can streamline it a little by observing that the left-hand
    argument [n] is the same everywhere in the definition, so we can
    actually make it a "general parameter" to the whole definition,
    rather than an argument to each constructor.  This is similar to
    what we did in our second definition of the [eq] relation,
    above. *)

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

(** The second one is better, even though it looks less symmetric.
    Why?  Because it gives us a simpler induction principle. 
    (The same was true of our second version of [eq].) *)

Check le_ind.
(* ===>  forall (n : nat) (P : nat -> Prop),
           P n ->
           (forall m : nat, n <= m -> P m -> P (S m)) ->
           forall n0 : nat, n <= n0 -> P n0 *)

(** By contrast, the induction principle that Coq calculates for the
    first definition has a lot of extra quantifiers, which makes it
    messier to work with when proving things by induction.  Here is
    the induction principle for the first [le]: *)

(* le_ind : 
     forall P : nat -> nat -> Prop,
     (forall n : nat, P n n) ->
     (forall n m : nat, le n m -> P n m -> P n (S m)) ->
     forall n n0 : nat, le n n0 -> P n n0 *)

(** Proofs of facts about [<=] using the constructors [le_n] and
    [le_S] follow the same patterns as proofs about properties, like
    [ev] in chapter [Prop].  We can [apply] the constructors to prove [<=]
    goals (e.g., to show that [3<=3] or [3<=6]), and we can use
    tactics like [inversion] to extract information from [<=]
    hypotheses in the context (e.g., to prove that [~(2 <= 1)].) *)

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
  ~ (2 <= 1).
Proof. 
  (* WORKED IN CLASS *)
  intros H. inversion H. inversion H1.  Qed.

(** The "strictly less than" relation [n < m] can now be defined
    in terms of [le]. *)

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** Here are a few more simple relations on numbers: *)

Inductive square_of : nat -> nat -> Prop :=
  sq : forall n:nat, square_of n (n * n).

Inductive next_nat (n:nat) : nat -> Prop :=
  | nn : next_nat n (S n).

Inductive next_even (n:nat) : nat -> Prop :=
  | ne_1 : ev (S n) -> next_even n (S n)
  | ne_2 : ev (S (S n)) -> next_even n (S (S n)).

(** **** Exercise: 2 stars, recommended (total_relation) *)
(** Define an inductive binary relation [total_relation] that holds
    between every pair of natural numbers. *)

Inductive total_relation : nat -> nat->Prop :=
  total_relation1:forall n m:nat, total_relation n m.

(** [] *)

(** **** Exercise: 2 stars (empty_relation) *)
(** Define an inductive binary relation [empty_relation] (on numbers)
    that never holds. *)
Inductive empty_relation: nat -> nat -> Prop := .
(** [] *)

(** **** Exercise: 3 stars, recommended (R_provability) *)
Module R.
(** We can define three-place relations, four-place relations,
    etc., in just the same way as binary relations.  For example,
    consider the following three-place relation on numbers: *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0 
   | c2 : forall m n o, R m n o -> R (S m) n (S o)
   | c3 : forall m n o, R m n o -> R m (S n) (S o)
   | c4 : forall m n o, R (S m) (S n) (S (S o)) -> R m n o
   | c5 : forall m n o, R m n o -> R n m o.

(** - Which of the following propositions are provable?
      - [R 1 1 2] 
      - [R 2 2 6]

    - If we dropped constructor [c5] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.
  
    - If we dropped constructor [c4] from the definition of [R],
      would the set of provable propositions change?  Briefly (1
      sentence) explain your answer.

(*
      - [R 1 1 2] provable c2 c3 c1
      - [R 2 2 6] not provable 2+2 <>6
      c4 and c5 are useless.
      We need only c2 and c3 to reduce m, n and o to 0. Then we can use c1.  
*)
[]
*)

(** **** Exercise: 3 stars, optional (R_fact) *)  
(** State and prove an equivalent characterization of the relation
    [R].  That is, if [R m n o] is true, what can we say about [m],
    [n], and [o], and vice versa?
*)

Theorem RT1 : forall n, R 0 n n.
Proof.
  intros.
  induction n as [| n'].
  SSCase "n = 0".
    apply c1.
  SSCase "n = S n'".
    apply c3.
    apply IHn'.
Qed.
Theorem RT2 : forall n m, R n m (n+m).
Proof.
  intros.
  induction n as [| n'].
  SSCase "n = 0".
    apply RT1.
  SSCase "n = S n'".
    apply c2.
    apply IHn'.
Qed.

Theorem RT : forall m n o,
  R m n o <-> m+n=o.
Proof.
  split.
  Case "->".
    intros.
    induction H.
    reflexivity.
    rewrite <- IHR.
    reflexivity.
    rewrite <- IHR.
    rewrite plus_n_Sm.
    reflexivity.
    inversion IHR.
    rewrite <- plus_n_Sm in H1.
    inversion H1.
    reflexivity.
    rewrite plus_comm.
    apply IHR.
  Case "->".
    intros.
    rewrite <- H.
    apply RT2.
Qed.
    
      


End R.

(** **** Exercise: 3 stars, recommended (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  |all0 : all X P []
  |all1 : forall h l, P h -> all X P l -> all X P (h::l). 


(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)
SearchAbout bool.
Theorem forallbT : forall (X : Type) (test : X -> bool) (l : list X) , 
  forallb test l=true<->all X (fun n=>test n=true) l.
Proof.
  split.
  Case "->".
    intros.
    induction l as [| h l'].
    SCase "l=[]".
      apply all0.
    SCase "l=h::l'".
      apply all1.
      simpl in H.
      SearchAbout andb.
      rewrite andb_true_elim1 with (b:=test h) (c:=forallb test l').
      reflexivity.
      apply H.
      apply IHl'.
      rewrite andb_true_elim2 with (b:=test h) (c:=forallb test l').
      reflexivity.
      apply H.
  Case "<-".
    intros.
    induction H.
    SCase "all0".
      reflexivity.
    SCase "all1".
      simpl.
      rewrite H.
      simpl.
      apply IHall.
Qed.
(** [] *)

(** **** Exercise: 4 stars, optional (filter_challenge) *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
    [1,4,6,2,3]
    is an in-order merge of
    [1,6,2]
    and
    [4,3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)


Inductive mrg (X : Type) (P : X -> Prop) : list X -> list X -> list X -> Prop :=
  |mrg0 : mrg X P [] [] []
  |mrg1 : forall h l1 l2 l3, P h -> mrg X P l1 l2 l3 -> mrg X P (h::l1) (h::l2) l3
  |mrg2 : forall h l1 l2 l3, ~P h -> mrg X P l1 l2 l3 -> mrg X P (h::l1) l2 (h::l3). 


Theorem mrgT : forall (X : Type) (test : X -> bool) (l1 l2 l3 : list X) , 
  mrg X (fun n=>test n=true) l1 l2 l3->  filter test l1=l2.
Proof.
  intros.
    induction H.
    Case "mrg0".
      simpl.
      reflexivity.
    Case "mrg1".
      simpl.
      rewrite H.
      rewrite IHmrg.
      reflexivity.
    Case "mrg2".
      simpl.
      unfold not in H.
      remember (test h) as t.
      destruct t.
      SCase "true".
        apply ex_falso_quodlibet.
        apply H.
        reflexivity.
      SCase "false".
        apply IHmrg.
Qed.
    
(** [] *)

(** **** Exercise: 5 stars, optional (filter_challenge_2) *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

Inductive subs (X : Type): list X -> list X -> Prop :=
  |subs0 : subs X [] []
  |subs1 : forall h l1 l2, subs X l1 l2 -> subs X (h::l1) (h::l2)
  |subs2 : forall h l1 l2, subs X l1 l2 -> subs X l1 (h::l2). 
Theorem leT :forall n1 n2, n1<=n2->S n1<= S n2.
  Proof.
    intros.
    induction H.
      apply le_n.
      apply le_S.
      apply IHle.
Qed.


Theorem fT : forall (X : Type) (test : X -> bool) (l1 l2: list X) , 
  ((subs X l1 l2)/\forallb test l1=true)->((length l1) <= length (filter test l2)).
  Proof.
    intros.
    induction H.
    induction H.
    Case "subs0".
      simpl.
      apply le_n.
    Case "subs1".
      simpl.
      remember (test h) as t.
      destruct t.
      SCase "true".
        simpl.
        apply leT.
        apply IHsubs.
        inversion H0.
        rewrite H2.
        rewrite <- Heqt in H2.
        simpl in H2.
        apply H2.
      SCase "false".
        simpl in H0.
        rewrite <- Heqt in H0.
        inversion H0.        
    Case "subs2".
      simpl.
      remember (test h) as t.
      destruct t.
      SCase "true".
        simpl.
        apply le_S.
        apply IHsubs.
        apply H0.
      SCase "false".
        apply IHsubs.
        apply H0.
Qed.    
      
      
(** [] *)

(** **** Exercise: 4 stars, optional (no_repeats) *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

Theorem app_nil_end : forall (X:Type) (l : list X), l++[]=l.
Proof.
  intros.
  induction l. 
  reflexivity.
  rewrite<- IHl at 2.
  simpl.
  reflexivity.
Qed.    
  
(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 

    Here's a pair of warm-ups about [appears_in].
*)
Lemma appears_in_app : forall {X:Type} (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.

Proof.
  intros X.
  induction xs.
  simpl.
  intros.
  right.
  apply H.
  induction ys.
  simpl.
  rewrite app_nil_end.
  intros.
  left.
  apply H.
  intros.
  inversion H.
  
  Case "ai_here".
    left.
    apply ai_here.
  Case "ai_later".
    subst.
apply IHxs in H1. 
inversion H1.
  left.
    apply ai_later.
    apply H0.
    right.
    apply H0.
Qed.

Lemma app_appears_in : forall {X:Type} (xs ys : list X) (x:X), 
     appears_in x xs \/ appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros.
  inversion H.
  Case "left".
    induction xs.
    SCase "xs=[]".
      inversion H0.
    SCase "xs=x0 :: xs".
      inversion H0.
      apply ai_here.
      apply ai_later.
      apply IHxs.
      left.
      apply H2.
      apply H2.
  Case "right".
    induction xs.
    SCase "xs=[]".
      apply H0.
    SCase "xs=x0 :: xs".
      apply ai_later.
      apply IHxs.
      right.
      apply H0.
Qed.
  
(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)


Inductive disjoint {X:Type} : list X -> list X -> Prop :=
  | disjoint0 : forall l, disjoint [] l
  | disjoint1 : forall h l1 l2, ~appears_in h l2 -> disjoint l1 l2 -> disjoint (h::l1) l2
  | disjoint2 : forall h l1 l2, ~appears_in h l1 -> disjoint l1 l2 -> disjoint l1 (h::l2).

(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)


Inductive no_repeats {X:Type} : list X -> Prop :=
  | no_repeats0 : no_repeats []
  | no_repeats1 : forall h l, ~appears_in h l-> no_repeats (l) -> no_repeats (h::l).
(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)

(** [] *)

(* ######################################################### *)
(** ** Digression: More Facts about [<=] and [<] *)

(** Let's pause briefly to record several facts about the [<=]
    and [<] relations that we are going to need later in the
    course.  The proofs make good practice exercises. *)

(** **** Exercise: 2 stars, optional (le_exercises) *)
Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros.
  induction n as [|n'].
  Case "n=0".
    apply le_n.
  Case "n=S n'".
    apply le_S.
    apply IHn'.
Qed.
    

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof. 
  apply leT.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof. 
  intros n m.  generalize dependent n.  induction m.
  Case "m=0".
    intros.
    destruct n.
    SCase "n=0".
      apply le_n.
    SCase "n=S n'".
      inversion H.
      inversion H1.
  Case "m=S m'".
    intros.
    destruct n.
    SCase "n=0".
      apply le_S.
      apply IHm.
      inversion H.
      apply H1.
    SCase "n=S n'".
      inversion H.
      apply le_n.
      apply le_S.
      apply IHm.
      apply H1.
Qed.

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof. 
  intros.
  rewrite plus_comm.
  induction b as [| b'].
  Case "b=0".
    apply le_n.
  Case "b=S b'".
    apply le_S.
    apply IHb'.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof. 
  unfold lt.
  intros.
  induction H.
  Case "le_n".
    split.
    SCase "left".
      replace (S (n1 + n2)) with (S n1 + n2).
      apply le_plus_l.
      simpl.
      reflexivity.
    SCase "right".
      rewrite plus_comm.
      replace (S (n2 + n1)) with (S n2 + n1).
      apply le_plus_l.
      simpl.
      reflexivity.
  Case "le_S".
    inversion IHle.
    split.
    SCase "left".
      apply le_S.
      apply H0.
    SCase "right".
      apply le_S.
      apply H1.
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
  
Theorem ble_nat_true : forall n m,
  ble_nat n m = true -> n <= m.
Proof. 
  unfold lt.
  intros.
  generalize dependent m. 
  induction n.
  Case "n=0".
    intros.
    replace (m) with (0 + m).
    apply le_plus_l.
    simpl.
    reflexivity.
  Case"n=S n".
    intros.
    destruct m.
    SCase"m=0".
      inversion H.
    SCase"m=S m".
      apply n_le_m__Sn_le_Sm.
      apply IHn.  
      simpl in H.
      apply H.
Qed.

Theorem ble_nat_n_Sn_false : forall n m,
  ble_nat n (S m) = false ->
  ble_nat n m = false.
Proof. 
  intros.
  generalize dependent n. 
  induction m.
  Case "m=0".
    intros.
    destruct n.
    SCase"n=0".
      inversion H.
    SCase"n=S n".
    simpl.
    reflexivity.
  Case"m=S m".
    intros.
    destruct n.
    SCase"n=0".
      inversion H.
    SCase"n=S n".
      simpl.
      apply IHm.
      simpl in H.
      apply H.
Qed.

Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  (* Hint: Do the right induction! *)

  unfold not.
  intros. 
  generalize dependent n. 
  induction m.
  Case "m=0".
    intros.
    destruct n.
    SCase"n=0".
      inversion H.
    SCase"n=S n".
      inversion H0.
  Case"m=S m".
    intros.
    destruct n.
    SCase"n=0".
      inversion H.
    SCase"n=S n".
      apply Sn_le_Sm__n_le_m in H0.
      apply IHm with (n:=n).
      simpl in H.
      apply H.
      apply H0.
Qed.
(** [] *)

(** **** Exercise: 3 stars, recommended (nostutter) *)
(** Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all (except from your study group partner, if
    you have one).

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1,4,1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
  | nostutter0 : nostutter []
  | nostutter1 : forall n, nostutter [n]
  | nostutter2 : forall n m l, ~n=m -> nostutter (m::l)->nostutter(n::m::l)
.

(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3,1,4,1,5,6].
(*
  apply nostutter2.
  unfold not.
  intros.
  inversion H.
  apply nostutter2.
  unfold not.
  intros.
  inversion H.
  apply nostutter2.
  unfold not.
  intros.
  inversion H.
  apply nostutter2.
  unfold not.
  intros.
  inversion H.
  apply nostutter2.
  unfold not.
  intros.
  inversion H.
  apply nostutter1.
 Qed.*) Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.
(* 
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.
*)

Example test_nostutter_2:  nostutter [].
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_3:  nostutter [5].
  Proof. repeat constructor; apply beq_false_not_eq; auto. Qed.

Example test_nostutter_4:      not (nostutter [3,1,1,4]).
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.
(** [] *)

(** **** Exercise: 4 stars, optional (pigeonhole principle) *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas... (we already proved this for lists
    of naturals, but not for arbitrary lists.) *)

Lemma app_length : forall {X:Type} (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros.
  induction l1 as [|h l1'].
  Case "l1=[]".
    reflexivity.
  Case "l1=h::l1'".
    simpl.
    rewrite IHl1'.
    reflexivity.
Qed.

Lemma appears_in_app_split : forall {X:Type} (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros.
  induction l as [|h l'].
  Case "l=[]".
    inversion H.
  Case "l=h::l'".
    induction H.
    SCase "ai_here".
      exists [].
      exists l.
      reflexivity.
    SCase "ai_later".
      inversion IHappears_in.
      inversion H0.
      exists (b::witness).
      exists witness0.
      rewrite H1.
      reflexivity.
Qed.

    
    

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  repeats0 : forall l1 l2 l3 x,repeats (l1++(x::l2)++(x::l3))
.

(** Now here's a way to formalize the pigeonhole principle. List [l2]
   represents a list of pigeonhole labels, and list [l1] represents an
   assignment of items to labels: if there are more items than labels,
   at least two items must have the same label.  You will almost
   certainly need to use the [excluded_middle] hypothesis. *)


Theorem app_nil : forall {X:Type} (l:list X), 
   l ++ [] = l.
Proof.
   intros.
   induction l.
   Case "l = nil".
     reflexivity.
   Case "l = cons n l1'".
     simpl. rewrite IHl. reflexivity. Qed.

Theorem app_ass : forall {X:Type} (l1 l2 l3:list X), 
   (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
   intros X l1 l2 l3. induction l1 as [| n l1'].
   Case "l1 = nil".
     reflexivity.
   Case "l1 = cons n l1'".
     simpl. rewrite -> IHl1'. reflexivity. Qed.


Theorem app_dist : forall {X:Type} x (l1 l2:list X), 
   x::(l1 ++ l2) = (x::l1) ++ l2.
Proof.
   intros. induction l1 as [| n l1'].
   Case "l1 = nil".
     reflexivity.
   Case "l1 = cons n l1'".
     simpl. reflexivity. Qed.

Theorem app_dist1 : forall {X:Type} x (l1 l2 l3:list X), 
   x::(l1 ++ l2)++l3 = x::l1 ++ l2++l3.
Proof.
   intros.
   rewrite <-app_ass.
   reflexivity.
 Qed.

Theorem rep1:forall {X:Type} x (l:list X),
  excluded_middle -> 
  repeats (x::l)->repeats (l++[x]).
Proof. 
  intros.
  inversion H0.
  induction l.
  rewrite <- H2.
  simpl.
  apply repeats0.
  destruct l1.
  inversion H2.
  replace ((l2 ++ x :: l3) ++ [x]) with (l2 ++ (x :: l3) ++ ([x])).
  apply repeats0.
  simpl.
  rewrite app_ass.
  reflexivity.
  inversion H2.
  replace ((l1 ++ x0 :: l2 ++ x0 :: l3) ++ [x]) with (l1 ++ (x0 :: l2) ++ (x0 :: l3 ++ [x])).
  apply repeats0.
  simpl.
  rewrite app_ass.
  replace ((x0 :: l2 ++ x0 :: l3) ++ [x]) with (x0 :: l2 ++ x0 :: l3 ++ [x]).
  reflexivity.
  simpl.
  rewrite app_dist1.
  rewrite <- app_dist.
  reflexivity.
 Qed.

Theorem app_dist2 : forall {X:Type} x1 x2 (l1 l2 :list X), 
   l1++[x1] = l2++[x2] ->x1=x2.
Proof. 
  intros X x1 x2 l1.
  induction l1.
  intros.
  inversion H.
  destruct l2.
  inversion H.
  reflexivity.
  inversion H1.
  destruct l2.
  inversion H3.
  inversion H3.
  intros.
  destruct l2.
  inversion H.
  destruct l1.
  inversion H2.
  inversion H2.
  inversion H.
  apply IHl1 with (l2:=l2).
  apply H2.
 Qed.

Theorem app_eq :forall {X:Type} x (l1 l2 :list X), 
   x::l1 = x::l2 <->l1=l2.
Proof. 

  intros X x1 x2 l1.
  split.
  induction l1.
  intros.
  inversion H.
  reflexivity.
  intros.
  inversion H.
  reflexivity.

  intros.
  rewrite H.
  reflexivity.
 Qed.
  

Theorem app_dist3 : forall {X:Type} x1 x2 (l1 l2 :list X), 
   l1++[x1] = l2++[x2] ->l1=l2.
Proof. 
  intros X x1 x2 l1.
  induction l1.
  intros.
  inversion H.
  destruct l2.
  inversion H.
  reflexivity.
  inversion H1.
  destruct l2.
  inversion H3.
  inversion H3.
  intros.
  destruct l2.
  inversion H.
  destruct l1.
  inversion H2.
  inversion H2.
  inversion H.
  apply app_eq.
  apply IHl1.
  apply H2.
 Qed.
  
Fixpoint wlast {X:Type} : .

Theorem tl_intr : forall {X:Type} x1 x2 (l1 l2 :list X), 
   x1::l1 = l2++[x2] ->tl(x1::l1)=l2(*\/x1=x2*).
Proof.
  intros.
  induction l2.
  destruct l1.
  simpl.
  reflexivity.
  inversion H.
  


Theorem rep2:forall {X:Type} x (l:list X),
  excluded_middle ->repeats (l++[x])-> 
  repeats (x::l).
Proof. 
  intros.
  inversion H0.
  destruct l3.
  replace (l1 ++ x0 :: l2 ++ [x0]) with ((l1 ++ x0 :: l2) ++ [x0]) in H2.
  inversion H2.
  apply app_dist2 in H2.
  inversion H3.
  apply app_dist3 in H3.
  rewrite <- H2.
  rewrite <- H3.
  replace (x0 :: l1 ++ x0 :: l2) with ([]++(x0 :: l1) ++ x0 :: l2).
  apply repeats0.
  simpl.
  reflexivity.
  rewrite app_ass.
  rewrite app_dist.
  reflexivity.
  
  destruct l1.
  inversion H2.
  apply app_dist2 in H4.
  rewrite H4.
  replace (x :: x :: l) with ([]++ (x :: []) ++x :: l).
  apply repeats0.
  simpl.
  reflexivity.
  apply app_dist2 in H3.
  replace ((l1 ++ x0 :: l2 ++ x0 :: l3) ++ [x]) with (l1 ++ (x0 :: l2) ++ (x0 :: l3 ++ [x])).
  apply repeats0.
  simpl.
  rewrite app_ass.
  replace ((x0 :: l2 ++ x0 :: l3) ++ [x]) with (x0 :: l2 ++ x0 :: l3 ++ [x]).
  reflexivity.
  simpl.
  rewrite app_dist1.
  rewrite <- app_dist.
  reflexivity.
 Qed.

Theorem rep2:forall {X:Type} (l1 l2:list X),
  excluded_middle -> 
  repeats (l1++l2)->repeats (l2++l1).
Proof. 
  intros.
  inversion H0.
  generalize dependent l1. 
  induction l2.
  intros.
  rewrite app_nil in H2. 
  rewrite <- H2.
  simpl.
  apply repeats0.
  intros.
  rewrite <- app_dist.
  apply rep1.
  destruct l1.
  inversion H2.
  replace ((l2 ++ x :: l3) ++ [x]) with (l2 ++ (x :: l3) ++ ([x])).
  apply repeats0.
  simpl.
  rewrite app_ass.
  reflexivity.
  inversion H2.
  replace ((l1 ++ x0 :: l2 ++ x0 :: l3) ++ [x]) with (l1 ++ (x0 :: l2) ++ (x0 :: l3 ++ [x])).
  apply repeats0.
  simpl.
  rewrite app_ass.
  replace ((x0 :: l2 ++ x0 :: l3) ++ [x]) with (x0 :: l2 ++ x0 :: l3 ++ [x]).
  reflexivity.
  simpl.
  rewrite app_dist1.
  rewrite <- app_dist.
  reflexivity.
 Qed.
  
Theorem rep1:forall {X:Type} (l1 l2 l3:list X),
  excluded_middle -> 
  repeats (l1++l3)->repeats (l1++l2++l3).
Proof. 
  intros.
  induction l1.
  Case "l1=[]".
    inversion H0.
    simpl in H1.
    rewrite <- H1.
    simpl.
    replace (l2 ++ l1 ++ x :: l0 ++ x :: l4) with ((l2 ++ l1 )++ (x :: l0) ++( x :: l4)).
    apply repeats0.
    simpl.
    apply app_ass.
  Case "l1=x::l1".
    inversion H0.
    assert (x=x0\/~x=x0).
    apply H.
    inversion H1.
    rewrite <- H3 in H2.
    

Theorem repAp:forall {X:Type} (x:X) (l:list X),
  appears_in x l->repeats (x::l).
Proof. 
  intros. 
  induction H.
  Case "ap_here".
    replace (x :: x :: l) with ([]++(x::[])++(x::l)).
    apply repeats0.
    simpl.
    reflexivity.
  Case "ap_later".

Theorem pigeonhole_principle: forall {X:Type} (l1 l2:list X),
  excluded_middle -> 
  (forall x, appears_in x l1 -> appears_in x l2) -> 
  length l2 < length l1 -> 
  repeats l1.  
Proof.  intros X l1. induction l1.
  Case "l1=[]".
    intros.
    simpl in H1.
    inversion H1.
  Case "l1=x::l1".
    intros.
    assert (appears_in x l1 \/ ~appears_in x l1).
    apply H.
    inversion H2.
    SCase "appears_in x l1".
      inversion H3.
      replace (x :: x :: l) with ([]++(x::[])++(x::l)).
      apply repeats0.
      simpl.
      reflexivity.
    SCase "~appears_in x l1".
    apply repeats0.
    unfold not.
    intros.
    destruct l2.
    apply H0.
    apply repeats0 in IHl1.
(** [] *)

(* ####################################################### *)
(** * Informal Proofs *)

(** Q: What is the relation between a formal proof of a proposition
       [P] and an informal proof of the same proposition [P]?

    A: The latter should _teach_ the reader how to produce the
       former.

    Q: How much detail is needed?

    A: There is no single right answer; rather, there is a range
       of choices.  

      At one end of the spectrum, we can essentially give the
      reader the whole formal proof (i.e., the informal proof
      amounts to just transcribing the formal one into words).
      This gives the reader the _ability_ to reproduce the formal
      one for themselves, but it doesn't _teach_ them anything.

      At the other end of the spectrum, we can say "The theorem
      is true and you can figure out why for yourself if you
      think about it hard enough."  This is also not a good
      teaching strategy, because usually writing the proof
      requires some deep insights into the thing we're proving,
      and most readers will give up before they rediscover all
      the same insights as we did.

      In the middle is the golden mean -- a proof that includes
      all of the essential insights (saving the reader the hard
      part of work that we went through to find the proof in the
      first place) and clear high-level suggestions for the more
      routine parts to save the reader from spending too much
      time reconstructing these parts (e.g., what the IH says and
      what must be shown in each case of an inductive proof), but
      not so much detail that the main ideas are obscured. 

   Another key point: if we're talking about a formal proof of a
   proposition P and an informal proof of P, the proposition P doesn't
   change.  That is, formal and informal proofs are _talking about the
   same world_ and they _must play by the same rules_. *)

(* ####################################################### *)
(** ** Informal Proofs by Induction *)

(** Since we've spent much of this chapter looking "under the hood" at
    formal proofs by induction, now is a good moment to talk a little
    about _informal_ proofs by induction.

    In the real world of mathematical communication, written proofs
    range from extremely longwinded and pedantic to extremely brief
    and telegraphic.  The ideal is somewhere in between, of course,
    but while you are getting used to the style it is better to start
    out at the pedantic end.  Also, during the learning phase, it is
    probably helpful to have a clear standard to compare against.
    With this in mind, we offer two templates below -- one for proofs
    by induction over _data_ (i.e., where the thing we're doing
    induction on lives in [Type]) and one for proofs by induction over
    _evidence_ (i.e., where the inductively defined thing lives in
    [Prop]).  In the rest of this course, please follow one of the two
    for _all_ of your inductive proofs. *)

(** *** Induction Over an Inductively Defined Set *)
 
(** _Template_: 

       - _Theorem_: <Universally quantified proposition of the form
         "For all [n:S], [P(n)]," where [S] is some inductively defined
         set.>

         _Proof_: By induction on [n].

           <one case for each constructor [c] of [S]...>

           - Suppose [n = c a1 ... ak], where <...and here we state
             the IH for each of the [a]'s that has type [S], if any>.
             We must show <...and here we restate [P(c a1 ... ak)]>.

             <go on and prove [P(n)] to finish the case...>

           - <other cases similarly...>                        []
 
    _Example_:
 
      - _Theorem_: For all sets [X], lists [l : list X], and numbers
        [n], if [length l = n] then [index (S n) l = None].

        _Proof_: By induction on [l].

        - Suppose [l = []].  We must show, for all numbers [n],
          that, if length [[] = n], then [index (S n) [] =
          None].

          This follows immediately from the definition of index.

        - Suppose [l = x :: l'] for some [x] and [l'], where
          [length l' = n'] implies [index (S n') l' = None], for
          any number [n'].  We must show, for all [n], that, if
          [length (x::l') = n] then [index (S n) (x::l') =
          None].

          Let [n] be a number with [length l = n].  Since
            length l = length (x::l') = S (length l'),
          it suffices to show that 
            index (S (length l')) l' = None.
]]  
          But this follows directly from the induction hypothesis,
          picking [n'] to be length [l'].  [] *)
 
(** *** Induction Over an Inductively Defined Proposition *)

(** Since inductively defined proof objects are often called
    "derivation trees," this form of proof is also known as _induction
    on derivations_. 

    _Template_:
 
       - _Theorem_: <Proposition of the form "[Q -> P]," where [Q] is
         some inductively defined proposition (more generally,
         "For all [x] [y] [z], [Q x y z -> P x y z]")>

         _Proof_: By induction on a derivation of [Q].  <Or, more
         generally, "Suppose we are given [x], [y], and [z].  We
         show that [Q x y z] implies [P x y z], by induction on a
         derivation of [Q x y z]"...>

           <one case for each constructor [c] of [Q]...>

           - Suppose the final rule used to show [Q] is [c].  Then
             <...and here we state the types of all of the [a]'s
             together with any equalities that follow from the
             definition of the constructor and the IH for each of
             the [a]'s that has type [Q], if there are any>.  We must
             show <...and here we restate [P]>.

             <go on and prove [P] to finish the case...>

           - <other cases similarly...>                        []

    _Example_
 
       - _Theorem_: The [<=] relation is transitive -- i.e., for all
         numbers [n], [m], and [o], if [n <= m] and [m <= o], then
         [n <= o].

         _Proof_: By induction on a derivation of [m <= o].

           - Suppose the final rule used to show [m <= o] is
             [le_n]. Then [m = o] and we must show that [n <= m],
             which is immediate by hypothesis.

           - Suppose the final rule used to show [m <= o] is
             [le_S].  Then [o = S o'] for some [o'] with [m <= o'].
             We must show that [n <= S o'].
             By induction hypothesis, [n <= o'].

             But then, by [le_S], [n <= S o'].  [] *)

(* ##################################################### *)
(** * Optional Material *)

(* ################################################### *)
(** ** Induction Principles for [/\] and [\/] *)

(** The induction principles for conjunction and disjunction are a
    good illustration of Coq's way of generating simplified induction
    principles for [Inductive]ly defined propositions, which we
    discussed in the last chapter.  You try first: *)

(** **** Exercise: 1 star, optional (and_ind_principle) *)
(** See if you can predict the induction principle for conjunction. *)

(* Check and_ind. *)
(** [] *)

(** **** Exercise: 1 star, optional (or_ind_principle) *)
(** See if you can predict the induction principle for disjunction. *)

(* Check or_ind. *)
(** [] *)

Check and_ind.

(** From the inductive definition of the proposition [and P Q]
     Inductive and (P Q : Prop) : Prop :=
       conj : P -> Q -> (and P Q).
    we might expect Coq to generate this induction principle
     and_ind_max :
       forall (P Q : Prop) (P0 : P /\ Q -> Prop),
            (forall (a : P) (b : Q), P0 (conj P Q a b)) ->
            forall a : P /\ Q, P0 a
    but actually it generates this simpler and more useful one:
     and_ind :
       forall P Q P0 : Prop,
            (P -> Q -> P0) ->
            P /\ Q -> P0
    In the same way, when given the inductive definition of [or P Q]
     Inductive or (P Q : Prop) : Prop :=
       | or_introl : P -> or P Q
       | or_intror : Q -> or P Q.
    instead of the "maximal induction principle"
     or_ind_max :
       forall (P Q : Prop) (P0 : P \/ Q -> Prop),
            (forall a : P, P0 (or_introl P Q a)) ->
            (forall b : Q, P0 (or_intror P Q b)) ->
            forall o : P \/ Q, P0 o
    what Coq actually generates is this:
     or_ind :
       forall P Q P0 : Prop,
            (P -> P0) ->
            (Q -> P0) ->
            P \/ Q -> P0
]] 
*)

(* ######################################################### *)
(** ** Explicit Proof Objects for Induction *)


(** Although tactic-based proofs are normally much easier to
    work with, the ability to write a proof term directly is sometimes
    very handy, particularly when we want Coq to do something slightly
    non-standard.  *)
    
(** Recall the induction principle on naturals that Coq generates for
    us automatically from the Inductive declation for [nat]. *)

(* Check nat_ind. *)
(* ===> 
   nat_ind : forall P : nat -> Prop,
      P 0%nat -> 
      (forall n : nat, P n -> P (S n)) -> 
      forall n : nat, P n  *)

(** There's nothing magic about this induction lemma: it's just
   another Coq lemma that requires a proof.  Coq generates the proof
   automatically too...  *)
 
Print nat_ind.  
(* ===> (after some manual tidying)
   nat_ind =
    fun (P : nat -> Type) 
        (f : P 0) 
        (f0 : forall n : nat, P n -> P (S n)) =>
          fix F (n : nat) : P n :=
             match n as n0 return (P n0) with
            | 0 => f
            | S n0 => f0 n0 (F n0)
            end.
*)

(** We can read this as follows: 
     Suppose we have evidence [f] that [P] holds on 0,  and 
     evidence [f0] that [forall n:nat, P n -> P (S n)].  
     Then we can prove that [P] holds of an arbitrary nat [n] via 
     a recursive function [F] (here defined using the expression 
     form [Fix] rather than by a top-level [Fixpoint] 
     declaration).  [F] pattern matches on [n]: 
      - If it finds 0, [F] uses [f] to show that [P n] holds.
      - If it finds [S n0], [F] applies itself recursively on [n0] 
         to obtain evidence that [P n0] holds; then it applies [f0] 
         on that evidence to show that [P (S n)] holds. 
    [F] is just an ordinary recursive function that happens to 
    operate on evidence in [Prop] rather than on terms in [Set].
 
    Aside to those interested in functional programming: You may
    notice that the [match] in [F] requires an annotation [as n0
    return (P n0)] to help Coq's typechecker realize that the two arms
    of the [match] actually return the same type (namely [P n]).  This
    is essentially like matching over a GADT (generalized algebraic
    datatype) in Haskell.  In fact, [F] has a _dependent_ type: its
    result type depends on its argument; GADT's can be used to
    describe simple dependent types like this.
 
    We can adapt this approach to proving [nat_ind] to help prove
    _non-standard_ induction principles too.  Recall our desire to
    prove that

    [forall n : nat, even n -> ev n].
 
    Attempts to do this by standard induction on [n] fail, because the
    induction principle only lets us proceed when we can prove that
    [even n -> even (S n)] -- which is of course never provable.  What
    we did earlier in this chapter was a bit of a hack:
 
    [Theorem even__ev : forall n : nat,
     (even n -> ev n) /\ (even (S n) -> ev (S n))].
 
    We can make a much better proof by defining and proving a
    non-standard induction principle that goes "by twos":
 
 *)
 
 Definition nat_ind2 : 
    forall (P : nat -> Prop), 
    P 0 -> 
    P 1 -> 
    (forall n : nat, P n -> P (S(S n))) -> 
    forall n : nat , P n :=
       fun P => fun P0 => fun P1 => fun PSS => 
          fix f (n:nat) := match n return P n with 
                             0 => P0 
                           | 1 => P1 
                           | S (S n') => PSS n' (f n') 
                          end.
 
 (** Once you get the hang of it, it is entirely straightforward to
     give an explicit proof term for induction principles like this.
     Proving this as a lemma using tactics is much less intuitive (try
     it!).

     The [induction ... using] tactic gives a convenient way to
     specify a non-standard induction principle like this. *)
 
Lemma even__ev' : forall n, even n -> ev n.
Proof. 
 intros.  
 induction n as [ | |n'] using nat_ind2. 
  Case "even 0". 
    apply ev_0.  
  Case "even 1". 
    inversion H.
  Case "even (S(S n'))". 
    apply ev_SS. 
    apply IHn'.  unfold even.  unfold even in H.  simpl in H. apply H. 
Qed. 

(* ######################################################### *)
(** ** The Coq Trusted Computing Base *)

(** One issue that arises with any automated proof assistant is "why
    trust it?": what if there is a bug in the implementation that
    renders all its reasoning suspect?

    While it is impossible to allay such concerns completely, the fact
    that Coq is based on the Curry-Howard Correspondence gives it a
    strong foundation. Because propositions are just types and proofs
    are just terms, checking that an alleged proof of a proposition is
    valid just amounts to _type-checking_ the term.  Type checkers are
    relatively small and straightforward programs, so the "trusted
    computing base" for Coq -- the part of the code that we have to
    believe is operating correctly -- is small too.

    What must a typechecker do?  Its primary job is to make sure that
    in each function application the expected and actual argument
    types match, that the arms of a [match] expression are constructor
    patterns belonging to the inductive type being matched over and
    all arms of the [match] return the same type, and so on.

    There are a few additional wrinkles:

    - Since Coq types can themselves be expressions, the checker must
      normalize these (by using the conversion rules) before
      comparing them.

    - The checker must make sure that [match] expressions are
      _exhaustive_.  That is, there must be an arm for every possible
      constructor.  To see why, consider the following alleged proof
      object:
      Definition or_bogus : forall P Q, P \/ Q -> P :=
        fun (P Q : Prop) (A : P \/ Q) =>
           match A with
           | or_introl H => H
           end. 
      All the types here match correctly, but the [match] only
      considers one of the possible constructors for [or].  Coq's
      exhaustiveness check will reject this definition.

    - The checker must make sure that each [fix] expression
      terminates.  It does this using a syntactic check to make sure
      that each recursive call is on a subexpression of the original
      argument.  To see why this is essential, consider this alleged
      proof:
          Definition nat_false : forall (n:nat), False :=
             fix f (n:nat) : False := f n. 
      Again, this is perfectly well-typed, but (fortunately) Coq will
      reject it. *)

(** Note that the soundness of Coq depends only on the correctness of
    this typechecking engine, not on the tactic machinery.  If there
    is a bug in a tactic implementation (and this certainly does
    happen!), that tactic might construct an invalid proof term.  But
    when you type [Qed], Coq checks the term for validity from
    scratch.  Only lemmas whose proofs pass the type-checker can be
    used in further proof developments.  *)


