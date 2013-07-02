
Require Export Lists.

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

Inductive list (X:Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.


Fixpoint length (X:Type) (l:list X) : nat := 
  match l with
  | nil      => 0
  | cons h t => S (length X t)
  end.


Fixpoint app (X : Type) (l1 l2 : list X) 
                : (list X) := 
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) := 
  match l with
  | nil      => cons X v (nil X)
  | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X := 
  match l with
  | nil      => nil X
  | cons h t => snoc X (rev X t) h
  end.

Example test_rev1 :
    rev nat (cons nat 1 (cons nat 2 (nil nat))) 
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity.  Qed.

Example test_rev2: 
  rev bool (nil bool) = nil bool.
Proof. reflexivity.  Qed.

Fixpoint app' X l1 l2 : list X := 
  match l1 with
  | nil      => l2
  | cons h t => cons X h (app' X t l2)
  end.


Fixpoint length' (X:Type) (l:list X) : nat := 
  match l with
  | nil      => 0
  | cons h t => S (length' _ t)
  end.

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Fixpoint length'' {X:Type} (l:list X) : nat := 
  match l with
  | nil      => 0
  | cons h t => S (length'' t)
  end.


Definition mynil : list nat := nil.

Definition mynil' := @nil nat. 

Notation "x :: y" := (cons x y) 
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) 
                     (at level 60, right associativity).


(** **** Exercise: 2 stars, optional (poly_exercises) *)
(** Here are a few simple exercises, just like ones in the [Lists]
    chapter, for practice with polymorphism.  Fill in the definitions
    and complete the proofs below. *)

Fixpoint repeat (X : Type) (n : X) (count : nat) : list X := 
  match count with
  |0 => []
  |S count' => n::(repeat X n count')
  end.

Example test_repeat1: 
  repeat bool true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app : forall X:Type, forall l:list X, 
  app [] l = l.
Proof.
  intros X l.
  reflexivity. 
Qed.

Theorem rev_snoc : forall X : Type, 
                     forall v : X,
                     forall s : list X,
  rev (snoc s v) = v :: (rev s).
Proof.
  intros X v s.
  induction s.
  Case "s = []".
  reflexivity. 
  Case "s = x :: s".
  simpl.
  rewrite IHs.
  reflexivity. 
Qed.
  

Theorem snoc_append : forall X : Type, forall (l : list X) (n:X),
  snoc l n = l ++ [n].
Proof.
  intros X l n. induction l as [| h l'].
  Case "l = []".
    reflexivity.
  Case "l = h :: l'".
    simpl.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem rev1 :forall X : Type, forall (l : list X) (n:X),
  rev  (l ++ [n]) = n::(rev l) .
Proof.
  intros X l n. induction l as [| h l'].
  Case "l = []".
    reflexivity.
  Case "l = h :: l'".
    simpl.
    rewrite -> IHl'.
    rewrite -> snoc_append.
    rewrite -> snoc_append.
    reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [| h l'].
  Case "l = []".
    reflexivity.
  Case "l = h :: l'".
    simpl.
    rewrite -> snoc_append.
    rewrite -> rev1.
    rewrite -> IHl'.
    reflexivity.
Qed.

Theorem snoc_with_append : forall X : Type, 
                         forall l1 l2 : list X,
                         forall v : X,
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  
  intros X l1 l2 v.
  induction l1 as [| h l1'].
  Case "l1 = []".
    reflexivity.
  Case "l1 = h :: l1'".
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.
(** [] *)

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X] [Y]].

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X := 
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y := 
  match p with (x,y) => y end.


Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) 
           : list (X*Y) :=
  match (lx,ly) with
  | ([],_) => []
  | (_,[]) => []
  | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.


Fixpoint combine' {X Y : Type} (lx : list X) (ly : list Y) 
           : list (X*Y) :=
  match lx,ly with
  | [],_ => []
  | _,[] => []
  | x::tx, y::ty => (x,y) :: (combine' tx ty)
  end.

(** **** Exercise: 1 star, optional (combine_checks) *)
(** Try answering the following questions on paper and
    checking your answers in coq:
    - What is the type of [combine] (i.e., what does [Check 
      @combine] print?)
    - What does
        Eval simpl in (combine [1,2] [false,false,true,true]).
      print?   []
*)

(** **** Exercise: 2 stars, recommended (split) *)
(** The function [split] is the right inverse of combine: it takes a
    list of pairs and returns a pair of lists.  In many functional
    programing languages, this function is called [unzip].

    Uncomment the material below and fill in the definition of
    [split].  Make sure it passes the given unit tests. *)


Definition addPair {X Y : Type} (p : X * Y) 
(l : (list X)*(list Y))  :  (list X)*(list Y) := 
  match p,l with 
  |(x,y), (l1,l2) => (x::l1,y::l2)
  end. 
Fixpoint split {X Y : Type} (l : list (X*Y))  
           : (list X)*(list Y) :=
  match l with
  |h::l'=>addPair h (split l')
  |[] => ([],[])
  end.



Example test_split:
  split [(1,false),(2,false)] = ([1,2],[false,false]).
Proof. reflexivity.  Qed.


Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None 
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 :    index 0 [4,5,6,7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index  1 [[1],[2]]  = Some [2].
Proof. reflexivity.  Qed.
Example test_index3 :    index  2 [true]  = None.
Proof. reflexivity.  Qed.

(** **** Exercise: 1 star, optional (hd_opt_poly) *)
(** Complete the definition of a polymorphic version of the
    [hd_opt] function from the last chapter. Be sure that it
    passes the unit tests below. *)

Definition hd_opt {X : Type} (l : list X)  : option X :=
match l with 
  |[] => None
  |n::l' => Some n
end.

(** Once again, to force the implicit arguments to be explicit, 
    we can use [@] before the name of the function. *)

Check @hd_opt.

Example test_hd_opt1 :  hd_opt [1,2] = Some 1. 
Proof. reflexivity.  Qed.
Example test_hd_opt2 :   hd_opt  [[1],[2]]  = Some [1].
Proof. reflexivity.  Qed.
(** [] *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X := 
  f (f (f n)).


Check @doit3times.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity.  Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity.  Qed.


Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity.  Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity.  Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity.  Qed.

(** **** Exercise: 2 stars, optional (currying) *)
(** In Coq, a function [f : A -> B -> C] really has the type [A
    -> (B -> C)].  That is, if you give [f] a value of type [A], it
    will give you function [f' : B -> C].  If you then give [f'] a
    value of type [B], it will return a value of type [C].  This
    allows for partial application, as in [plus3].  Processing a list
    of arguments with functions that return functions is called
    _currying_, in honor of the logician Haskell Curry.

    Conversely, we can reinterpret the type [A -> B -> C] as [(A *
    B) -> C].  This is called _uncurrying_.  With an uncurried binary
    function, both arguments must be given at once as a pair; there is
    no partial application. *)

(** We can define currying as follows: *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** As an exercise, define its inverse, [prod_uncurry].  Then prove
    the theorems below to show that the two are inverses. *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  match p with 
  |(x,y) => f x y
  end. 

  

(** (Thought exercise: before running these commands, can you
    calculate the types of [prod_curry] and [prod_uncurry]?) *)

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.  
  intros X Y Z f x y.
  reflexivity.  
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) 
                               (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  destruct p.
  reflexivity.  
Qed.

Fixpoint filter {X:Type} (test: X->bool) (l:list X) 
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

Example test_filter1: filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity.  Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2: 
    filter length_is_1
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity.  Qed.


Definition countoddmembers' (l:list nat) : nat := 
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity.  Qed.
Example test_countoddmembers'2:   countoddmembers' [0,2,4] = 0.
Proof. reflexivity.  Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity.  Qed.


Example test_anon_fun': 
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity.  Qed.

Example test_filter2': 
    filter (fun l => beq_nat (length l) 1)
           [ [1, 2], [3], [4], [5,6,7], [], [8] ]
  = [ [3], [4], [8] ].
Proof. reflexivity.  Qed.

(** **** Exercise: 2 stars (filter_even_gt7) *)

(** Use [filter] (instead of [Fixpoint]) to write a Coq function
    [filter_even_gt7] which takes a list of natural numbers as input
    and keeps only those numbers which are even and greater than 7. *)

Definition filter_even_gt7 (l : list nat) : list nat :=
  filter (fun n=>andb (evenb n) (ble_nat 7 n)) l. 

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. reflexivity.  Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
Proof. reflexivity.  Qed.
(** [] *)

(** **** Exercise: 3 stars (partition) *)
(** Use [filter] to write a Coq function [partition]: 
  partition : forall X : Type, 
              (X -> bool) -> list X -> list X * list X
   Given a set [X], a test function of type [X -> bool] and a [list
   X], [partition] should return a pair of lists.  The first member of
   the pair is the sublist of the original list containing the
   elements that satisfy the test, and the second is the sublist
   containing those that fail the test.  The order of elements in the
   two sublists should be the same as their order in the original
   list.
*)

Definition partition {X : Type} (test : X -> bool) (l : list X) 
                     : list X * list X :=
  (filter test l, filter (fun n => negb (test n)) l).

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof. reflexivity.  Qed.
Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
Proof. reflexivity.  Qed.
(** [] *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X) 
             : (list Y) := 
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

Example test_map1: map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity.  Qed.

Example test_map2: map oddb [2,1,2,5] = [false,true,false,true].
Proof. reflexivity.  Qed.

Example test_map3: 
    map (fun n => [evenb n,oddb n]) [2,1,2,5] 
  = [[true,false],[false,true],[true,false],[false,true]].
Proof. reflexivity.  Qed.


(** **** Exercise: 3 stars, optional (map_rev) *)
(** Show that [map] and [rev] commute.  You may need to define an
    auxiliary lemma. *)

Theorem map1 : forall (X Y : Type) (f : X -> Y) (l : list X) (n: X),
  map f (l++[n]) = (map f l)++[f n].
Proof.
  intros X Y f l n.
  induction l as [| h l'].
  Case "l = []".
    reflexivity.
  Case "l = h :: l'".
    simpl.
    rewrite IHl'.
  reflexivity. 
Qed.



Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [| h l'].
  Case "l = []".
    reflexivity.
  Case "l = h :: l'".
    simpl.
    rewrite snoc_append.
    rewrite map1.
    rewrite <- IHl'.
    rewrite snoc_append.
    reflexivity. 
Qed.
(** [] *)

(** **** Exercise: 2 stars, recommended (flat_map) *)
(** The function [map] maps a [list X] to a [list Y] using a function
    of type [X -> Y].  We can define a similar function, [flat_map],
    which maps a [list X] to a [list Y] using a function [f] of type
    [X -> list Y].  Your definition should work by 'flattening' the
    results of [f], like so:
        flat_map (fun n => [n,n+1,n+2]) [1,5,10]
      = [1, 2, 3, 5, 6, 7, 10, 11, 12].
*)

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X) 
                   : (list Y) := 
  match l with
  | []     => []
  | h :: t => (f h) ++ (flat_map f t)
  end.

Example test_flat_map1: 
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. reflexivity.  Qed.

(** [] *)


Definition option_map {X Y : Type} (f : X -> Y) (xo : option X) 
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(** **** Exercise: 2 stars, optional (implicit_args) *)
(** The definitions and uses of [filter] and [map] use implicit
    arguments in many places.  Replace the curly braces around the
    implicit arguments with parentheses, and then fill in explicit
    type parameters where necessary and use Coq to check that you've
    done so correctly.  This exercise is not to be turned in; it is
    probably easiest to do it on a _copy_ of this file that you can
    throw away afterwards.  [] *)


Fixpoint fold {X Y:Type} (f: X->Y->Y) (l:list X) (b:Y) : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).

Example fold_example1 : fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true,true,false,true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app  [[1],[],[2,3],[4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.

(** **** Exercise: 1 star, optional (fold_types_different) *)
(** Observe that the type of [fold] is parameterized by _two_ type
    variables, [X] and [Y], and the parameter [f] is a binary operator
    that takes an [X] and a [Y] and returns a [Y].  Can you think of a
    situation where it would be useful for [X] and [Y] to be
    different?

Для преобразования списка в другую коллекцию.
Например: Y - дерево, f - добавление эелмента в дерево.


 *)

Definition constfun {X: Type} (x: X) : nat->X := 
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.


Definition override {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if beq_nat k k' then x else f k'.


Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

(** **** Exercise: 1 star (override_example) *)
(** Before starting to work on the following proof, make sure you
    understand exactly what the theorem is saying and can paraphrase
    it in your own words.  The proof itself is straightforward. *)

Theorem override_example : forall (b:bool), 
  (override (constfun b) 3 true) 2 = b.
Proof.
  intros b.
  reflexivity. 
Qed.
(** [] *)

Inductive boolllist : nat -> Type :=
  boollnil  : boolllist O
| boollcons : forall n, bool -> boolllist n -> boolllist (S n).

Implicit Arguments boollcons [[n]].

Check (boollcons true (boollcons false (boollcons true boollnil))).

Fixpoint blapp {n1} (l1: boolllist n1) 
               {n2} (l2: boolllist n2) 
             : boolllist (n1 + n2) := 
  match l1 with
  | boollnil        => l2
  | boollcons _ h t => boollcons h (blapp t l2)
  end.

Inductive llist (X:Type) : nat -> Type :=
  lnil  : llist X O
| lcons : forall n, X -> llist X n -> llist X (S n).

Implicit Arguments lnil [[X]].
Implicit Arguments lcons [[X] [n]].

Check (lcons true (lcons false (lcons true lnil))).

Fixpoint lapp (X:Type)
              {n1} (l1: llist X n1) 
              {n2} (l2: llist X n2) 
            : llist X (n1 + n2) := 
  match l1 with
  | lnil        => l2
  | lcons _ h t => lcons h (lapp X t l2)
  end.

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n,o] = [n,p] ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* At this point, we could finish with "[rewrite -> eq2. reflexivity.]"
     as we have done several times above. But we can achieve the 
     same effect in a single step by using the [apply] tactic instead: *)
  apply eq2.  Qed.

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
     [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2. 
  apply eq2. apply eq1.  Qed.

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** Exercise: 2 stars, optional (silly_ex) *)
(** Complete the following proof without using [simpl]. *)

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros n eq1. 
  apply eq1.  Qed.

(** [] *)


Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* Here we cannot use [apply] directly *)
Admitted.

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Actually, this [simpl] is unnecessary, since 
            [apply] will do a [simpl] step first. *)  
  apply H.  Qed.         

(** **** Exercise: 3 stars, recommended (apply_exercise1) *)

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  (* Hint: you can use [apply] with previously defined lemmas, not
     just hypotheses in the context.  Remember that [SearchAbout] is
     your friend. *)
  intros l l' H.
  rewrite H.
  symmetry.
  apply rev_involutive.
Qed. 
  


(** [] *)

(** **** Exercise: 1 star (apply_rewrite) *)
(** Briefly explain the difference between the tactics [apply] and
    [rewrite].  Are there situations where both can usefully be
    applied?

apply пвтается полностью сопоставить цель и гипотезу/теорему.
rewrite ищет в цели вхождения левой или правой части равенства из 
гипотезы/теоремы и заменяет их.
apply может не сработать, если левая и правя части в одном из равенств
поменены местами.
*)
(** [] *)


Theorem unfold_example_bad : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  (* At this point, we'd like to do [rewrite -> H], since 
     [plus3 n] is definitionally equal to [3 + n].  However, 
     Coq doesn't automatically expand [plus3 n] to its 
     definition. *)
  Admitted.

(** The [unfold] tactic can be used to explicitly replace a
    defined name by the right-hand side of its definition.  *)

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity.  Qed.

(** Now we can prove a first property of [override]: If we
    override a function at some argument [k] and then look up [k], we
    get back the overridden value. *)

Theorem override_eq : forall {X:Type} x k (f:nat->X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.  Qed.

(** This proof was straightforward, but note that it requires
    [unfold] to expand the definition of [override]. *)

(** **** Exercise: 2 stars (override_neq) *)
Theorem override_neq : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f H1 H2.
  unfold override.
  rewrite  H2.
  rewrite  H1.
  reflexivity.  
Qed.
(** [] *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.  Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity.  Qed.

Theorem silly5 : forall (n m o : nat),
     [n,m] = [o,o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

(** **** Exercise: 1 star (sillyex1) *) 
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros X x y z l j H1 H2.
  inversion H2.
  reflexivity.  
Qed.
(** [] *)

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra.  Qed.

(** **** Exercise: 1 star (sillyex2) *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros X x y z l j H1 H2.
  inversion H1.
Qed.
(** [] *)

Lemma eq_remove_S : forall n m,
  n = m -> S n = S m.
Proof. intros n m eq. rewrite -> eq. reflexivity. Qed.

(** Here's another illustration of [inversion].  This is a slightly
    roundabout way of stating a fact that we have already proved
    above.  The extra equalities force us to do a little more
    equational reasoning and exercise some of the tactics we've seen
    recently. *)

Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l. induction l as [| v' l'].
  Case "l = []". intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'". intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply eq_remove_S. apply IHl'. inversion eq. reflexivity. Qed.

Theorem beq_nat_eq_FAILED : forall n m,
  true = beq_nat n m -> n = m.
Proof.
  intros n m H. induction n as [| n']. 
  Case "n = 0".
    destruct m as [| m'].
    SCase "m = 0". reflexivity.  
    SCase "m = S m'". simpl in H. inversion H. 
  Case "n = S n'".
    destruct m as [| m'].
    SCase "m = 0". simpl in H. inversion H.
    SCase "m = S m'".
      apply eq_remove_S. 
      (* stuck here because the induction hypothesis
         talks about an extremely specific m *)
      Admitted.


Theorem beq_nat_eq : forall n m,
  true = beq_nat n m -> n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". 
    intros m. destruct m as [| m'].
    SCase "m = 0". reflexivity.  
    SCase "m = S m'". simpl. intros contra. inversion contra. 
  Case "n = S n'".
    intros m. destruct m as [| m'].
    SCase "m = 0". simpl. intros contra. inversion contra.
    SCase "m = S m'". simpl. intros H.
      apply eq_remove_S. apply IHn'. apply H. Qed.

(** **** Exercise: 2 stars (beq_nat_eq_informal) *)
(** Give an informal proof of [beq_nat_eq]. *)

(* FILL IN HERE *)
(** [] *)

(** **** Exercise: 3 stars (beq_nat_eq') *)
(** We can also prove beq_nat_eq by induction on [m], though we have
    to be a little careful about which order we introduce the
    variables, so that we get a general enough induction hypothesis --
    this is done for you below.  Finish the following proof.  To get
    maximum benefit from the exercise, try first to do it without
    looking back at the one above. *)

Theorem beq_nat_eq' : forall m n,
  beq_nat n m = true -> n = m.
Proof.
  intros m. induction m as [| m']. 
  Case "m = 0".
    destruct n.
    SCase "n = 0". 
      reflexivity.  
    SCase "n = S n'".
      intros H. inversion H.
  Case "m = S m'".
    destruct n.
    SCase "n = 0". 
      intros H. inversion H.
    SCase "n = S n'".
      intros H. 
      apply eq_remove_S.
      apply IHm'.
      inversion H.
      reflexivity.  
Qed.
(** [] *)



(** **** Exercise: 2 stars, optional (practice) *)
(** Some nontrivial but not-too-complicated proofs to work together in
    class, and some for you to work as exercises.  Some of the
    exercises may involve applying lemmas from earlier lectures or
    homeworks. *)
 

Theorem beq_nat_0_l : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  intros n H.
  destruct n as [| n'].
  Case "n = 0". 
    reflexivity. 
  SCase "n = S n'". 
  inversion H.
Qed.

Theorem beq_nat_0_r : forall n,
  true = beq_nat 0 n -> 0 = n.
Proof.
  intros n H.
  destruct n as [| n'].
  Case "n = 0". 
    reflexivity. 
  SCase "n = S n'". 
  inversion H.
Qed.
(** [] *)

(** **** Exercise: 3 stars (apply_exercise2) *)
(** In the following proof opening, notice that we don't introduce [m]
    before performing induction.  This leaves it general, so that the
    IH doesn't specify a particular [m], but lets us pick.  Finish the
    proof. *)

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". 
  destruct m as [| m'].
    SCase "m = 0". reflexivity.  
    SCase "m = S m'".
      reflexivity. 
  Case "n = S n'". 
  destruct m as [| m'].
    SCase "m = 0". reflexivity.  
    SCase "m = S m'".
    apply IHn'.
Qed.
(** [] *)

(** **** Exercise: 3 stars (beq_nat_sym_informal) *)
(** Provide an informal proof of this lemma that corresponds
    to your formal proof above:

   Theorem: For any [nat]s [n] [m], [beq_nat n m = beq_nat m n].

   Proof:
   (* FILL IN HERE *)
[]
 *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b. 
Proof.
  intros n m b H. simpl in H. apply H.  Qed.


Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5  ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H. 
  apply H.  Qed.

(** **** Exercise: 3 stars, recommended (plus_n_n_injective) *)
(** You can practice using the "in" variants in this exercise. *)

Theorem unS : forall n m,
     n  = m  ->
     S n = S m.
Proof.
  intros n m H.
  rewrite H.
  reflexivity. 
Qed.


Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". 
  destruct m as [| m'].
    SCase "m = 0". reflexivity.  
    SCase "m = S m'".
    intros H.
    inversion H.
  Case "n = S n'". 
  destruct m as [| m'].
    SCase "m = 0".
    intros H.
    inversion H.   
    SCase "m = S m'".
    rewrite <- plus_n_Sm.
    rewrite <- plus_n_Sm.
simpl.
    intros H.
    apply unS.
    apply IHn'.
    inversion H.  
  reflexivity. 
Qed.

    (* Hint: use the plus_n_Sm lemma *)
(** [] *)

(* ###################################################### *)
(** ** Using [destruct] on Compound Expressions *)


(** We have seen many examples where the [destruct] tactic is
    used to perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun. 
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity.  Qed.

(** After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (beq_nat n 3) then ... else ...].  Well,
    either [n] is equal to [3] or it isn't, so we use [destruct
    (beq_nat n 3)] to let us reason about the two cases. *)

(** **** Exercise: 1 star (override_shadow) *)
Theorem override_shadow : forall {X:Type} x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x3 k1 k2 f.
  unfold override.
  destruct (beq_nat k1 k2).
    Case "beq_nat k1 k2 = true". reflexivity.
    Case "beq_nat k1 k2 = false". reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, recommended (combine_split) *)
Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l. induction l as [| [x y] l'].
  Case "l = []".
    intros.
    inversion H.  
    reflexivity.
  Case "l = (x, y) :: l'".
    intros.
    inversion H.
    destruct (split l').
Admitted.
(** [] *)

(** **** Exercise: 3 stars, optional (split_combine) *)
(** Thought exercise: We have just proven that for all lists of pairs,
    [combine] is the inverse of [split].  How would you state the
    theorem showing that [split] is the inverse of [combine]?
 
    Hint: what property do you need of [l1] and [l2] for [split]
    [combine l1 l2 = (l1,l2)] to be true?

    State this theorem in Coq, and prove it. (Be sure to leave your
    induction hypothesis general by not doing [intros] on more things
    than necessary.) *)

(* FILL IN HERE *) 
(** [] *)

(* ###################################################### *)
(** ** The [remember] Tactic *)

(** (Note: the [remember] tactic is not strictly needed until a
    bit later, so if necessary this section can be skipped and
    returned to when needed.) *)

(** We have seen how the [destruct] tactic can be used to
    perform case analysis of the results of arbitrary computations.
    If [e] is an expression whose type is some inductively defined
    type [T], then, for each constructor [c] of [T], [destruct e]
    generates a subgoal in which all occurrences of [e] (in the goal
    and in the context) are replaced by [c].

    Sometimes, however, this substitution process loses information
    that we need in order to complete the proof.  For example, suppose
    we define a function [sillyfun1] like this: *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(** And suppose that we want to convince Coq of the rather
    obvious observation that [sillyfun1 n] yields [true] only when [n]
    is odd.  By analogy with the proofs we did with [sillyfun] above,
    it is natural to start the proof like this: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Admitted.

(** We get stuck at this point because the context does not
    contain enough information to prove the goal!  The problem is that
    the substitution peformed by [destruct] is too brutal -- it threw
    away every occurrence of [beq_nat n 3], but we need to keep at
    least one of these because we need to be able to reason that
    since, in this branch of the case analysis, [beq_nat n 3 = true],
    it must be that [n = 3], from which it follows that [n] is odd.

    What we would really like is not to use [destruct] directly on
    [beq_nat n 3] and substitute away all occurrences of this
    expression, but rather to use [destruct] on something else that is
    _equal_ to [beq_nat n 3].  For example, if we had a variable that
    we knew was equal to [beq_nat n 3], we could [destruct] this
    variable instead.

    The [remember] tactic allows us to introduce such a variable. *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
   remember (beq_nat n 3) as e3.
   (* At this point, the context has been enriched with a new
      variable [e3] and an assumption that [e3 = beq_nat n 3].
      Now if we do [destruct e3]... *)
   destruct e3.
   (* ... the variable [e3] gets substituted away (it
     disappears completely) and we are left with the same
      state as at the point where we got stuck above, except
      that the context still contains the extra equality
      assumption -- now with [true] substituted for [e3] --
      which is exactly what we need to make progress. *)
     Case "e3 = true". apply beq_nat_eq in Heqe3.
       rewrite -> Heqe3. reflexivity.
     Case "e3 = false".
      (* When we come to the second equality test in the
        body of the function we are reasoning about, we can
         use [remember] again in the same way, allowing us
         to finish the proof. *)
       remember (beq_nat n 5) as e5. destruct e5.
         SCase "e5 = true".
           apply beq_nat_eq in Heqe5.
           rewrite -> Heqe5. reflexivity.
         SCase "e5 = false". inversion eq.  Qed.

(** **** Exercise: 2 stars (override_same) *)
Theorem override_same : forall {X:Type} x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override f k1 x1) k2 = f k2.
Proof.
  intros.
  unfold override.
 remember (beq_nat k1 k2) as e3.
   
   destruct e3.
     Case "e3 = true". apply beq_nat_eq in Heqe3.
       rewrite -> Heqe3 in H.
       symmetry.
       apply H.
     Case "e3 = false".
       reflexivity.
 Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (filter_exercise) *)
(** This one is a bit challenging.  Be sure your initial [intros] go
    only up through the parameter on which you want to do
    induction! *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l lf.
  induction l as [| h l'].
  Case "l = []".
  intros.
    inversion H.
  Case "l = h::l'".
    remember (test h) as e3.
    destruct e3.
    SCase "e3 = true". 
      simpl.
      rewrite <- Heqe3.
      intros.
      inversion H.
      rewrite H1 in Heqe3.
      symmetry.
      apply Heqe3.
    SCase "e3 = false".
      simpl.
      rewrite <- Heqe3.
      apply IHl'.
Qed.
  
(** [] *)

(* ###################################################### *)
(** ** The [apply ... with ...] Tactic *)

(** The following silly example uses two rewrites in a row to
    get from [[a,b]] to [[e,f]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Since this is a common pattern, we might
    abstract it out as a lemma recording once and for all
    the fact that equality is transitive. *)

Theorem trans_eq : forall {X:Type} (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. 
  reflexivity.  Qed.

(** Now, we should be able to use [trans_eq] to
    prove the above example.  However, to do this we need
    a slight refinement of the [apply] tactic. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a,b] = [c,d] ->
     [c,d] = [e,f] ->
     [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2. 
  (* If we simply tell Coq [apply trans_eq] at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate [X]
     with [[nat]], [n] with [[a,b]], and [o] with [[e,f]].
     However, the matching process doesn't determine an
     instantiation for [m]: we have to supply one explicitly
     by adding [with (m:=[c,d])] to the invocation of
     [apply]. *)
  apply trans_eq with (m:=[c,d]). apply eq1. apply eq2.   Qed.

(**  Actually, we usually don't have to include the name [m]
    in the [with] clause; Coq is often smart enough to
    figure out which instantiation we're giving. We could
    instead write: apply trans_eq with [c,d]. *)

(** **** Exercise: 3 stars, recommended (apply_exercises) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o). 
Proof.
  intros.
  rewrite H0.
  apply H.
Qed.

Theorem beqTrue : forall n, true = beq_nat n n.
Proof.  
  intros.
  induction n as[| n'].
  
  reflexivity.
  simpl.  
  apply IHn'.
Qed.


Theorem beq_nat_trans : forall n m p,
  true = beq_nat n m ->
  true = beq_nat m p ->
  true = beq_nat n p.
Proof.
  
  intros.
apply beq_nat_eq in H.
apply beq_nat_eq in H0.
  rewrite H.
  rewrite H0.
  apply beqTrue.
Qed.

Theorem override_permute : forall {X:Type} x1 x2 k1 k2 k3 (f : nat->X),
  false = beq_nat k2 k1 ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros.
  unfold override.
 remember (beq_nat k1 k3) as e3.
   
   destruct e3.
     Case "e3 = true". apply beq_nat_eq in Heqe3.
       rewrite -> Heqe3 in H.
       rewrite <- H.
       reflexivity.
     Case "e3 = false".
       reflexivity.
 Qed.
(** [] *)

(* ################################################################## *)
(** * Review *)

(** We've now seen a bunch of Coq's fundamental tactics -- enough to
    do pretty much everything we'll want for a while.  We'll introduce
    one or two more as we go along through the next few lectures, and
    later in the course we'll introduce some more powerful
    _automation_ tactics that make Coq do more of the low-level work
    in many cases.  But basically we've got what we need to get work
    done.

    Here are the ones we've seen:

      - [intros]: 
        move hypotheses/variables from goal to context 

      - [reflexivity]:
        finish the proof (when the goal looks like [e = e])

      - [apply]:
        prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: 
        apply a hypothesis, lemma, or constructor to a hypothesis in
        the context (forward reasoning)

      - [apply... with...]:
        explicitly specify values for variables that cannot be
        determined by pattern matching

      - [simpl]:
        simplify computations in the goal 

      - [simpl in H]:
        ... or a hypothesis 

      - [rewrite]:
        use an equality hypothesis (or lemma) to rewrite the goal 

      - [rewrite ... in H]:
        ... or a hypothesis 

      - [symmetry]:
        changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]:
        changes a hypothesis of the form [t=u] into [u=t]

      - [unfold]:
        replace a defined constant by its right-hand side in the goal 

      - [unfold... in H]:
        ... or a hypothesis  

      - [destruct... as...]:
        case analysis on values of inductively defined types 

      - [induction... as...]:
        induction on values of inductively defined types 

      - [inversion]:
        reason by injectivity and distinctness of constructors

      - [remember (e) as x]:
        give a name ([x]) to an expression ([e]) so that we can
        destruct [x] without "losing" [e]

      - [assert (e) as H]:
        introduce a "local lemma" [e] and call it [H] 
*)

(* ###################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 2 stars, optional (fold_length) *)
(** Many common functions on lists can be implemented in terms of
   [fold].  For example, here is an alternate definition of [length]: *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4,7,0] = 3.
Proof. reflexivity. Qed.

(** Prove the correctness of [fold_length]. *)


Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros.
  induction l as [| h l'].
  Case "l = []".
    reflexivity.
  Case "l = h :: l'".
    simpl.
    unfold fold_length.
    simpl.
    rewrite <- IHl'.
    unfold fold_length.
    reflexivity. 
Qed.
(** [] *)

(** **** Exercise: 3 stars, recommended (fold_map) *)
(** We can also define [map] in terms of [fold].  Finish [fold_map]
    below. *)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun n1 n2 => (f n1) :: n2) l [].


(** Write down a theorem in Coq stating that [fold_map] is correct,
    and prove it. *)

Theorem fold_map_correct : forall X Y (l : list X) (f : X -> Y),
  fold_map f l = map f l.
Proof.
  intros.
  induction l as [| h l'].
  Case "l = []".
    reflexivity.
  Case "l = h :: l'".
    simpl.
    unfold fold_length.
    simpl.
    rewrite <- IHl'.
    unfold fold_length.
    reflexivity. 
Qed.
(** [] *)

Module MumbleBaz.
(** **** Exercise: 2 stars, optional (mumble_grumble) *)
(** Consider the following two inductively defined types. *)

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.
Inductive grumble (X:Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(** Which of the following are well-typed elements of [grumble X] for
    some type [X]?
      - [d (b a 5)] - нет типа после d 
      - [d mumble (b a 5)] - well-typed
      - [d bool (b a 5)] - well-typed
      - [e bool true] - well-typed
      - [e mumble (b c 0)] - well-typed
      - [e bool (b c 0)] - вместо bool должен быть mumble, 
                           или в скобках должан быть bool
      - [c] - well-typed

[] *)
(** **** Exercise: 2 stars, optional (baz_num_elts) *)
(** Consider the following inductive definition: *)

Inductive baz : Type :=
   | x : baz -> baz
   | y : baz -> bool -> baz.

(** How _many_ elements does the type [baz] have? 

Здесь не хватает базисного элемента. 
=> нельзя постоить ни одного элемента

[] *)

End MumbleBaz.

(** **** Exercise: 4 stars, recommended (forall_exists_challenge) *)
(** Challenge problem: Define two recursive [Fixpoints],
    [forallb] and [existsb].  The first checks whether every
    element in a list satisfies a given predicate:
      forallb oddb [1,3,5,7,9] = true

      forallb negb [false,false] = true
  
      forallb evenb [0,2,4,5] = false
  
      forallb (beq_nat 5) [] = true
    The function [existsb] checks whether there exists an element in
    the list that satisfies a given predicate:
      existsb (beq_nat 5) [0,2,3,6] = false
 
      existsb (andb true) [true,true,false] = true
 
      existsb oddb [1,0,0,0,0,3] = true
 
      existsb evenb [] = false
    Next, create a _nonrecursive_ [Definition], [existsb'], using
    [forallb] and [negb].
 
    Prove that [existsb'] and [existsb] have the same behavior.
*)

Fixpoint forallb {X :Type} (f : X -> bool) (l : list X) : bool :=
  match l with 
  |[] => true
  |h::l' => if f h then forallb f l' else false
  end.
Example forallb_example1 : forallb oddb [1,3,5,7,9] = true.
Proof. reflexivity. Qed.
Example forallb_example2 : forallb evenb [0,2,4,5] = false.
Proof. reflexivity. Qed.
Example forallb_example3 : forallb (beq_nat 5) [] = true.
Proof. reflexivity. Qed.
Example forallb_example4 : forallb negb [false,false] = true.
Proof. reflexivity. Qed.
Fixpoint existsb {X :Type} (f : X -> bool) (l : list X) : bool :=
  match l with 
  |[] => false
  |h::l' => if f h then true else existsb f l'
  end.
Example existsb_example1 : existsb (beq_nat 5) [0,2,3,6] = false.
Proof. reflexivity. Qed.
Example existsb_example2 : existsb (andb true) [true,true,false] = true.
Proof. reflexivity. Qed.
Example existsb_example3 : existsb oddb [1,0,0,0,0,3] = true.
Proof. reflexivity. Qed.
Example existsb_example4 : existsb evenb [] = false.
Proof. reflexivity. Qed.
Definition existsb' {X :Type} (f : X -> bool) (l : list X) : bool :=
negb (forallb (fun n => negb(f n)) l).
Theorem fold_existsb_correct : forall X (l : list X) (f : X -> bool),
  existsb f l = existsb' f l.
Proof.
  intros.
  induction l as [| h l'].
  Case "l = []".
    reflexivity.
  Case "l = h :: l'".
    simpl.
    unfold existsb'.
    simpl.
    remember (f h) as e3.
    destruct e3.
    SCase "e3 = true". 
      reflexivity. 
    SCase "e3 = false".
      simpl.
      rewrite -> IHl'.
      unfold existsb'.
      reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (index_informal) *)
(** Recall the definition of the [index] function:
   Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
     match l with
     | [] => None 
     | a :: l' => if beq_nat n O then Some a else index (pred n) l'
     end.
   Write an informal proof of the following theorem:
   forall X n l, length l = n -> @index X (S n) l = None.
(* FILL IN HERE *)
*)
(** [] *)

