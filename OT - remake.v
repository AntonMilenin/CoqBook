Require Export "Ascii". 
Require Export "Prop".
Open Scope char_scope.

Inductive function : Type:=
  |fInsert: nat -> ascii->function 
  |fDelete: nat -> function 
  |fId: function.

Definition beq_ascii n m : bool :=
  if ascii_dec n m then true else false
  .

Definition function_eq (a b:function) : bool :=
  match a, b with 
  |fDelete n1,fDelete n2 => beq_nat n1 n2
  |fInsert n1 x1, fInsert n2 x2 => andb (beq_nat n1 n2) (beq_ascii x1 x2)
  |_,_ =>false
  end.


Example test_function_eq0: function_eq (fDelete 0) (fDelete 0)= true.
Proof. simpl; reflexivity. Qed.
Example test_function_eq1: function_eq (fDelete 0) (fDelete 3)= false.
Proof. simpl; reflexivity. Qed.
Example test_function_eq2: function_eq (fInsert 0 "a") (fInsert 0 "a")= true.
Proof. simpl; reflexivity. Qed.
Example test_function_eq3: function_eq (fInsert 0 "a") (fInsert 0 "c")= false.
Proof. simpl; reflexivity. Qed.


Fixpoint insert1 n x (l:list ascii):list ascii:=
  match n with 
  |0 => x::l
  |S n' =>match l with
    |[] => []
    |h::l' => h::(insert1 n' x l')
    end
  end.

Definition insert n x (l:list ascii): option (list ascii):=
if ble_nat (S(length l)) n then None else Some(insert1 n x l).
Example test_insert0: insert 0 "a" ["0","1","2","3"] = Some ["a","0","1","2","3"].
Proof. simpl; reflexivity. Qed.
Example test_insert1: insert 2 "a" ["0","1","2","3"] = Some ["0","1","a","2","3"].
Proof. simpl; reflexivity. Qed.
Example test_insert2: insert 7 "a" ["0","1","2","3"] = None.
Proof. simpl; reflexivity. Qed.
Example test_insert3: insert 4 "a" ["0","1","2","3"] = Some ["0","1","2","3","a"].
Proof. simpl; reflexivity. Qed.
Example test_insert4: insert 5 "a" ["0","1","2","3"] = None.
Proof. simpl; reflexivity. Qed.

Fixpoint delete1 n (l:list ascii):list ascii:=
  match l with
   |[] => []
   |h::l' =>
    match n with 
     |0 => l'
     |S n' =>h::(delete1 n' l')
    end 
  end.

Definition delete n (l:list ascii): option (list ascii):=
if ble_nat (length l) n then None else Some(delete1 n l).

Example test_delete0: delete 0 ["0","1","2","3"] = Some ["1","2","3"].
Proof. simpl; reflexivity. Qed.
Example test_delete1: delete 2 ["0","1","2","3"] = Some ["0","1","3"].
Proof. simpl; reflexivity. Qed.
Example test_delete2: delete 8 ["0","1","2","3"] = None.
Proof. simpl; reflexivity. Qed.
Example test_delete3: delete 3 ["0","1","2","3"] = Some ["0","1","2"].
Proof. simpl; reflexivity. Qed.
Example test_delete4: delete 4 ["0","1","2","3"] = None.
Proof. simpl. reflexivity. Qed.

Definition apply (f:function) (l:list ascii): option (list ascii):=
  match f with 
  |fInsert n x => insert n x l
  |fDelete n => delete n l
  |fId => Some l
  end.
(*f1 - applied function, f2 - function that we must apply*)
Definition OT (f1 f2:function) (server:bool):function:=
  if function_eq f1 f2 then fId else
  match f1, f2 with
   |fId, _ => f2 
   |_, fId => fId
   |fInsert n1 x1, fInsert n2 x2 => (*
    if beq_nat n1 n2 
     then (
      if server 
       then fInsert (S n2) x2
       else f2)
     else (
      if ble_nat n1 n2
       then fInsert (S n2) x2
       else f2)*)
    if orb (andb server (beq_nat n1 n2)) (negb(ble_nat n2 n1)) (*server or n1<n2*)
     then fInsert (S n2) x2
     else f2
   |fDelete n1, fInsert n2 x2 => 
    if negb (ble_nat n2 n1) (*n1<n2*)
     then fInsert (pred n2) x2
     else f2
   |fInsert n1 x1, fDelete n2 =>
    if ble_nat n1 n2 (*n1<=n2*)
     then fDelete (S n2)
     else f2
   |fDelete n1, fDelete n2 => 
    if negb (ble_nat n2 n1) (*n1<n2*)
     then fDelete (pred n2) 
     else f2
   end.
Open Scope string_scope.

Definition xor_boolToProp (b1 b2: bool):Prop:=
  (b1 =false /\ b2=true)\/(b2 =false /\ b1=true).
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.

Theorem ble_nat_neg : forall (n0 n1 : nat),false=ble_nat n0 n1->true=ble_nat n1 n0.
Proof.
  intros n0. induction n0.
  Case "n0=0".
   intros. inversion H.
  Case "n0=S n0".
   intros. destruct n1. 
    reflexivity.
    simpl. apply IHn0. inversion H. reflexivity.
Qed.

Theorem ble_nat_trans : forall (n0 n1 n2 : nat),true=ble_nat n0 n1->
true = ble_nat n1 n2-> true=ble_nat n0 n2.
Proof.
  intros n0. induction n0.
  Case "n0=0".
   intros. reflexivity.
  Case "n0=S n0".
   intros. destruct n2,n1; try inversion H.
    inversion H0.
    apply IHn0 with (n1:=n1).
     inversion H. reflexivity.
     inversion H0. reflexivity.
Qed.
 
Theorem ble_nat_negtrans : forall (n0 n1 n2 : nat),false=ble_nat n0 n1->
false = ble_nat n1 n2-> false=ble_nat n0 n2.
Proof.
  intros n0. induction n0.
  Case "n0=0".
   intros. inversion H.
  Case "n0=S n0".
   intros. destruct n2, n1;try inversion H0.
    reflexivity.
    apply IHn0 with (n1:=n1).
     inversion H. reflexivity.
     inversion H0. reflexivity.
Qed.

Theorem ble_nat_negtrans1 : forall (n0 n1 n2 : nat),true = ble_nat n0 n1->
false = ble_nat n2 n1-> false=ble_nat n2 n0.
Proof.
  intros n0. induction n0.
  Case "n0=0".
   intros. destruct n2,n1;try inversion H0;try inversion H;try reflexivity.
  Case "n0=S n0".
   intros. destruct n2, n1;try inversion H0.
    inversion H.
    apply IHn0 with (n1:=n1).
     inversion H. reflexivity.
     inversion H0. reflexivity.
Qed.

Theorem beq_ascii_sym : forall (n1 n2 : ascii),beq_ascii n1 n2=beq_ascii n2 n1.
Proof.
Admitted.

Theorem beq_ascii_eq : forall (n1 n2 : ascii),true = beq_ascii n1 n2 -> n1=n2.
Proof.
Admitted.

Theorem ble_nat_neg0 : forall n n0 ,  false = beq_nat  n n0 ->true = ble_nat n0 n ->false=ble_nat n n0. 
Proof.
  intros n. induction n.
   intros. destruct n0. 
    inversion H.
    inversion H0.
   intros. destruct n0.
    reflexivity.
    simpl. apply IHn.
     simpl in H,H0. apply H.
     simpl in H0. apply H0.
Qed.
  
Theorem ble_nat_neg1 : forall n n0 ,  false = beq_nat  n n0 ->false = ble_nat n0 n ->true=ble_nat n n0. 
Proof.
  intros n. induction n.
   intros. reflexivity.
   intros. destruct n0.
    inversion H0.
    simpl. apply IHn.
     simpl in H,H0. apply H.
     simpl in H0. apply H0.
Qed.

Theorem ble_nat_neg2 : forall n n0 ,  
true = ble_nat (S n) (n0) -> false = ble_nat n0 n. 
Proof.
  intros n. induction n.
  intros. destruct n0.
   inversion H.
   reflexivity.
  intros. destruct n0.
   inversion H.
   simpl. apply IHn. simpl in H. apply H.
Qed.

Theorem ble_nat_beq : forall n n0 ,  
true = ble_nat n0 (S n) -> false = ble_nat n0 n->true = beq_nat n0 (S n). 
Proof.
  intros n. induction n.
   intros. destruct n0. inversion H0. destruct n0. reflexivity. inversion H. 
   intros. destruct n0. inversion H0.
    apply IHn with (n0:=n0).
     simpl in H. apply H.
     simpl in H0. apply H0.
Qed.


Theorem bleSF : forall n1 n2 , false = ble_nat n1 (S n2)->false = ble_nat n1 (n2).
Proof.
  intros n1. induction n1.
   simpl. intros. inversion H.
   intros. destruct n2.
    reflexivity.
    simpl. apply IHn1. simpl in H. apply H.
Qed.


Theorem bleST : forall n1 n2 , true = ble_nat (S n1) n2 ->true = ble_nat n1 n2.
Proof.
  intros n1. induction n1.
   simpl. intros. destruct n2.
    inversion H.
    reflexivity.
   intros. destruct n2.
    inversion H.
    simpl. simpl in H. apply IHn1. apply H.
Qed.


Theorem bleSF1 : forall n1 n2 , false = ble_nat n1 n2 ->false = ble_nat (S n1) n2.
Proof.
  intros n1. induction n1.
   simpl. intros. inversion H.
   intros. destruct n2.
    reflexivity.
    simpl. apply IHn1. simpl in H. apply H.
Qed.

Theorem ble_nat_neg3 : forall n n0 ,  false = beq_nat (n) (n0)->
false = ble_nat (S n) (n0) -> false = ble_nat n n0. 
Proof.
  intros n. induction n.
   intros. destruct n0.
    inversion H.
    inversion H0.
   intros. destruct n0.
    reflexivity.
    simpl. apply IHn.
     apply H.
     simpl in H0. apply H0.
Qed.


Theorem insert_len : forall n a l l1,apply (fInsert n a) l = Some l1->S (length l)=length l1.
Proof.
  intros n a l. generalize n. 
   induction l.
   Case "l=[]".
    simpl. intros.
     destruct l1; destruct n0; try inversion H; try reflexivity.
   Case "l=x::l".
    intros. simpl. destruct l1.
     destruct n0;simpl in H; unfold insert in H.
      simpl in H. inversion H.
      destruct (ble_nat (S (length (x :: l))) (S n0)) in H;inversion H.
     simpl in H. 
      destruct n0;simpl in H; unfold insert in H.
       simpl in H. inversion H. simpl. reflexivity.
       remember (ble_nat (S (length (x :: l))) (S n0)) as ble.
        destruct ble;inversion H.
        simpl. apply eq_remove_S. apply IHl with (n:=n0). simpl. unfold insert. 
        simpl in Heqble. simpl. rewrite <- Heqble. reflexivity.
Qed.
 
Theorem delete_len : forall n l l1,apply (fDelete n) l = Some l1->(length l)=S(length l1).
Proof.
 intros n l. generalize n.
  induction l.
  Case "l=[]".
   simpl. intros.
   destruct l1; destruct n0; inversion H.
  Case "l=x::l".
   simpl. intros. destruct l1.
    destruct n0.
     simpl in H.
     inversion H.
     reflexivity. unfold delete in H.  destruct (ble_nat (length (x :: l)) (S n0)); inversion H.
    simpl. intros. apply eq_remove_S. 
     destruct n0.
      simpl in H. inversion H.  reflexivity.
      apply IHl with (n:=n0). simpl. unfold delete in H.  simpl in H. unfold delete. 
       destruct (ble_nat (length l) n0); inversion H. reflexivity.
Qed. 
  
Theorem OT2 : forall n0 a a0 l,insert1 n0 a0 (insert1 n0 a l) =insert1 (S n0) a (insert1 n0 a0 l).
Proof.
  intros. generalize n0.
  induction l.
   intros. destruct n1; reflexivity.
   intros.
    destruct n1; simpl;try rewrite IHl; reflexivity.
Qed.
  
Theorem OT3 : forall n n0 a a0 l,true=ble_nat n0 n->
 insert1 n0 a0 (insert1 n a l) = insert1 (S n) a (insert1 n0 a0 l).
Proof.
 intros. generalize dependent n0. generalize dependent n.
  induction l.
   intros. destruct n0. reflexivity. destruct n. inversion H. reflexivity.
   destruct n0. reflexivity. intros. destruct n. inversion H. simpl. 
    rewrite IHl.
     reflexivity. 
     simpl in H. apply H.
Qed.

Theorem OT5 : forall n n0 a l,true = ble_nat n n0 -> delete1 (S n0) (insert1 n a l) =
insert1 n a (delete1 n0 l).
Proof.
  intros. generalize dependent n0. generalize dependent n.
   induction l.
    intros. destruct n0,n;reflexivity.
    intros.
     destruct n0,n;try reflexivity.
      inversion H.
      simpl. 
       rewrite <-IHl. reflexivity.
       simpl in H. apply H.
Qed.

Theorem OT6 : forall n n0 a l a4,false = ble_nat (S (length l)) n -> false = ble_nat (S n) n0->
delete1 n0 (a4 :: insert1 n a l) =insert1 n a (delete1 n0 (a4 :: l)).
Proof.
  intros. generalize dependent n0. generalize dependent n. generalize dependent a4.
   induction l.
    intros. destruct n0,n; try reflexivity.
     inversion H0.
     inversion H.
    intros. destruct n0,n; try reflexivity.
     inversion H0.
     simpl. rewrite <-IHl.
      reflexivity.
      simpl in H. apply H.
      simpl in H0. apply H0.  
Qed.

Theorem OT7 : forall n n0 a l,true = ble_nat n0 n->insert1 n0 a (delete1 n l) =
match insert1 n0 a l with
         | [] => []
         | h :: l' => h :: delete1 n l'
         end.
Proof.
  intros. generalize dependent n0. generalize dependent n.
  induction l.
   intros. destruct n0,n; reflexivity.
   intros. destruct n0,n; try reflexivity;try inversion H.
    simpl in IHl. simpl. rewrite IHl.
     reflexivity.
     simpl in H. apply H.  
Qed.

Theorem OT8 : forall n n0 a l a0,false = ble_nat (S(length l)) n -> false = ble_nat (S n0) n->
insert1 n0 a (delete1 n (a0 :: l)) = delete1 n (a0 :: insert1 n0 a l).
Proof.
  intros. generalize dependent n0. generalize dependent n. generalize dependent a0.
   induction l.
    intros. destruct n. reflexivity. inversion H.
  intros. destruct n0,n; try reflexivity.
   inversion H0.
   simpl. rewrite <-IHl. 
    reflexivity.
    simpl in H. apply H.
    simpl in H0. apply H0.  
Qed.

Theorem OT9 : forall n n0 l a,false = ble_nat (length l) n ->false = ble_nat (S n) n0->
delete1 n0 (a :: delete1 n l) = delete1 n (delete1 n0 (a :: l)).
Proof.
  intros. generalize dependent n0. generalize dependent n. generalize dependent a. induction l.
   intros. destruct n0,n; inversion H.
   intros. destruct n0,n;try reflexivity.
    inversion H0.
    simpl. rewrite <-IHl. 
     reflexivity.
     simpl in H. apply H.
     simpl in H0. apply H0.  
Qed.
Theorem OT11 : forall n0 n l a,false = ble_nat (S n) n0 ->length l = S n->
delete1 n0 (a :: delete1 n l) =delete1 n (delete1 n0 (a :: l)).
Proof.
  intros. generalize dependent n0. generalize dependent n. generalize dependent a. induction l.
   intros. inversion H0. 
   intros. destruct n0,n;try reflexivity.
    inversion H.
    simpl. rewrite <-IHl. 
     reflexivity.
     inversion H0.  reflexivity.
     simpl in H. apply H.  
Qed.

Theorem OT10 : forall n n0 l a,false = ble_nat (length l) n -> false = ble_nat (S n0) n->
      delete1 n0 (delete1 n (a :: l)) = delete1 n (a :: delete1 n0 l).
Proof.
  intros. generalize dependent n0. generalize dependent n. generalize dependent a. induction l. 
   intros. destruct n0,n; inversion H.
   intros. destruct n0,n; try reflexivity.
   inversion H0.
   simpl. rewrite <-IHl. 
     reflexivity.
     simpl in H. apply H.
     simpl in H0. apply H0.  
Qed.

Theorem OT_correctness : forall (f1 f2:function) (b1 b2: bool) (l l1 l2:list ascii),((apply f1 l)=Some l1 
 /\ (apply f2 l) =Some l2)-> (apply (OT f1 f2 false) l1 =apply (OT f2 f1 true) l2/\exists l3,apply (OT f2 f1 true) l2=Some l3).
Proof.
  intros. destruct f1,f2.
  Case "f1=inv, f2=inv".
   inversion H. inversion H. apply insert_len in H3. apply insert_len in H2. simpl in H0,H1.
    unfold insert in H0,H1. unfold OT. unfold function_eq. 
    remember (beq_nat n n0) as beq. destruct beq.
    SCase "n=n0".
     rewrite beq_nat_sym. rewrite <- Heqbeq. simpl.
      remember (beq_ascii a a0) as beqa. destruct beqa.
      SSCase "a=a0".
       rewrite beq_ascii_sym. rewrite <- Heqbeqa. apply beq_nat_eq in Heqbeq.
        rewrite Heqbeq in H0. apply beq_ascii_eq in Heqbeqa. rewrite Heqbeqa in H0.
        rewrite H0 in H1. inversion H1. split. reflexivity. exists l2. reflexivity.
      SSCase "a!=a0".
       rewrite beq_ascii_sym.  rewrite <- Heqbeqa. apply beq_nat_eq in Heqbeq.  rewrite Heqbeq.
        rewrite <- ble_nat_refl. simpl. unfold insert. rewrite <-H2,<-H3. rewrite Heqbeq in H0.
        replace (ble_nat (S (S (length l))) (S n0)) with (ble_nat (S (length l)) n0) by reflexivity.
        remember (ble_nat (S(length l)) n0) as ble. destruct ble; inversion H0. inversion H1.
        apply bleSF1 in Heqble. rewrite <-Heqble. rewrite OT2. 
        split;try exists (insert1 (S n0) a (insert1 n0 a0 l));reflexivity.
    SCase "n!=n0".
     rewrite beq_nat_sym. rewrite <-Heqbeq. simpl. remember (ble_nat n0 n) as ble. destruct ble.
     SSCase "n0<=n".
      inversion Heqble.  apply ble_nat_neg0 in H5;try apply Heqbeq. rewrite <-H5.
       simpl. unfold insert. rewrite <- H2,<-H3. 
       replace (ble_nat (S (S (length l))) (S n)) with (ble_nat (S (length l)) n) by reflexivity.
       destruct (ble_nat (S (length l)) n); inversion H0.
       remember (ble_nat (S (length l)) n0) as ble. destruct ble; inversion H1. apply bleSF1 in Heqble0.
       rewrite <-Heqble0. rewrite OT3; try apply Heqble.
       split;try exists (insert1 (S n) a (insert1 n0 a0 l));reflexivity.
     SSCase "n0>n".
      inversion Heqble.  apply ble_nat_neg in H5. rewrite <-H5. simpl. unfold insert.
       rewrite <- H2,<-H3. 
       replace (ble_nat (S (S (length l))) (S n0)) with (ble_nat (S (length l)) n0) by reflexivity.
       destruct (ble_nat (S (length l)) n0); inversion H1.
       remember (ble_nat (S (length l)) n) as ble. destruct ble; inversion H0. apply bleSF1 in Heqble0.
       rewrite <-Heqble0. rewrite <-OT3; try apply H5.
       split;try exists (insert1 n a (insert1 n0 a0 l));reflexivity.
  Case "f1=ins, f2=del".
   inversion H. inversion H. apply insert_len in H2. apply delete_len in H3.
    unfold OT. simpl. simpl in H0,H1. unfold insert,delete in H0,H1. 
    remember (ble_nat n n0) as ble. destruct ble.
    SCase "n<=n0".
     simpl. unfold delete,insert. rewrite <- H2,<-H3.
      replace (ble_nat ((S (length l))) (S n0)) with (ble_nat ((length l)) n0) by reflexivity.
      remember (ble_nat (length l) n0) as ble. destruct ble;inversion H1. 
      inversion Heqble0. apply ble_nat_negtrans1 with (n0:=n) in H6; try apply Heqble.
      rewrite <- H6. destruct (ble_nat (S (length l)) n); inversion H0.
      rewrite OT5;try apply Heqble. split;try exists (insert1 n a (delete1 n0 l));reflexivity.
    SCase "n>n0". 
     simpl. unfold delete,insert. rewrite <- H2,<-H3.
      destruct n. inversion Heqble. unfold pred. simpl in H0. 
       remember (ble_nat (length l) n) as ble. destruct ble;inversion H0. 
       remember (ble_nat (length l) n0) as ble. destruct ble; inversion H1. apply bleSF1 in Heqble1.
       rewrite<- Heqble1. destruct l. inversion H3. simpl in Heqble,Heqble0.
       rewrite OT6;try simpl;try apply Heqble; try apply Heqble0.
       split;try exists (insert1 n a (delete1 n0 (a0 :: l)));reflexivity.
  Case "ins,id".
   simpl. inversion H. inversion H. inversion H1. apply insert_len in H2.
    simpl in H0. unfold insert. unfold insert in H0. rewrite <- H5.
    destruct (ble_nat (S (length l)) n);inversion H0.
    split;try exists (insert1 n a l);reflexivity.
  Case "delete,ins".
   inversion H. inversion H. apply insert_len in H3. apply delete_len in H2.
    unfold OT. simpl. simpl in H0,H1. unfold insert,delete in H0,H1. 
    remember (ble_nat n0 n) as ble. destruct ble.
    SCase "n0<=n".
     simpl. unfold insert,delete. rewrite <-H2,<-H3. simpl. 
      remember (ble_nat (length l) n) as ble. destruct ble;inversion H0.
      inversion Heqble0. apply ble_nat_negtrans1 with (n0:=n0) in H6;try apply Heqble.
      rewrite <- H6. apply bleSF1 in H6. rewrite <- H6 in H1. inversion H1. rewrite OT7;try apply Heqble.
      split;try exists (match insert1 n0 a l with | [] => [] | h :: l' => h :: delete1 n l' end);reflexivity.
    SCase "n0>n".
     simpl. unfold insert,delete. rewrite <-H2,<-H3. destruct n0. inversion Heqble. unfold pred.
      remember (ble_nat (length l) n) as ble. destruct ble;inversion H0. inversion Heqble0.
      apply bleSF1 in H6. rewrite <- H6. simpl in H1. destruct (ble_nat (length l) n0);
      inversion H1. destruct l. inversion H2. simpl in Heqble, Heqble0. 
      rewrite OT8;simpl;try apply Heqble;try apply Heqble0. 
      split;try exists (delete1 n (a0 :: insert1 n0 a l));reflexivity.
  Case "del,del".
   inversion H. inversion H. apply delete_len in H3. apply delete_len in H2.
   unfold OT. simpl. simpl in H0,H1. unfold delete in H0,H1. 
   remember (beq_nat n n0) as beq. destruct beq.
    SCase "n=n0".
     apply beq_nat_eq in Heqbeq. rewrite <-Heqbeq. rewrite <- Heqbeq in H1.
     rewrite <- beq_nat_refl. simpl. destruct (ble_nat (length l) n); inversion H0.
     inversion H1. split;try exists (delete1 n l);reflexivity.
    SCase "n!=n0".
     remember (ble_nat n0 n) as ble. destruct ble.
      SSCase "n0<=n".
       inversion Heqble. apply ble_nat_neg0 in H5;try apply Heqbeq. rewrite <- H5.
       rewrite beq_nat_sym in Heqbeq. rewrite<-Heqbeq. simpl. unfold delete.
       destruct n. inversion H5. destruct l;inversion H2;inversion H3.
       unfold pred. simpl in H0,H1. remember (ble_nat (length l) n) as ble.
       destruct ble;inversion H0. inversion H5.
       remember (beq_nat (length l) (S n)) as beq. destruct beq.
        apply beq_nat_eq in Heqbeq0. rewrite Heqbeq0. rewrite <- H5.   
        rewrite Heqbeq0 in H1. 
        remember (match n0 with | 0 => false | S m' => ble_nat (S n) m' end) as mat.
        destruct mat; inversion H1.  rewrite OT11; try apply H5; try apply Heqbeq0.
        split;try exists (delete1 n (delete1 n0 (a :: l)));reflexivity.
       inversion Heqble0. 
        replace (ble_nat (length l) n) with  (ble_nat (S (length l)) (S n)) in H10 by reflexivity.
        apply ble_nat_neg3 in H10; try apply Heqbeq0.
        replace (match n0 with| 0 => false | S m' => ble_nat n m' end) with (ble_nat (S n) n0) in H9 by reflexivity.
        apply ble_nat_negtrans with (n0:=length l) in H9; try apply H10.
        rewrite <- H9. destruct (match n0 with | 0 => false| S m' => ble_nat (length l) m' end);inversion H1.
        rewrite OT9; try apply H5; try apply Heqble0. 
        split;try exists (delete1 n (delete1 n0 (a :: l)));reflexivity.
      SSCase "n0>n".
       rewrite beq_nat_sym in Heqbeq. rewrite <- Heqbeq.
       inversion Heqble. apply ble_nat_neg in H5. rewrite <- H5. simpl.
       destruct n0. inversion Heqble. unfold pred. unfold delete.
       destruct l; inversion H2; inversion H3. simpl in H1.
       remember (ble_nat (length l) n0) as ble. destruct ble; inversion H1.
       replace (ble_nat (length (a :: l)) n) with (ble_nat (S (length l)) n) in H0 by reflexivity.
       remember (ble_nat (S (length l)) n) as ble. destruct ble; inversion H0.
       remember (beq_nat (length l) n) as beq. destruct beq.
        apply beq_nat_eq in Heqbeq0. rewrite Heqbeq0 in Heqble1, Heqble0.
         apply ble_nat_beq in Heqble0; try apply H5. rewrite beq_nat_sym in Heqble0.
         rewrite <-Heqble0 in Heqbeq. inversion Heqbeq.
        apply ble_nat_neg3 in Heqble1; try apply Heqbeq0. rewrite <-Heqble1.
         rewrite OT10; try apply Heqble1; try apply Heqble.
         split;try exists (delete1 n (a :: delete1 n0 l));reflexivity.
  Case "del,id".
   inversion H. inversion H. apply delete_len in H2. simpl. unfold delete. simpl in H0,H1.
    unfold delete in H0. inversion H1. rewrite<- H5. destruct (ble_nat (length l) n); inversion H0.
    split;try exists (delete1 n l);reflexivity.
  Case "id,ins".
   simpl. inversion H. inversion H. apply insert_len in H3. unfold insert. simpl in H0,H1.
    unfold insert in H1. inversion H0. rewrite<- H5. destruct (ble_nat (S(length l)) n); inversion H1.
    split;try exists (insert1 n a l);reflexivity.
  Case "id,del".
   inversion H. inversion H. apply delete_len in H3. simpl. unfold delete. simpl in H0,H1.
    unfold delete in H1. inversion H0. rewrite<- H5. destruct (ble_nat (length l) n); inversion H1.
    split;try exists (delete1 n l);reflexivity.
  Case "ins,ins".
   simpl. inversion H. inversion H0. inversion H1. rewrite <- H3,<-H4.
     split. reflexivity. exists (l). reflexivity.
Qed.