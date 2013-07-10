Require Export "Ascii". 
Require Export "Prop".
(*
Require Export "Prop".
Require Export "Datatypes". 
*)
Open Scope char_scope.

Inductive function : Type:=
  |fInsert: nat -> ascii->function 
  |fDelete: nat -> function 
  |fId: function.

Fixpoint beq_ascii n m : bool :=
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

Fixpoint insert n x (l:list ascii): option (list ascii):=
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

Fixpoint delete n (l:list ascii): option (list ascii):=
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
  intros n0.
  induction n0.
  Case "n0=0".
   intros. 
   inversion H.
  Case "n0=S n0".
   intros.
   destruct n1.
   reflexivity.
   simpl.
   apply IHn0.
   inversion H.
   reflexivity.
Qed.

Theorem ble_nat_trans : forall (n0 n1 n2 : nat),true=ble_nat n0 n1->
true = ble_nat n1 n2-> true=ble_nat n0 n2.
Proof.
  intros n0.
  induction n0.
  Case "n0=0".
   intros.
   reflexivity.
  Case "n0=S n0".
   intros.
   destruct n2.
   destruct n1.
   inversion H.
   inversion H0.
   simpl.
   destruct n1.
   inversion H.
   apply IHn0 with (n1:=n1).
   inversion H.
   reflexivity.
   inversion H0.
   reflexivity.
Qed.
  
Theorem ble_nat_negtrans : forall (n0 n1 n2 : nat),false=ble_nat n0 n1->
false = ble_nat n1 n2-> false=ble_nat n0 n2.
Proof.
  intros n0.
  induction n0.
  Case "n0=0".
   intros.
   inversion H.
  Case "n0=S n0".
   intros.
   destruct n2.
   destruct n1.
   inversion H.
   inversion H0.
   simpl.
   reflexivity.
   destruct n1.
   inversion H0.
   apply IHn0 with (n1:=n1).
   inversion H.
   reflexivity.
   inversion H0.
   reflexivity.
Qed.

Theorem beq_ascii_sym : forall (n1 n2 : ascii),beq_ascii n1 n2=beq_ascii n2 n1.
Proof.
Admitted.

Theorem beq_ascii_eq : forall (n1 n2 : ascii),true = beq_ascii n1 n2 -> n1=n2.
Proof.
Admitted.

Theorem ins_len : forall (a:ascii) (n:nat) (l:list ascii),false = ble_nat (S(length l)) n-> length (insert1 n a l)=S (length l).
Proof.
  intros a n.
  induction n.
  intros.
  simpl H.
  destruct l.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  intros.
  destruct l as [| h l'].
  simpl in H.
  inversion H.
  simpl.
  apply eq_remove_S.
  apply IHn.
  rewrite H.
  simpl.
  reflexivity.
Qed.

Theorem ble_neg : forall n n0 ,  false = beq_nat  n n0 ->true = ble_nat n0 n ->false=ble_nat n n0. 
Proof.
  intros n.
  induction n.
  intros.
  destruct n0.
  inversion H.
  inversion H0.
  intros.
  destruct n0.
  reflexivity.
  simpl.
  apply IHn.
  simpl in H,H0.
  apply H.
  simpl in H0.
  apply H0.
Qed.
  

Theorem ble_neg' : forall n n0 ,  false = beq_nat  n n0 ->false = ble_nat n0 n ->true=ble_nat n n0. 
Proof.
  intros n.
  induction n.
  intros.
  reflexivity.
  intros.
  destruct n0.
  inversion H0.
  simpl.
  apply IHn.
  simpl in H,H0.
  apply H.
  simpl in H0.
  apply H0.
Qed.

Theorem bleSF : forall n1 n2 , false = ble_nat n1 (S n2)->false = ble_nat n1 (n2).
Proof.
  intros n1.
  induction n1.
  simpl.
  intros.
  inversion H.
  intros.
  destruct n2.
  simpl.
  reflexivity.
  simpl.
  apply IHn1.
  simpl in H.
  apply H.
Qed.

Theorem bleST : forall n1 n2 , true = ble_nat (S n1) n2 ->true = ble_nat n1 n2.
Proof.
  intros n1.
  induction n1.
  simpl.
  intros.
  destruct n2.
  inversion H.
  reflexivity.
  intros.
  destruct n2.
  inversion H.
  simpl.
  simpl in H.
  apply IHn1.
  apply H.
Qed.


Theorem bleSF1 : forall n1 n2 , false = ble_nat n1 n2 ->false = ble_nat (S n1) n2.
Proof.
  intros n1.
  induction n1.
  simpl.
  intros.
  inversion H.
  intros.
  destruct n2.
  simpl.
  reflexivity.
  simpl.
  apply IHn1.
  simpl in H.
  apply H.
Qed.

Theorem OT1 : forall n a l l1,apply (fInsert n a) l = Some l1->S (length l)=length l1.
Proof.
  intros n a l.
  generalize n.
  induction l.
  Case "l=[]".
   simpl.
   intros.
   destruct l1.
   destruct n0.
    simpl in H.
    inversion H.
    inversion H.
   simpl.
   destruct n0.
    simpl in H.
    inversion H.
    reflexivity.
    inversion H.
  Case "l=x::l".
   simpl.
   destruct l1.
    intros.
    destruct n0.
     simpl in H.
     inversion H.
     inversion H.
    simpl in H.
    destruct n0.
     simpl in H.
     inversion H.
     destruct (ble_nat (length l) n0).
      inversion H.
      inversion H.
    simpl.
    intros.
    apply eq_remove_S.
    destruct n0.
    simpl in H.
    inversion H.
    reflexivity.
    apply IHl with (n:=n0).
    simpl.
    simpl in H.
    destruct n0.
    inversion H.
    reflexivity.
    simpl in H.
    simpl.
     destruct (ble_nat (length l) n0).
      inversion H.
      inversion H.
      reflexivity.
Qed.
  
  
Theorem OT2 : forall n0 a a0 l,insert1 n0 a0 (insert1 n0 a l) =match insert1 n0 a0 l with
            | [] => []
            | h :: l' => h :: insert1 n0 a l'
            end.
Proof.
  intros.
  generalize n0.
  induction l.
  intros.
  destruct n1.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  intros.
  destruct n1.
  simpl.
  reflexivity.
  simpl.
  rewrite IHl.
  reflexivity.
Qed.
  
Theorem OT3 : forall n n0 a a0 l,true=ble_nat n0 n->insert1 n0 a0 (insert1 n a l) = match insert1 n0 a0 l with
         | [] => []
         | h :: l' => h :: insert1 n a l'
         end.
  intros.
  generalize dependent n0.
  generalize dependent n.
  induction l.
  intros.
  destruct n0,n.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  inversion H.
  simpl.
  reflexivity.
  simpl.
  intros.
  destruct n0,n.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  inversion H.
  simpl.
  rewrite IHl.
  reflexivity.
  simpl in H.
  apply H.
Qed.

Theorem OT4 : forall n n0 a a0 l,false = ble_nat n0 n->insert1 (S n0) a0 (insert1 n a l) =
insert1 n a (insert1 n0 a0 l).  
Proof.
  intros.
  generalize dependent n0.
  generalize dependent n.
  induction l.
  intros.
  destruct n0,n.
  simpl.
  reflexivity.
  simpl.
  inversion H.
  simpl.
  reflexivity.
  simpl.
  reflexivity.
  intros.
  destruct n0,n.
  simpl.
  reflexivity.
  simpl.
  inversion H.
  reflexivity.
  simpl.
  rewrite <-IHl.
  simpl.
  reflexivity.
  simpl in H.
  apply H.
Qed.

Theorem OT_ : forall (f1 f2:function) (b1 b2: bool) (l l1 l2:list ascii),((apply f1 l)=Some l1 
 /\ (apply f2 l) =Some l2)-> (apply (OT f1 f2 false) l1 =apply (OT f2 f1 true) l2/\exists l3,apply (OT f2 f1 true) l2=Some l3).
Proof.
  intros.
  destruct f1,f2.
  Case "f1=inv, f2=inv".
    inversion H.
    unfold OT.
    unfold function_eq.
    remember (beq_nat n n0) as beq.
    destruct beq.
    SCase "beq_nat n n0=true".
     rewrite beq_nat_sym.
     rewrite <- Heqbeq.
     simpl.
     remember (beq_ascii a a0) as beqa.
     destruct beqa.
     SSCase "beq_ascii a a0=true".
      rewrite beq_ascii_sym.
      rewrite <- Heqbeqa.
      apply beq_nat_eq in Heqbeq.
      rewrite Heqbeq in H0.
      apply beq_ascii_eq in Heqbeqa.
      rewrite Heqbeqa in H0.
      rewrite H0 in H1.
      inversion H1.
      split.
      reflexivity.
      exists l2.
      reflexivity.
     SSCase "beq_ascii a a0=false".
      rewrite beq_ascii_sym.
      rewrite <- Heqbeqa.
      apply beq_nat_eq in Heqbeq.
      rewrite Heqbeq.
      rewrite <- ble_nat_refl.
      simpl.
      remember (ble_nat (length l2) n0) as ble.
      destruct ble.
      SSSCase "true=ble_nat (length l2) n0".
       unfold apply in H1,H0.
       inversion H.
       apply OT1 in H2.
       apply OT1 in H3.
       unfold insert in H0,H1.
       simpl in H0,H1.
       destruct n0.
       inversion H1.
       rewrite <- H5 in Heqble.
       inversion Heqble.
       rewrite <- H3 in Heqble.
       simpl in Heqble.
       rewrite <- Heqble in H1.
       inversion H1.
      SSSCase "false=ble_nat (length l2) n0".
       destruct l2.
       apply OT1 in H1.
       inversion H1.
       split.
       destruct l.
       rewrite Heqbeq in H0.
       destruct n0.
       simpl in H0,H1.
       inversion H1.
       inversion H0.
       simpl.
       reflexivity.
       simpl in H1 ,H0.
       inversion H1.
       simpl in H1,H0.
       rewrite Heqbeq in H0.
       destruct n0.
       simpl in H1,H0.
       inversion H1.
       inversion H0.
       reflexivity.
       simpl in H1,H0.
       destruct n0.
       inversion H1.
       inversion H0.
       simpl.
       rewrite H3.
       reflexivity.
       
       inversion H.
       apply OT1 in H3.
       apply OT1 in H2.
       rewrite <- H3 in Heqble.
       simpl in Heqble.
       rewrite <- Heqble in H1,H0.
       destruct l1.
       inversion H0.
       simpl.
       inversion H2.
       apply bleSF1 in Heqble.
       rewrite <- Heqble.
       inversion H1.
       inversion H0.
       rewrite <- H6,H8.
       destruct l.
       reflexivity.
       remember (ble_nat (S (length l)) n0) as ble.
       destruct ble.
       unfold ble_nat in Heqble0.
       rewrite OT2.
       reflexivity.
       rewrite OT2.
       reflexivity.
       exists (a1 :: insert1 n0 a l2).
       reflexivity.
    SCase "beq_nat n n0=false".
     inversion H.
     apply OT1 in H3.
     apply OT1 in H2.
     simpl.
     rewrite beq_nat_sym.
     rewrite <-Heqbeq.
     simpl.
     remember (ble_nat n0 n) as ble.
     destruct ble.
     SSSCase "true=ble_nat n0 n".
      simpl.
      remember (ble_nat (length l2) n) as ble.
      destruct ble.
      SSSSCase "true = ble_nat (length l2) n".
      simpl in H1,H0.
      rewrite <- H3 in Heqble0.
      unfold insert in H1.
      destruct n, l.
      inversion Heqble0.
      inversion Heqble0.
      simpl in H0.
      inversion H0.
      simpl in  Heqble0.
      simpl in H0.
      rewrite <- Heqble0 in H0.
      inversion H0.
      SSSSCase "false = ble_nat (length l2) n".
       split.
       destruct l,l1,l2,n,n0.
       (*2^5-1 easy goals*)
       inversion Heqbeq.
       inversion Heqble.
       inversion H1.
       inversion H0.
       inversion H0.
       inversion H1.
       inversion H0.
       inversion H1.
       inversion Heqbeq.
       inversion Heqble.
       inversion Heqble0.
       inversion Heqble0.
       inversion Heqbeq.
       inversion Heqble.
       inversion H0.
       inversion H1.
       inversion Heqbeq.
       inversion Heqble.
       inversion H2.
       inversion H2.
       inversion H2.
       inversion H2.
       inversion H2.
       inversion H2.
       inversion H3.
       inversion Heqble.
       inversion H3.
       inversion H3.
       inversion Heqbeq.
       inversion Heqble.
       simpl in H1,H0.
       destruct n.
        inversion H1.
        inversion H0.
        simpl.
        reflexivity.
       destruct (ble_nat (length l) n).
       inversion H0.
       inversion H0.
       inversion H1.
       simpl.
       destruct l.
        inversion H.
        inversion H4.
       simpl.
       destruct n.
       rewrite H5.
       reflexivity.
       rewrite H5.
       simpl in H2,H3,Heqble0.
       inversion H3.
       rewrite <- H9 in Heqble0.
       simpl in H2,H3,Heqble0.
       rewrite<-Heqble0.
       reflexivity.
       (*2^5'th goal*)
       simpl.
       destruct n0.
       inversion H1.
       inversion H0.
       destruct n.
       inversion Heqbeq.
       simpl.
       destruct l.
       inversion H7.
       destruct (ble_nat (length (a4 :: l)) n).
       inversion H7.
       inversion H7.
       rewrite <- H5,H8.
       reflexivity.
       remember (ble_nat (length l1) n0) as ble.
       destruct ble.
       inversion H1.
       simpl in H2,H3.
       inversion H2.
       rewrite <- H6 in Heqble1.
       apply bleST in Heqble1.
       rewrite <- Heqble1 in H5.
       inversion H5.
       inversion H0.
       inversion H1.
       destruct ( ble_nat (length l) n0).
       inversion H6.
       destruct n.
       inversion Heqble.
       destruct ( ble_nat (length l) n).
       inversion H5.
       inversion H5.
       inversion H6.
       destruct l.
       rewrite <- H8 in Heqble1.
       inversion Heqble1.
       simpl.
       simpl in Heqble,Heqbeq.
       apply ble_neg in Heqbeq. 
       rewrite <- Heqbeq.
       simpl.
       rewrite <- H10 in Heqble0.
       simpl in Heqble0.
       rewrite <- Heqble0.
       rewrite OT3.
       rewrite <- H7,H9.
       reflexivity.
       apply Heqble.
       apply Heqble.
       simpl.
       apply ble_neg in Heqbeq. 
       rewrite <- Heqbeq.
       simpl.
       rewrite <- Heqble0.
       
       exists (match l2 with
       | [] => []
       | h :: l' => h :: insert1 n a l'
       end).
       reflexivity.
       apply Heqble.
     SSCase "false=ble_nat n0 n".
      rewrite H2 in H3.
      simpl.
      assert (H4:true=ble_nat n n0).
      apply ble_neg'.
      apply Heqbeq.
      apply Heqble.
      rewrite <- H4.
      simpl.
      unfold apply in H0,H1.
      unfold insert in H0,H1.
      remember (ble_nat (length l1) n0) as ble. 
      destruct ble.
      SSSCase "true = ble_nat (length l1) n0".
       destruct l,n.
       simpl in H0.
       destruct n0.
       inversion Heqble.
       inversion H1.
       destruct n0.
       inversion Heqble.
       inversion H1.
       simpl in H0.
       destruct n0.
       inversion Heqbeq.
       simpl in H1.
       destruct n0.
       rewrite <- H2 in Heqble0.
       inversion Heqble0.
       rewrite<- H2 in Heqble0.
       inversion Heqble0.
       rewrite <- H6 in H1.      
       inversion H1.
       inversion Heqble0.
       destruct n0.
       inversion Heqble.
       rewrite H2 in H1.
       rewrite <- Heqble0 in H1.
       inversion H1.
      SSSSCase "false = ble_nat (length l2) n".
       destruct l,l1,l2,n,n0.
       (*2^5-1 easy goals*)
       inversion Heqbeq.
       inversion H2.
       inversion Heqble.       
       inversion H1.      
       inversion Heqbeq. 
       inversion H1.
       inversion H0.
       inversion H0.      
       inversion Heqbeq. 
       inversion H1.
       inversion H0.
       inversion H0.      
       inversion Heqbeq.      
       inversion H1.      
       inversion Heqble.      
       inversion H0.      
       inversion Heqbeq.      
       inversion H2.      
       inversion Heqble.
       inversion H2.      
       inversion Heqbeq.
       inversion H2.      
       inversion Heqble.      
       inversion H2.      
       inversion Heqbeq.      
       inversion H3.      
       inversion Heqble.      
       inversion H3.      
       inversion Heqbeq.
       simpl in H1,H0.
        destruct n0.
        inversion H1.
        inversion H0. 
        simpl.
        split.
        rewrite <- H6.
        reflexivity.
        exists (a2 :: a3 :: a0 :: l).
        reflexivity.
       
       simpl.
        split.
        destruct l1.
        inversion H2.
        destruct l1.
        rewrite <-H2 in Heqble0.
        simpl in Heqble0.
        rewrite <-Heqble0 in H1.
        inversion H0.
        inversion H.
        rewrite H8 in H9.
        unfold apply in H9.
        unfold insert in H9.
        simpl H9.
        unfold length in  H9.
        simpl in H9.
        inversion H9.
        inversion H2.
        replace (length (a2 :: a4 :: a5 :: l1)) with (S(S(length l))) in Heqble0.
        simpl in Heqble0.
        rewrite <- Heqble0 in H1.
        destruct l.
        inversion H6.
        inversion H1.
        inversion H0.
        rewrite <-H10,H7.
        reflexivity.
        exists ((a :: a3 :: l2)).
        reflexivity.
        inversion Heqble.
       (*2^5'th goal*)
        split.
        simpl in H1,H0.
        destruct n,n0.
        inversion Heqbeq.
        simpl in Heqble0,H2.
        inversion H2.
        rewrite <-H6 in Heqble0.
        simpl in Heqble0.
        rewrite <- Heqble0 in H1.
        destruct l.
        inversion Heqble0.
        inversion H1.
        inversion H0.
        simpl.
        rewrite<- H7,H9.
        reflexivity.        
        inversion Heqble.

        simpl in Heqble0.
        inversion H2.
        rewrite <- H6 in Heqble0.
        simpl in Heqble0.
        rewrite <- Heqble0 in H1.
        inversion Heqble.
        apply ble_nat_negtrans with (n0:=length l) in H7.
        rewrite<-H7 in H0.
        destruct l.
        destruct n0.
        inversion Heqble.
        inversion Heqble0.
        inversion H1.
        inversion H0.
        simpl.
        destruct n.
        simpl.
        rewrite<- H8,H10.
        reflexivity.
        destruct l1,l2.
        inversion H9.
        inversion H11.
        inversion H9.
        inversion H9.
        inversion H11.
        destruct l.
        inversion H.
        inversion H5.
        inversion H6.
        inversion H3.
        replace (length (a4 :: a7 :: l)) with (length l1)in H7.
        inversion H7.
        apply bleSF in H18.
        rewrite H13.
        rewrite <-H17.
        rewrite <-H18.
        rewrite <- H13.
        simpl.
        destruct n0.
        inversion H4.
        replace ( match insert1 (S n0) a0 (a7 :: l) with
         | [] => []
         | h :: l' => h :: insert1 n a l'
         end) with (a7:: (insert1 n a(insert1 n0 a0  l))).
        rewrite OT4.
        rewrite <- H8,H10.
        reflexivity.
        simpl in Heqble.
        apply Heqble.
        simpl.
        reflexivity.
        apply Heqble0.
        simpl.
        destruct n.
        exists (a3 :: insert1 0 a l2).
        reflexivity.
        rewrite H3 in Heqble0.
        destruct n0.
        inversion H4.
        simpl in Heqble,Heqble0.
        apply ble_nat_negtrans with (n0:=length l2) in Heqble.
        rewrite <- Heqble.
        exists (a3 :: insert1 (S n) a l2).
        reflexivity.
        apply bleSF.
        apply Heqble0.
  Case "f1=inv, f2=del".
   inversion H.
   inversion H.
   apply OT1 in H2.
   apply OT5 in H3.

   unfold OT.
   simpl.
   remember (ble_nat n n0) as ble.
   destruct ble.
    SCase "true = ble_nat n n0".
     simpl.
     remember (ble_nat (length l1) (S n0)) as ble.
     destruct ble.
     SSCase (true = ble_nat (length l1) (S n0)).
     
     SSCase (false = ble_nat (length l1) (S n0)).
    SCase "false = ble_nat n n0".         
        