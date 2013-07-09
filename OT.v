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
    if orb server (negb(ble_nat n2 n1)) (*server or n1<n2*)
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
Theorem beq_nat_com : forall (n1 n2 : nat),beq_nat n1 n2=beq_nat n2 n1.
Proof.
  intros n1.
  induction n1.
  Case "n1=0".
   intros. 
   destruct n2. reflexivity. reflexivity.
  Case "n1=S n1".
   intros.
   destruct n2.
   reflexivity.
   simpl.
   apply IHn1.
Qed.
  
Theorem beq_ascii_com : forall (n1 n2 : ascii),beq_ascii n1 n2=beq_ascii n2 n1.
Proof.
Admitted.

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
(*
Theorem T0 : forall n0 a a0 l,insert1 n0 a0 (insert1 n0 a l) =match insert1 n0 a0 l with
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
  
Theorem T1 : forall n0 x a1 a a0 l,
insert (S (S n0)) a0 (x :: a1 :: insert1 n0 a l) =
insert (S (S (S n0))) a (x :: a1 :: insert1 n0 a0 l).
Proof.
  intros.
*)(*
Theorem OT_ : forall (f1 f2:function) (b1 b2: bool) (l:option (list ascii)), 
  excluded_middle ->xor_boolToProp b1 b2-> apply (OT f1 f2 b1) (apply f1 l)=apply (OT f2 f1 b2) (apply f2 l).
Proof.
  intros.
  unfold excluded_middle in H.
  unfold not in H.
  destruct f1, f2.
  Case "f1=inv, f2=inv".
   destruct H0.
   SCase "b1 = false /\ b2 = true".
    inversion H0.
    rewrite H1.
    rewrite H2.
    unfold OT.
    unfold function_eq.
    remember (beq_nat n n0) as beq.
    destruct beq.
    SSCase "beq_nat n n0=true".
     rewrite beq_nat_com.
     rewrite <- Heqbeq.
     simpl.
     remember (beq_ascii a a0) as beqa.
     destruct beqa.
     SSSCase "beq_ascii a a0=true".
      rewrite beq_ascii_com.
      rewrite <- Heqbeqa.
      apply beq_nat_eq in Heqbeq.
      rewrite Heqbeq.
      apply beq_ascii_eq in Heqbeqa.
      rewrite Heqbeqa.
      reflexivity.
     SSSCase "beq_ascii a a0=false".
      rewrite beq_ascii_com.
      rewrite <- Heqbeqa.
      apply beq_nat_eq in Heqbeq.
      rewrite Heqbeq.
      rewrite <- ble_nat_refl.
      simpl.
      destruct l.
      SSSSCase "l=Some l".
      remember (ble_nat (S(length l)) n0) as ble.
      destruct ble.
      simpl.
      unfold insert .
      simpl.
      destruct n0.
      simpl.
      reflexivity.
      simpl in Heqble.
      rewrite <-Heqble.
      simpl.
      reflexivity.
      simpl.
      generalize dependent n0.
      induction l.
      intros.
      destruct n0.
      simpl.
      reflexivity.
      simpl.
      reflexivity.
      intros.
      destruct n0.
      simpl.
      reflexivity.
      simpl.
      destruct n0.
      simpl.
      reflexivity.
      simpl.
      simpl in Heqble.
      rewrite <-Heqble.
      unfold apply.
      destruct l.
      inversion Heqble.
      simpl.
      destruct n0.
      replace (length (a1 :: l)) with (S (length l)) in Heqble.
      apply ins_len with (a:=a0) in Heqble.
      rewrite Heqble.
      simpl.
      reflexivity.
      simpl.
      reflexivity.
      replace (length (a1 :: l)) with (S (length l)) in Heqble.
      rewrite ins_len with (a:=a).
      rewrite ins_len with (a:=a0).
      rewrite <- Heqble.
      inversion Heqble.
      apply bleSF in Heqble.
      rewrite <- Heqble.
      destruct l.
      simpl.
      reflexivity.
      simpl.
      rewrite T0.
      reflexivity.
      apply Heqble.
      apply Heqble.
      reflexivity.
      simpl.
      reflexivity.
    SSCase "beq_nat n n0=false".
     simpl.
     rewrite beq_nat_com.
     rewrite <- Heqbeq.
     simpl.
     remember (ble_nat n0 n) as ble.
     destruct ble.
     SSSCase "true=ble_nat n0 n".
      simpl.
      destruct l.
      SSSSCase "l=Some l".
(**)
       destruct n.
       simpl.
       destruct n0.
       simpl.
       reflexivity.
       destruct l.
       simpl.
       destruct n0.
       simpl.
      SSSSCase "l=None".
     SSSCase "false=ble_nat n0 n".
     
*)
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
  
  
  
Theorem OT_ : forall (f1 f2:function) (b1 b2: bool) (l l1 l2:list ascii),xor_boolToProp b1 b2->((apply f1 l)=Some l1 
 /\ (apply f2 l) =Some l2)-> (apply (OT f1 f2 b1) l1 =apply (OT f2 f1 b2) l2/\exists l3,apply (OT f2 f1 b2) l2=Some l3).
Proof.
  intros.
  inversion H0.
  destruct f1,f2.
  Case "f1=inv, f2=inv".
   destruct H.
   SCase "b1 = false /\ b2 = true".
    inversion H.
    rewrite H3.
    rewrite H4.
    unfold OT.
    unfold function_eq.
    remember (beq_nat n n0) as beq.
    destruct beq.
    SSCase "beq_nat n n0=true".
     rewrite beq_nat_com.
     rewrite <- Heqbeq.
     simpl.
     remember (beq_ascii a a0) as beqa.
     destruct beqa.
     SSSCase "beq_ascii a a0=true".
      rewrite beq_ascii_com.
      rewrite <- Heqbeqa.
      apply beq_nat_eq in Heqbeq.
      rewrite Heqbeq in H1.
      apply beq_ascii_eq in Heqbeqa.
      rewrite Heqbeqa in H1.
      rewrite H1 in H2.
      inversion H2.
      split.
      reflexivity.
      exists l2.
      reflexivity.
     SSSCase "beq_ascii a a0=false".
      rewrite beq_ascii_com.
      rewrite <- Heqbeqa.
      apply beq_nat_eq in Heqbeq.
      rewrite Heqbeq.
      rewrite <- ble_nat_refl.
      simpl.
      remember (ble_nat (length l2) n0) as ble.
      destruct ble.
      SSSSCase "true=ble_nat (length l2) n0".
       unfold apply in H2.
       inversion H0.
       apply OT1 in H6.
       unfold insert in H2.
       simpl in H2.
       destruct n0.
       inversion H2.
       rewrite <- H6 in Heqble.
       inversion Heqble.
       rewrite <- H6 in Heqble.
       simpl in Heqble.
       rewrite <- Heqble in H2.
       inversion H2.
      SSSSCase "false=ble_nat (length l2) n0".
       destruct l2.
       apply OT1 in H2.
       inversion H2.
       split.
       destruct l1.
       




       simpl H2.
       rewrite H6 in H2.
       apply OT1 in H1.
unfold insert .
      simpl.
      destruct n0.
      simpl.
      reflexivity.
      simpl in Heqble.
      rewrite <-Heqble.
      simpl.
      reflexivity.
      simpl.
      generalize dependent n0.
      induction l.
      intros.
      destruct n0.
      simpl.
      reflexivity.
      simpl.
      reflexivity.
      intros.
      destruct n0.
      simpl.
      reflexivity.
      simpl.
      destruct n0.
      simpl.
      reflexivity.
      simpl.
      simpl in Heqble.
      rewrite <-Heqble.
      unfold apply.
      destruct l.
      inversion Heqble.
      simpl.
      destruct n0.
      replace (length (a1 :: l)) with (S (length l)) in Heqble.
      apply ins_len with (a:=a0) in Heqble.
      rewrite Heqble.
      simpl.
      reflexivity.
      simpl.
      reflexivity.
      replace (length (a1 :: l)) with (S (length l)) in Heqble.
      rewrite ins_len with (a:=a).
      rewrite ins_len with (a:=a0).
      rewrite <- Heqble.
      inversion Heqble.
      apply bleSF in Heqble.
      rewrite <- Heqble.
      destruct l.
      simpl.
      reflexivity.
      simpl.
      rewrite T0.
      reflexivity.
      apply Heqble.
      apply Heqble.
      reflexivity.
      simpl.
      reflexivity.
    SSCase "beq_nat n n0=false".
     simpl.
     rewrite beq_nat_com.
     rewrite <- Heqbeq.
     simpl.
     remember (ble_nat n0 n) as ble.
     destruct ble.
     SSSCase "true=ble_nat n0 n".
      simpl.
      destruct l.
      SSSSCase "l=Some l".
  