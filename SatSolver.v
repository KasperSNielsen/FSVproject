Require Import SAT.project_lib.

(* Exercise 2.1 *)
Inductive form :=
  | f_var : id -> form
  | f_true : form
  | f_false : form
  | f_and : form -> form -> form
  | f_or : form -> form -> form
  | f_impl : form -> form -> form
  | f_neg : form -> form.

(* Custom Notation *)
Declare Custom Entry sat.
Notation "<{ e }>" := e (e custom sat at level 99).
Notation "( x )" := x (in custom sat, x at level 99).
Notation "x" := x (in custom sat at level 0, x constr at level 0).
Notation "x -> y" := (f_impl x y) (in custom sat at level 70, right associativity).
Notation "x /\ y" := (f_and x y) (in custom sat at level 40, left associativity).
Notation "x \/ y" := (f_or x y) (in custom sat at level 50, left associativity).
Notation "~ x" := (f_neg x) (in custom sat at level 30).
Notation "'true'"  := true (at level 1).
Notation "'true'" := f_true (in custom sat at level 0).
Notation "'false'"  := false (at level 1).
Notation "'false'" := f_false (in custom sat at level 0).
Coercion f_var : id >-> form.

Definition x : id := (Id 0).
Definition y : id := (Id 1).
Definition z : id := (Id 2).
Local Hint Unfold x : core.
Local Hint Unfold y : core.
Local Hint Unfold z : core.

(* Exercise 2.2 *)
Definition twotwoone := <{(x \/ ~y) /\ (~x \/ y)}>.
Definition twotwotwo := <{ ~y -> (x \/ y) }> .
Definition twotwothree := <{ x /\ ~x /\ true }>.

Definition valuation := id -> bool .
Definition empty_valuation : valuation := fun x => false .
Definition override (V : valuation ) (x : id) (b : bool ) : valuation :=
  fun y => if beq_id x y then b else V y.

Fixpoint interp (V : valuation) (p : form ) : bool :=
  match p with
  | f_true => true
  | f_false => false
  | f_var x => V x
  | <{ x /\ y }> => (interp V x) && (interp V y)
  | <{ x \/ y }> => (interp V x) || (interp V y)
  | <{ ~x }> => negb (interp V x)
  | <{ x -> y }> => negb (interp V x) || (interp V y)
  end.

Notation "'Ø'" := empty_valuation.
Notation "m '|[' x '|->' v ']|'" := (override m x v)  (at level 100, v at next level, right associativity).

Definition testval := Ø|[x |-> false]||[y |-> true]||[z |-> true]|.

Example interp_test1 : interp testval twotwoone = false. 
Proof. reflexivity. Qed.

Example interp_test2 : interp testval twotwotwo = true. 
Proof. reflexivity. Qed.

Example interp_test3 : interp testval twotwothree = false. 
Proof. reflexivity. Qed.

Definition satisfiable (p : form ) : Prop := exists V : valuation , interp V p = true .

Lemma test1 : satisfiable twotwoone .
Proof. 
  unfold satisfiable, twotwoone. exists Ø. reflexivity.
Qed.

Lemma test2 : satisfiable twotwotwo .
Proof.
  unfold satisfiable, twotwotwo. exists (Ø|[ x |-> true]|). reflexivity.
Qed.

Fixpoint set_add (x : id) (l : list id) :=
  match l with
  | nil => [x]
  | a :: l' => if beq_id a x then l else a :: (set_add x l')
  end.

Fixpoint set_union (l1 l2 : list id) : list id :=
  match l1 with
  | nil => l2
  | x :: l' => set_add x (set_union l' l2)
  end.

Fixpoint occuring_vars (p : form) : list id :=
  match p with
  | f_true => nil
  | f_false => nil
  | f_var x => [x]
  | <{ x /\ y }> => set_union (occuring_vars x) (occuring_vars y)
  | <{ x \/ y }> => set_union (occuring_vars x) (occuring_vars y)
  | <{ ~x }> => (occuring_vars x)
  | <{ x -> y }> => set_union (occuring_vars x) (occuring_vars y)
  end.

Compute occuring_vars twotwoone.

Print map.

Fixpoint allValuations (l : list id) : list valuation :=
  match l with
  | nil => [empty_valuation]
  | x :: l' => let lv := allValuations l' in (map (fun V => override V x false) lv) ++ (map (fun V => override V x true) lv) 
  end.

Compute length (allValuations (occuring_vars twotwoone)).

Fixpoint find_valuation_helper (p : form) (l : list valuation) : option valuation :=
  match l with
  | nil => None
  | v :: l' => if interp v p then Some v else find_valuation_helper p l'
  end.

Definition find_valuation (p : form ) : option valuation :=
  find_valuation_helper p (allValuations (occuring_vars p)).

Compute find_valuation twotwoone.
Compute find_valuation twotwothree.

Definition solver (p : form ) : bool :=
  match find_valuation p with
  | Some _ => true
  | None => false
  end.

  (* Explained *)

Example two7pos1 : solver twotwoone = true.
Proof. reflexivity. Qed.

Example two7pos2 : solver twotwotwo = true.
Proof. reflexivity. Qed.

Example two7neg1 : solver twotwothree = false.
Proof. reflexivity. Qed.

Example two7neg2 : solver <{ (x \/ y) /\ (~x \/ y) /\ (x \/ ~y) /\ (~x \/ ~y)  }> = false.
Proof. reflexivity. Qed.

Lemma solver_sound_helper : forall l p v, find_valuation_helper p l = Some v -> interp v p = true.
Proof. intros l. induction l; intros.
  - easy.
  - cbn in H. destruct (interp a p) eqn:E. inversion H. subst. auto. apply (IHl _ _ H).
Qed.

Lemma solver_sound : forall p, solver p = true -> satisfiable p.
Proof. intros. unfold satisfiable. unfold solver in H. destruct (find_valuation p) eqn:E; try easy. exists v.
  unfold find_valuation in E. apply solver_sound_helper in E. auto.
Qed.

Lemma solver_complete_help : forall l p v, interp v p = true -> In v l -> exists v', find_valuation_helper p l = Some v'.
Proof. induction l; intros.
  - easy.
  - destruct H0.
    + subst. exists v. cbn. rewrite H. reflexivity.
    + cbn. destruct (interp a p); eauto.
Qed.

Lemma helper : forall l (v: valuation), exists v', In v' (allValuations l) /\ forall x0, In x0 l ->  v x0 = v' x0.
Proof. induction l; intros.
  - exists Ø. split. left. reflexivity. intros. inversion H.
  - destruct (IHl v) as [v']. destruct H. destruct (v a) eqn:E1. 
    + exists (v'|[a |-> true]|). cbn. remember (fun V : valuation => V |[ a |-> true ]|) as f. assert (f v' = (v'|[a |-> true]|)) by (rewrite Heqf; reflexivity).
       split.
        * apply in_app_iff. right. rewrite <- H1. apply in_map. auto.
        * intros. destruct H2.
          -- subst. unfold override. rewrite <- beq_id_refl. apply E1.
          -- apply H0 in H2. destruct (beq_id a x0) eqn:E.
            ++ unfold override. rewrite E. symmetry in E. apply beq_id_eq in E. subst. assumption.
            ++ unfold override. rewrite E. apply H2.
    + exists (v'|[a |-> false]|). cbn. remember (fun V : valuation => V |[ a |-> false ]|) as f. assert (f v' = (v'|[a |-> false]|)) by (rewrite Heqf; reflexivity).
    split.
      * apply in_app_iff. left. rewrite <- H1. apply in_map.  auto.
      * intros. destruct H2.
        -- subst. unfold override. rewrite <- beq_id_refl. apply E1.
        -- apply H0 in H2. destruct (beq_id a x0) eqn:E.
          ++ unfold override. rewrite E. symmetry in E. apply beq_id_eq in E. subst. assumption.
          ++ unfold override. rewrite E. apply H2.
Qed.

Lemma in_set_add: forall x l, In x (set_add x l).
Proof. intros. induction l. 
  - cbn. left. reflexivity.
  - cbn. destruct (beq_id a x0) eqn:E.
    + symmetry in E. apply beq_id_eq in E. subst. left. reflexivity.
    + cbn. right. auto.
Qed.

Lemma in_set_add': forall x a l, In x l -> In x (set_add a l).
Proof. intros. induction l.
      * inversion H.
      * cbn. destruct (beq_id a0 a) eqn:E. auto. destruct H.
        ++ subst. left. reflexivity.
        ++ right. auto.
Qed.

Lemma in_set_union_l: forall x l1 l2, In x l1 -> In x (set_union l1 l2).
Proof. intros. induction l1.
  - inversion H.
  - destruct H.
    + subst. cbn. apply in_set_add.
    + cbn. apply in_set_add'. auto. 
Qed.

Lemma in_set_union_r: forall x l1 l2, In x l2 -> In x (set_union l1 l2).
Proof. intros. induction l1.
  - cbn. auto.
  - cbn. apply in_set_add'. auto. 
Qed.
    
Lemma satisfiable_helper : forall p, satisfiable p -> exists v, In v (allValuations (occuring_vars p)) /\ interp v p = true.
Proof. intros. destruct H as [v]. destruct (helper (occuring_vars p) v) as [v']. destruct H0. exists v'.
  split.
    - apply H0.
    - clear H0. rewrite <- H. clear H. induction p; cbn;
      try reflexivity; try (rewrite <- H1; auto; left; auto);
      try (rewrite IHp1, IHp2; try reflexivity; intros; apply H1; cbn; [ apply in_set_union_r |  apply in_set_union_l]; auto);
      (rewrite IHp; auto).
Qed.

Lemma solver_complete : forall p, satisfiable p -> solver p = true.
Proof. 
  intros. unfold solver, find_valuation. apply satisfiable_helper in H. destruct H. destruct H.
  pose proof (solver_complete_help (allValuations (occuring_vars p)) p x0 H0 H). 
  destruct H1. rewrite H1. reflexivity.
Qed. 

Fixpoint negation_nf_1 p :=
  match p with
  | <{ p1 -> p2 }> => let p1 := (negation_nf_1 p1) in let p2 := (negation_nf_1 p2) in 
    <{ ~ p1 \/ p2 }>
  | <{ p1 /\ p2 }> => let p1 := (negation_nf_1 p1) in let p2 := (negation_nf_1 p2) in 
    <{ p1 /\ p2 }>
  | <{ p1 \/ p2 }> => let p1 := (negation_nf_1 p1) in let p2 := (negation_nf_1 p2) in 
    <{ p1 \/ p2 }>
  | <{ ~p1 }> => f_neg (negation_nf_1 p1)
  | _ => p
  end.

Fixpoint de_morg p :=
  match p with
  | <{(p1 \/ p2) }> => f_and (de_morg p1) (de_morg p2)  
  | <{(p1 /\ p2) }> => f_or (de_morg p1) (de_morg p2) 
  | f_neg p1 => p1
  | _ => f_neg p
  end.


Fixpoint negation_nf_2 p :=
  match p with
  | <{ ~p1 }> => let p1 := negation_nf_2 p1 in de_morg p1
  | <{ p1 /\ p2 }> => let p1 := (negation_nf_2 p1) in let p2 := (negation_nf_2 p2) in 
    <{ p1 /\ p2 }>
  | <{ p1 \/ p2 }> => let p1 := (negation_nf_2 p1) in let p2 := (negation_nf_2 p2) in 
    <{ p1 \/ p2 }>
  | _ => p
  end.
(*
Fixpoint negation_nf_3 p :=
  match p with
  | <{ ~~p1 }> => negation_nf_3 p1
  | <{ p1 /\ p2 }> => let p1 := (negation_nf_3 p1) in let p2 := (negation_nf_3 p2) in 
    <{ p1 /\ p2 }>
  | <{ p1 \/ p2 }> => let p1 := (negation_nf_3 p1) in let p2 := (negation_nf_3 p2) in 
    <{ p1 \/ p2 }>
  | <{ ~p1 }> => f_neg (negation_nf_3 p1)
  | _ => p
  end.
*)
Definition negation_nf p := 
  let p1 := negation_nf_1 p in
  negation_nf_2 p1.

Compute negation_nf twotwotwo.

Fixpoint verify_nnf p :=
  match p with
  | <{ p /\ q }> => (verify_nnf p) && (verify_nnf q)
  | <{ p \/ q }> => (verify_nnf p) && (verify_nnf q)
  | f_false | f_true | f_var _ | f_neg (f_var _)  => true
  | _ => false
  end.

Definition verify_nnf_works p := verify_nnf (negation_nf p) = true.

Fixpoint helper_left p q :=
  match q with
  | <{q1 /\ q2 }> => f_and (helper_left p q1) (helper_left p q2)
  | _ => <{p \/ q}>
  end.

Fixpoint helper_right q p :=
  match q with
  | <{q1 /\ q2 }> => f_and (helper_right q1 p) (helper_right q2 p)
  | _ => helper_left q p
  end.

Definition transf p := 
  match p with
  | <{p \/ q}> => helper_right p q
  | _ => p
  end.


Fixpoint cnf s :=
  match s with
  | <{ p /\ q }> => f_and (cnf p) (cnf q)
  | <{ p \/ q}> => transf (f_or (cnf p) (cnf q))
  | _ => s
  end.

Definition cnf_conv p := 
  let p1 := negation_nf p in
  cnf p1.

Definition x1 := Id 3 .

Fixpoint verify_cnf' s (seenor : bool) :=
  match s with
  | <{ p /\ q }> => if seenor then false else (verify_cnf' p false) && (verify_cnf' q false)
  | <{ p \/ q }> => (verify_cnf' p true) && (verify_cnf' q true)
  | f_false | f_true | f_var _ | f_neg (f_var _)  => true
  | _ => false
  end.

Definition verify_cnf s := verify_cnf' s false.


Definition test11 := <{ x \/ (y /\ z /\ x1 ) }> .
Definition test12 := <{ x \/ (y \/ z /\ x1 ) }> .
Definition test13 := <{ (x /\ ((y \/ x) /\ z)) \/ (y /\ (x \/ ( y /\ z))) }> .


Compute verify_cnf (cnf_conv test13).

Conjecture cnf_works : forall p, verify_cnf (cnf_conv p) = true.


Require Import Lia.

Conjecture cnf_sat : forall p v, interp v p = interp v (cnf_conv p).

From QuickChick Require Import QuickChick.

Derive Arbitrary for id.
Derive Arbitrary for form.
Derive Show for id.
Derive Show for form.


QuickChick cnf_works.