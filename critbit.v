Require Import Arith Bool Coq.Lists.List Coq.micromega.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.

Import ListNotations.
Parameter TODO : forall {t:Type}, t.

(* Bitstring definition *)
Definition bitstring := list bool.
Definition K := bitstring.
Definition valid_key (s: bitstring) : Prop :=
  last s false = true.
Definition ith (s: bitstring) (n: nat): bool :=
  nth_default false s n.
Definition keq := @list_eq_dec bool bool_dec.
Infix "<=?" := le_lt_dec.
Definition bool_ltb (a b : bool) :=
  match a, b with
  | false, true => true
  | _, _ => false
  end.
Fixpoint bitstring_ltb (a b : bitstring) : bool :=
  match a, b with
  | nil, cons _ _ => true
  | cons x a', cons y b' =>
      if Bool.eqb x y then bitstring_ltb a' b' else bool_ltb x y
  | _, _ => false
  end.

(* Notation stuff *)
Declare Custom Entry bit.
Notation "0" := false (in custom bit at level 0).
Notation "1" := true (in custom bit at level 0).
Declare Custom Entry bitstring.
Notation "x" := (@cons bool x nil)
  (in custom bitstring at level 0, x custom bit at level 0).
Notation "h t" := (@cons bool h t)
  (in custom bitstring at level 0,
   h custom bit at level 0, t custom bitstring at level 0).
Notation "#[]" := nil (format "#[]").
Notation "#[ x ]" := x (x custom bitstring at level 0, format "#[ x ]").

Fixpoint get_leading_falses (a : bitstring) : list bool :=
  match a with
  | false::a' => false :: get_leading_falses a'
  | _ => nil
  end.
Fixpoint bitstring_max_prefix (a b : bitstring) : list bool :=
  match a, b with
  | x::a', y::b' => if (eqb x y) then x::(bitstring_max_prefix a' b') else nil
  | false::a', nil => get_leading_falses a
  | nil, false::b' => get_leading_falses b
  | _, _ => nil
  end.
Goal bitstring_max_prefix #[0 0 1] #[0 0 1 0 1 1] = #[0 0 1 0].
Proof. reflexivity. Qed.
Ltac bitstring_max_prefix a b := constr:(bitstring_max_prefix a b).

Section ct_definition.
  Context {V : Type}.
  Context {fmap : map.map K V}.
  Axiom veq_exm: forall (v1 v2 : V),
    v1 = v2 \/ v1 <> v2.
  Definition map_singleton (k:K) (v:V) :=
    map.put map.empty k v.
  Context {map_ok : map.ok fmap}.
  Lemma map_get_singleton : forall k v sk rv,
    map.get (map_singleton k v) sk = Some rv ->
    k = sk /\ v = rv.
  Proof.
    unfold map_singleton.
    intros.
    destruct (keq sk k).
    - destruct (veq_exm v rv); subst.
      + split; reflexivity.
      + split; try reflexivity.
        rewrite map.get_put_same in H.
        inversion H. contradiction.
    - rewrite map.get_put_diff in H.
      + rewrite map.get_empty in H. discriminate.
      + assumption.
  Qed.
  Lemma map_get_singleton_none : forall k v sk,
    map.get (map_singleton k v) sk = None -> k <> sk.
  Proof.
    unfold map_singleton.
    intros.
    destruct (keq sk k); subst; eauto.
    rewrite map.get_put_same in H.
    discriminate.
  Qed.

  (* TODO: we should not need this function anymore *)
  Fixpoint diff (s1 : bitstring) :=
    match s1 with
    | c1::s1 => fun s2 => match s2 with
      | c2::s2 => 
          if (eqb c1 c2)
          then option_map S (diff s1 s2)
          else Some 0
      | nil =>
          if (eqb c1 false)
          then option_map S (diff s1 nil)
          else Some 0
      end
    | nil => fix fs2 s2 := match s2 with
      | c2::s2 => 
          if (eqb false c2)
          then option_map S (fs2 s2)
          else Some 0
      | nil => None
      end
    end.
  (* TODO: eliminate invalid keys *)
  Goal diff [] [false;true;false] = Some 1. Proof. reflexivity. Qed.
  Goal diff [] [false] = None. Proof. reflexivity. Qed.
  Goal diff [true;true] [true;true;true] = Some 2. Proof. reflexivity. Qed.
  Goal diff [true;false;true] [true;true;true] = Some 1. Proof. reflexivity. Qed.
  Goal diff [true] [true;false] = None. Proof. reflexivity. Qed.

  Inductive node : Type :=
  | Leaf (k: K) (v: V)
  | Internal (idx: nat) (l: node) (r: node).

  Inductive tree : Type :=
  | Empty
  | Node (n: node).

  Fixpoint max_prefix' (t : node) : bitstring :=
    match t with
    | Leaf k _ => k
    | Internal _ l r => bitstring_max_prefix (max_prefix' l) (max_prefix' r)
    end.
  Definition max_prefix (t : tree) : bitstring :=
    match t with
    | Empty => #[]
    | Node n => max_prefix' n
    end.

  Inductive ct : node -> K -> fmap -> Prop :=
  | ct_leaf :
      forall s s' v n,
        valid_key s ->
        s' = s ++ repeat false n ->
        ct (Leaf s v) s' (map_singleton s v)
  | ct_internal :
      forall tl tr s xl xr m ml mr n,
        ct tl (s++[false]++xl) ml ->
        ct tr (s++[true]++xr) mr ->
        n = length s ->
        m = map.putmany ml mr ->
        ct (Internal n tl tr) s m.

  Inductive ct_top : tree -> fmap -> Prop :=
  | ct_top_empty : ct_top Empty map.empty
  | ct_top_node : forall t m s, ct t s m -> ct_top (Node t) m.

  (* indices are always increasing as you go down the tree *)

  (* sk stands for search key *)
  Fixpoint find_best (n: node) (sk: K) : K*V :=
    match n with
    | Internal i l r =>
        find_best (if (ith sk i) then r else l) sk
    | Leaf k v =>
        (k,v)
    end.

  Lemma find_best_ok:  forall t m s,
    ct t s m -> 
    (forall k, valid_key k ->
      (forall v, map.get m k = Some v -> find_best t k = (k, v)) /\
      (map.get m k = None -> forall k', fst (find_best t k') <> k)).
  Proof.
    induction 1; subst; simpl; split; intros.
    (* base case *)
    - apply map_get_singleton in H1. destruct H1. subst. reflexivity.
    - apply map_get_singleton_none in H1. assumption.
    (* inductive case *)
    - destruct (ith k (length s)) eqn:E.
      + apply IHct2; auto. 
        cut (map.get ml k = None).
        * admit. (* should be a map lemma *)
        * admit. (* need to relate to H somehow *)
      + apply IHct1; auto.
        cut (map.get mr k = None).
        * admit.
        * admit.
    - eapply map.invert_get_putmany_None with
        (m1 := ml) (m2 := mr) in H2.
      destruct H2.
      destruct (ith k' (length s)) eqn:E.
      + apply IHct2; auto.
      + apply IHct1; auto.
      Unshelve. all: admit.
  Admitted.

  Definition lookup (t: tree) (sk: K) : option V :=
    match t with
    | Empty => None
    | Node n => 
      let (k,v) := find_best n sk in
      if (keq k sk) then Some v else None
    end.
  
  Definition empty : tree := Empty.
  Definition singleton (ik: K) (iv: V) : tree := Node (Leaf ik iv).

  (* d stands for diff index *)
  Fixpoint insert' (n: node) (ik: K) (iv: V) (d: nat) : node :=
    match n with
    | Leaf k v =>
        if ith ik d
        then Internal d (Leaf k v) (Leaf ik iv)
        else Internal d (Leaf ik iv) (Leaf k v)
    | Internal idx l r =>
        if d <=? idx
        then (
          if ith ik d
          then Internal d (Internal idx l r) (Leaf ik iv)
          else Internal d (Leaf ik iv) (Internal idx l r)
        )
        else (
          if ith ik idx
          then Internal idx l (insert' r ik iv d)
          else Internal idx (insert' l ik iv d) r
        )
    end.

  (* ik stands for insert key *)
  Definition insert (t: tree) (ik: K) (iv: V) : tree :=
    match t with
    | Empty => singleton ik iv
    | Node n =>
        let (k,v) := find_best n ik in
        match (diff k ik) with
        | None => Node (Leaf ik iv)
        | Some d => Node (insert' n ik iv d)
        end
    end.
  
  Theorem apply_empty :
    forall sk, lookup Empty sk = None.
  Proof.
    reflexivity.
  Qed.

  Theorem lookup_exists : forall t m k v,
    ct_top t m -> valid_key k -> map.get m k = Some v -> lookup t k = Some v.
  Proof.
    induction 1; intros; simpl.
    - rewrite map.get_empty in H0. discriminate.
    - destruct (find_best t k) eqn:E.
      pose proof find_best_ok t m s H k H0.
      destruct H2.
      apply H2 in H1.
      destruct (keq k0 k); congruence.
  Qed.

  Theorem lookup_none : forall t m k,
    ct_top t m -> valid_key k -> map.get m k = None -> lookup t k = None.
    induction 1; intros; simpl.
    - reflexivity.
    - destruct (find_best t k) eqn:E.
      pose proof find_best_ok t m s H k H0.
      destruct H2.
      destruct (keq k0 k); subst; try reflexivity.
      apply H3 with (k' := k) in H1.
      destruct (find_best t k). simpl in H1.
      congruence.
  Qed.

  Theorem lookup_ok : forall t m k r,
    ct_top t m -> valid_key k -> map.get m k = r -> lookup t k = r.
  Proof.
    intros.
    destruct r.
    - eauto using lookup_exists.
    - eauto using lookup_none.
  Qed.

  Theorem insert_ok : forall t m t' k v,
    ct_top t m -> ct_top t' (map.put m k v).
  Admitted.
End ct_definition.

Section Examples.

  Require Import FunctionalExtensionality. 
  Require Import coqutil.Tactics.Tactics.
  Require coqutil.Map.SortedList.
  Local Instance bitstring_strict_order: @SortedList.parameters.strict_order _ bitstring_ltb.
  Proof.
  Admitted.
  Definition Build_parameters T := SortedList.parameters.Build_parameters bitstring T bitstring_ltb.
  Local Instance map T : map.map bitstring T := SortedList.map (Build_parameters T) bitstring_strict_order.
  Local Instance ok T : @Interface.map.ok bitstring T (map T).
  Proof.
    pose proof @SortedList.map_ok (Build_parameters T) as H; eapply H.
  Qed.

  Ltac start :=
    repeat (let E := fresh "E" in
      (match goal with
      | [ |- context[match ?X with _ => _ end]] => destruct X eqn:?E
      end; inversion E; subst; clear E)).
  
  Ltac simp_if :=
    let E := fresh "E" in
      (match goal with
      | [ |- context[if ?X then _ else _]] => destruct X eqn:?E
      end; try discriminate; clear E).

  Ltac replace_with_simpl term :=
    let P := fresh in
    let H := fresh in
    (eset (term = _) as P;
    assert P as ?H;
    [(unfold P, term;
    simpl; reflexivity)
    | rewrite H; clear P H]).

  Ltac step f :=
    progress let F := fresh in
      (cbv delta [f] fix;
      fold f;
      remember f as F;
      simpl;
      subst F).
  
  Example ct0 := @Empty nat.
  Goal lookup ct0 nil = None. Proof. reflexivity. Qed.

  Example ct1 :=
    Node (Leaf #[1 0 0] 0).
  Goal lookup ct1 #[1 0 0] = Some 0. Proof. reflexivity. Qed.
  Goal lookup ct1 #[] = None. Proof. reflexivity. Qed.
  Goal lookup ct1 #[1 0 1] = None. Proof. reflexivity. Qed.

  Example ct2 :=
    Node (
      Internal 0
        (Internal 2
          (Leaf #[0 0 0 1] 0)
          (Internal 3
            (Internal 4
              (Leaf #[0 0 1] 1)
              (Leaf #[0 0 1 0 1] 2))
            (Internal 4
              (Leaf #[0 0 1 1] 3)
              (Leaf #[0 0 1 1 1] 4))))
        (Internal 2
          (Leaf #[1 0 0 0 1] 5)
          (Leaf #[1 0 1 0 1] 6))).
  Goal lookup ct2 #[0 0 0 1] = Some 0. Proof. reflexivity. Qed.
  Goal lookup ct2 #[0 0 1] = Some 1. Proof. reflexivity. Qed.
  Goal lookup ct2 #[0 0 1 0 1] = Some 2. Proof. reflexivity. Qed.
  Goal lookup ct2 #[0 0 1 1] = Some 3. Proof. reflexivity. Qed.
  Goal lookup ct2 #[0 0 1 1 1] = Some 4. Proof. reflexivity. Qed.
  Goal lookup ct2 #[1 0 0 0 1] = Some 5. Proof. reflexivity. Qed.
  Goal lookup ct2 #[1 0 1 0 1] = Some 6. Proof. reflexivity. Qed.
  Goal lookup ct2 #[1] = None.
  Proof. reflexivity. Qed.
  Goal lookup ct2 #[0 1] = None.
  Proof. reflexivity. Qed.
  Goal lookup ct2 #[0 1 1] = None.
  Proof. reflexivity. Qed.
  Goal lookup ct2 #[0 1 1 0 1] = None.
  Proof. reflexivity. Qed.
  Goal lookup ct2 #[1 0 1] = None.
  Proof. reflexivity. Qed.

  Example map3_0 := map_singleton #[0 0 0 1] 0.
  Example ct3_0 := insert Empty #[0 0 0 1] 0.
  Goal ct3_0 = Node (Leaf #[0 0 0 1] 0).
  Proof. reflexivity. Qed.
  Fact ct3_0_ok : ct_top ct3_0 map3_0.
    eapply ct_top_node.
    eapply ct_leaf with (n := 0); reflexivity.
  Qed.
  Ltac max_prefix' t := constr:(@max_prefix' nat t).
  Ltac max_prefix t := constr:(@max_prefix nat t).

  Ltac internal :=
    cbv; match goal with
    | [|- ct (Internal ?i ?l ?r) ?t ?m] =>
        let p := max_prefix' (Internal i l r) in
        eapply ct_internal with (s := p)
    end; try reflexivity.
  Ltac leaf' i :=
    cbv; match goal with
    | [|- ct (Leaf ?l ?i) ?t ?m] =>
      solve [ apply ct_leaf with (n := i); simpl; reflexivity | leaf' (i+1) ]
    end.
  Ltac leaf := leaf' 0.
  Ltac ct' := progress repeat (reflexivity || internal || leaf).
  Ltac ct := eapply ct_top_node; simpl; ct'.

  Example map3_1 := map.put map3_0 #[0 0 1 0 1] 1.
  Example ct3_1 := insert ct3_0 #[0 0 1 0 1] 1.
  Goal ct3_1 = Node 
    (Internal 2
      (Leaf #[0 0 0 1] 0)
      (Leaf #[0 0 1 0 1] 1)).
  Proof. reflexivity. Qed.
  Goal ct_top ct3_1 map3_1. Proof. ct. Qed.

  Example map3_2 := map.put map3_1 #[0 0 1] 2.
  Example ct3_2 := insert ct3_1 #[0 0 1] 2.
  Goal ct3_2 = Node
    (Internal 2
      (Leaf #[0 0 0 1] 0)
      (Internal 4
        (Leaf #[0 0 1] 2)
        (Leaf #[0 0 1 0 1] 1))).
  Proof. reflexivity. Qed.
  Goal ct_top ct3_2 map3_2. Proof. ct. Qed.

  Example map3_3 := map.put map3_2 #[1 0 1 0 1] 3.
  Example ct3_3 := insert ct3_2 #[1 0 1 0 1] 3.
  Goal ct3_3 = Node
    (Internal 0
      (Internal 2
        (Leaf #[0 0 0 1] 0)
        (Internal 4
          (Leaf #[0 0 1] 2)
          (Leaf #[0 0 1 0 1] 1)))
      (Leaf #[1 0 1 0 1] 3)).
  Proof. reflexivity. Qed.
  Goal ct_top ct3_3 map3_3. Proof. ct. Qed.

  Example map3_4 := map.put map3_3 #[0 0 1 1 1] 4.
  Example ct3_4 := insert ct3_3 #[0 0 1 1 1] 4.
  Goal ct3_4 = Node
    (Internal 0
      (Internal 2
        (Leaf #[0 0 0 1] 0)
        (Internal 3
          (Internal 4
            (Leaf #[0 0 1] 2)
            (Leaf #[0 0 1 0 1] 1))
          (Leaf #[0 0 1 1 1] 4)))
      (Leaf #[1 0 1 0 1] 3)).
  Proof. reflexivity. Qed.
  Goal ct_top ct3_4 map3_4. Proof. ct. Qed.

  Example map3_5 := map.put map3_4 #[1 0 0 0 1] 5.
  Example ct3_5 := insert ct3_4 #[1 0 0 0 1] 5.
  Goal ct3_5 = Node
    (Internal 0
      (Internal 2
        (Leaf #[0 0 0 1] 0)
        (Internal 3
          (Internal 4
            (Leaf #[0 0 1] 2)
            (Leaf #[0 0 1 0 1] 1))
          (Leaf #[0 0 1 1 1] 4)))
      (Internal 2
        (Leaf #[1 0 0 0 1] 5)
        (Leaf #[1 0 1 0 1] 3))).
  Proof. reflexivity. Qed.
  Goal ct_top ct3_5 map3_5. Proof. ct. Qed.

  Example map3_6 := map.put map3_5 #[0 0 1 1] 6.
  Example ct3_6 := insert ct3_5 #[0 0 1 1] 6.
  Goal ct3_6 = Node
    (Internal 0
      (Internal 2
        (Leaf #[0 0 0 1] 0)
        (Internal 3
          (Internal 4
            (Leaf #[0 0 1] 2)
            (Leaf #[0 0 1 0 1] 1))
          (Internal 4
            (Leaf #[0 0 1 1] 6)
            (Leaf #[0 0 1 1 1] 4))))
      (Internal 2
        (Leaf #[1 0 0 0 1] 5)
        (Leaf #[1 0 1 0 1] 3))).
  Proof. reflexivity. Qed.
  Goal ct_top ct3_6 map3_6. Proof. ct. Qed.

End Examples.