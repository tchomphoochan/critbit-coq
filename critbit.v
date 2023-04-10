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
Notation "#[ x ]" := x (x custom bitstring at level 0, format "#[ x ]").

Section ct_definition.
  Context {V : Type}.
  Context {fmap : map.map K V}.
  Search map.empty.
  Definition map_singleton (k:K) (v:V) :=
    map.put map.empty k v.
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

  Inductive ct : node -> K -> fmap -> Prop :=
  | ct_leaf : forall s v n,
      valid_key s ->
      ct (Leaf s v) (s ++ repeat false n) (map_singleton s v)
  | ct_internal : forall tl tr s xl xr ml mr,
      ct tl (s++[false]++xl) ml ->
      ct tr (s++[true]++xr) mr ->
      ct (Internal (length s) tl tr) s (map.putmany ml mr).
  
  Lemma ct_leaf' :
    forall s s' v n, valid_key s -> s' = s ++ repeat false n -> ct (Leaf s v) s' (map_singleton s v).
  Proof.
    intros. subst. econstructor. eauto.
  Qed.

  Lemma ct_internal' : 
    forall tl tr s xl xr m ml mr n,
      ct tl (s++[false]++xl) ml ->
      ct tr (s++[true]++xr) mr ->
      n = length s ->
      m = map.putmany ml mr ->
      ct (Internal n tl tr) s m.
  Proof.
    intros.
    subst. econstructor; eauto.
  Qed.

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

  Lemma find_best_exists_ok:  forall t s m,
    ct t s m -> forall k v, map.get m s = Some v -> find_best t k = (k, v).
  Proof.
    induction 1; simpl; intros.
  Abort.

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
    ct_top t m -> map.get m k = Some v -> lookup t k = Some v.
  Admitted.

  Theorem lookup_none : forall t m k,
    ct_top t m -> map.get m k = None -> lookup t k = None.
  Admitted.

  Theorem lookup_ok : forall t m k r,
    ct_top t m -> map.get m k = r -> lookup t k = r.
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
  Admitted.
  Definition Build_parameters T := SortedList.parameters.Build_parameters bitstring T bitstring_ltb.
  Local Instance map T : map.map bitstring T := SortedList.map (Build_parameters T) bitstring_strict_order.
  Local Instance ok T : @Interface.map.ok bitstring T (map T).
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
    Node (Leaf [true; false; false] 0).
  Goal lookup ct1 [true; false; false] = Some 0. Proof. reflexivity. Qed.
  Goal lookup ct1 [false] = None. Proof. reflexivity. Qed.
  Goal lookup ct1 [false; false; false] = None. Proof. reflexivity. Qed.

  Definition l0001 := [false; false; false; true].
  Goal valid_key l0001. Proof. reflexivity. Qed.

  Definition l001 := [false; false; true].
  Goal valid_key l001. Proof. reflexivity. Qed.

  Definition l00101 := [false; false; true; false; true].
  Goal valid_key l00101. Proof. reflexivity. Qed.

  Definition l0011 := [false; false; true; true].
  Goal valid_key l0011. Proof. reflexivity. Qed.

  Definition l00111 := [false; false; true; true; true].
  Goal valid_key l00111. Proof. reflexivity. Qed.

  Definition l10001 := [true; false; false; false; true].
  Goal valid_key l10001. Proof. reflexivity. Qed.

  Definition l10101 := [true; false; true; false; true].
  Goal valid_key l10101. Proof. reflexivity. Qed.

  Example ct2 :=
    Node (
      Internal 0
        (Internal 2
          (Leaf l0001 0)
          (Internal 3
            (Internal 4
              (Leaf l001 1)
              (Leaf l00101 2))
            (Internal 4
              (Leaf l0011 3)
              (Leaf l00111 4))))
        (Internal 2
          (Leaf l10001 5)
          (Leaf l10101 6))).
  Goal lookup ct2 l0001 = Some 0. Proof. reflexivity. Qed.
  Goal lookup ct2 l001 = Some 1. Proof. reflexivity. Qed.
  Goal lookup ct2 l00101 = Some 2. Proof. reflexivity. Qed.
  Goal lookup ct2 l0011 = Some 3. Proof. reflexivity. Qed.
  Goal lookup ct2 l00111 = Some 4. Proof. reflexivity. Qed.
  Goal lookup ct2 l10001 = Some 5. Proof. reflexivity. Qed.
  Goal lookup ct2 l10101 = Some 6. Proof. reflexivity. Qed.
  Goal lookup ct2 [true] = None.
  Proof. reflexivity. Qed.
  Goal lookup ct2 [false;true] = None.
  Proof. reflexivity. Qed.
  Goal lookup ct2 [false;true;true] = None.
  Proof. reflexivity. Qed.
  Goal lookup ct2 [false;true;true;false;true] = None.
  Proof. reflexivity. Qed.
  Goal lookup ct2 [true;false;true] = None.
  Proof. reflexivity. Qed.

  Example map3_0 := map_singleton l0001 0.
  Example ct3_0 := insert Empty l0001 0.
  Goal ct3_0 = Node (Leaf l0001 0).
  Proof. reflexivity. Qed.
  Fact ct3_0_ok : ct_top ct3_0 map3_0.
    eapply ct_top_node.
    eapply ct_leaf' with (n := 0); easy.
  Qed.

  Example map3_1 := map.put map3_0 l00101 1.
  Example ct3_1 := insert ct3_0 l00101 1.
  Goal ct3_1 = Node 
    (Internal 2
      (Leaf l0001 0)
      (Leaf l00101 1)).
  Proof. reflexivity. Qed.
  Fact ct3_1_ok : ct_top ct3_1 map3_1.
    unfold ct3_1, map3_1, map3_0; simpl.
    apply ct_top_node with (s := [false; false]).
    eapply ct_internal'.
    - eapply ct_leaf' with (n := 0); easy.
    - eapply ct_leaf' with (n := 0); easy.
    - easy.
    - easy.
  Qed.

  Example map3_2 := map.put map3_1 l001 2.
  Example ct3_2 := insert ct3_1 l001 2.
  Goal ct3_2 = Node
    (Internal 2
      (Leaf l0001 0)
      (Internal 4
        (Leaf l001 2)
        (Leaf l00101 1))).
  Proof. reflexivity. Qed.
  Fact ct3_2_ok : ct_top ct3_2 map3_2.
    apply ct_top_node with (s := [false; false]); simpl.
    eapply ct_internal'.
  Admitted.

  Example map3_3 := map.put map3_2 l10101 3.
  Example ct3_3 := insert ct3_2 l10101 3.
  Goal ct3_3 = Node
    (Internal 0
      (Internal 2
        (Leaf l0001 0)
        (Internal 4
          (Leaf l001 2)
          (Leaf l00101 1)))
      (Leaf l10101 3)).
  Proof. reflexivity. Qed.
  Fact ct3_3_ok : ct_top ct3_3 map3_3.
  Admitted.

  Example map3_4 := map.put map3_3 l00111 4.
  Example ct3_4 := insert ct3_3 l00111 4.
  Goal ct3_4 = Node
    (Internal 0
      (Internal 2
        (Leaf l0001 0)
        (Internal 3
          (Internal 4
            (Leaf l001 2)
            (Leaf l00101 1))
          (Leaf l00111 4)))
      (Leaf l10101 3)).
  Proof. reflexivity. Qed.
  Fact ct3_4_ok : ct_top ct3_4 map3_4.
  Admitted.

  Example map3_5 := map.put map3_4 l10001 5.
  Example ct3_5 := insert ct3_4 l10001 5.
  Goal ct3_5 = Node
    (Internal 0
      (Internal 2
        (Leaf l0001 0)
        (Internal 3
          (Internal 4
            (Leaf l001 2)
            (Leaf l00101 1))
          (Leaf l00111 4)))
      (Internal 2
        (Leaf l10001 5)
        (Leaf l10101 3))).
  Proof. reflexivity. Qed.
  Fact ct3_5_ok : ct_top ct3_5 map3_5.
  Admitted.

  Example map3_6 := map.put map3_5 l0011 6.
  Example ct3_6 := insert ct3_5 l0011 6.
  Goal ct3_6 = Node
    (Internal 0
      (Internal 2
        (Leaf l0001 0)
        (Internal 3
          (Internal 4
            (Leaf l001 2)
            (Leaf l00101 1))
          (Internal 4
            (Leaf l0011 6)
            (Leaf l00111 4))))
      (Internal 2
        (Leaf l10001 5)
        (Leaf l10101 3))).
  Proof. reflexivity. Qed.
  Fact ct3_6_ok : ct_top ct3_6 map3_6.
  Admitted.

End Examples.