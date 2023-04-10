Require Import Arith Bool List Lia.
Import ListNotations.
Parameter TODO : forall {t:Type}, t.

Definition partial_map (K V : Type) := K -> (option V).
Parameter map_singleton : forall {K V : Type} (k : K) (v : V), partial_map K V.
Parameter map_empty : forall {K V : Type}, partial_map K V.
Parameter map_union : forall {K V : Type}, partial_map K V -> partial_map K V -> partial_map K V.

Infix "<=?" := le_lt_dec.

Module CritbitTree.
  Definition bitstring := list bool.
  Definition K := bitstring.
  Definition V := nat.

  Definition ith (s: bitstring) (n: nat): bool :=
    nth_default false s n.
  Definition keq := @list_eq_dec bool bool_dec.
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

  Inductive ct : node -> K -> partial_map K V -> Prop :=
  | ct_leaf : forall s v, ct (Leaf s v) s (map_singleton s v)
  | ct_internal : forall tl tr s xl xr ml mr,
      ct tl (s++[false]++xl) ml ->
      ct tr (s++[true]++xr) mr ->
      ct (Internal (length s) tl tr) s (map_union ml mr).

  Inductive ct_top : tree -> partial_map K V -> Prop :=
  | ct_top_empty : ct_top Empty map_empty
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

  Theorem update_eq :
    forall t ik iv, lookup (insert t ik iv) ik = Some iv.
  Proof.
    induction t; intros; simpl.
    - destruct keq; easy.
    - admit.
  Admitted.

  Theorem update_neq :
    forall t ik iv k, ik <> k -> lookup (insert t ik iv) k = lookup t k.
  Proof.
    induction t; intros; simpl.
    - destruct keq; easy.
    - admit.
  Admitted.

End CritbitTree.

Module Examples.
  Module CT := CritbitTree.
  Import CT.

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
  
  Example ct0 := Empty.
  Goal lookup ct0 nil = None. Proof. reflexivity. Qed.

  Example ct1 :=
    Node (Leaf [true; false; false] 0).
  Goal lookup ct1 [true; false; false] = Some 0. Proof. reflexivity. Qed.
  Goal lookup ct1 [false] = None. Proof. reflexivity. Qed.
  Goal lookup ct1 [false; false; false] = None. Proof. reflexivity. Qed.

  Definition l00010 := [false; false; false; true; false].
  Definition l00100 := [false; false; true; false; false].
  Definition l00101 := [false; false; true; false; true].
  Definition l00110 := [false; false; true; true; false].
  Definition l00111 := [false; false; true; true; true].
  Definition l10001 := [true; false; false; false; true].
  Definition l10101 := [true; false; true; false; true].

  Example ct2 :=
    Node (
      Internal 0
        (Internal 2
          (Leaf l00010 0)
          (Internal 3
            (Internal 4
              (Leaf l00100 1)
              (Leaf l00101 2))
            (Internal 4
              (Leaf l00110 3)
              (Leaf l00111 4))))
        (Internal 2
          (Leaf l10001 5)
          (Leaf l10101 6))).
  Goal lookup ct2 l00010 = Some 0. Proof. reflexivity. Qed.
  Goal lookup ct2 l00100 = Some 1. Proof. reflexivity. Qed.
  Goal lookup ct2 l00101 = Some 2. Proof. reflexivity. Qed.
  Goal lookup ct2 l00110 = Some 3. Proof. reflexivity. Qed.
  Goal lookup ct2 l00111 = Some 4. Proof. reflexivity. Qed.
  Goal lookup ct2 l10001 = Some 5. Proof. reflexivity. Qed.
  Goal lookup ct2 l10101 = Some 6. Proof. reflexivity. Qed.
  Goal lookup ct2 [false;false;false;false;false] = None.
  Proof. reflexivity. Qed.
  Goal lookup ct2 [false;true;false;false;false] = None.
  Proof. reflexivity. Qed.
  Goal lookup ct2 [false;true;true;false;false] = None.
  Proof. reflexivity. Qed.
  Goal lookup ct2 [false;true;true;false;true] = None.
  Proof. reflexivity. Qed.
  Goal lookup ct2 [true;false;true;false;false] = None.
  Proof. reflexivity. Qed.

  Example ct3_0 := insert Empty l00010 0.
  Goal ct3_0 = Node (Leaf l00010 0).
  Proof. reflexivity. Qed.

  Example ct3_1 := insert ct3_0 l00101 1.
  Goal ct3_1 = Node 
    (Internal 2
      (Leaf l00010 0)
      (Leaf l00101 1)).
  Proof. reflexivity. Qed.

  Example ct3_2 := insert ct3_1 l00100 2.
  Goal ct3_2 = Node
    (Internal 2
      (Leaf l00010 0)
      (Internal 4
        (Leaf l00100 2)
        (Leaf l00101 1))).
  Proof.
    unfold ct3_2, insert.
    remember insert' as G.
    step find_best.
    step find_best.
    step find_best.
    subst G.
    step insert'.
    step insert'.
    reflexivity.
  Qed.

  Example ct3_3 := insert ct3_2 l10101 3.
  Goal ct3_3 = Node
    (Internal 0
      (Internal 2
        (Leaf l00010 0)
        (Internal 4
          (Leaf l00100 2)
          (Leaf l00101 1)))
      (Leaf l10101 3)).
  Proof. reflexivity. Qed.

  Example ct3_4 := insert ct3_3 l00111 4.
  Goal ct3_4 = Node
    (Internal 0
      (Internal 2
        (Leaf l00010 0)
        (Internal 3
          (Internal 4
            (Leaf l00100 2)
            (Leaf l00101 1))
          (Leaf l00111 4)))
      (Leaf l10101 3)).
  Proof. reflexivity. Qed.

  Example ct3_5 := insert ct3_4 l10001 5.
  Goal ct3_5 = Node
    (Internal 0
      (Internal 2
        (Leaf l00010 0)
        (Internal 3
          (Internal 4
            (Leaf l00100 2)
            (Leaf l00101 1))
          (Leaf l00111 4)))
      (Internal 2
        (Leaf l10001 5)
        (Leaf l10101 3))).
  Proof.
    unfold ct3_5, insert.
    start.
    step insert'.
    step insert'.
    reflexivity.
  Qed.

  Example ct3_6 := insert ct3_5 l00110 6.
  Goal ct3_6 = Node
    (Internal 0
      (Internal 2
        (Leaf l00010 0)
        (Internal 3
          (Internal 4
            (Leaf l00100 2)
            (Leaf l00101 1))
          (Internal 4
            (Leaf l00110 6)
            (Leaf l00111 4))))
      (Internal 2
        (Leaf l10001 5)
        (Leaf l10101 3))).
  Proof.
    unfold ct3_6, insert.
    start.
    step insert'.
    step insert'.
    step insert'.
    step insert'.
    reflexivity.
  Qed.

End Examples.