(******************************************************************************)
(* (c) 2017-2018 Mines ParisTech, LIRIS                                       *)
(*                                                                            *)
(* Some parts based on the math-comp library.                                 *)
(* Distributed under the terms of CeCILL-B.                                   *)
(*                                                                            *)
(******************************************************************************)
From mathcomp Require Import all_ssreflect.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(*******************************************************************************)
(* A module so notations are exported *)
Module ExtExists.
(*******************************************************************************)

Inductive ex3 (A:Type) (P Q R:A -> Prop) : Prop :=
  ex_intro3 : forall x:A, P x -> Q x -> R x -> ex3 (A:=A) P Q R.

Notation "'exists3' x , p & q & r" := (ex3 (fun x => p) (fun x => q) (fun x => r))
  (at level 200, x ident, p at level 200, right associativity) : type_scope.
Notation "'exists3' x : A , p & q & r" := (ex3 (A:=A) (fun x => p) (fun x => q) (fun x => r))
  (at level 200, x ident, A at level 200, p at level 200, right associativity,
    format "'[' 'exists3'  '/  ' x  :  A ,  '/  ' '[' p  &  '/' q  &  '/' r ']' ']'")
  : type_scope.

End ExtExists.
Export ExtExists.

(*******************************************************************************)
Section AuxList.
(*******************************************************************************)
Lemma has_cons X P (x : X) l : has P [:: x & l] = P x || has P l.
Proof. by []. Qed.

End AuxList.

(*******************************************************************************)
Section AuxSet.
(*******************************************************************************)

Variable (T : finType).

Lemma setlist0 : [set x : T in [::]] = set0.
Proof. by apply/setP => x; rewrite inE. Qed.

Lemma disjoint_meml (A B : pred T) (x : T) :
  [disjoint A & B] -> x \in A -> x \notin B.
Proof. by rewrite disjoint_subset => /subsetP/(_ x). Qed.

Lemma disjoint_setU (A B C : {set T}):
  [disjoint A :|: B & C] =
  [disjoint A & C] && [disjoint B & C].
Proof. by rewrite -disjointU; apply: eq_disjoint => x; rewrite inE. Qed.

Lemma disjoint_set1 x (A : {set T}):
  [disjoint [set x] & A] = (x \notin A).
Proof. by rewrite -disjoint1; apply: eq_disjoint => y; rewrite inE. Qed.

End AuxSet.

(*******************************************************************************)
Section AuxGraph.
(*******************************************************************************)

Variable V : finType.

(* Interpretation for l+(x,y) = l(x,z) ∧ l*(z,y) *)
Definition connect_plus (e : rel V) x y :=
  [exists z, e x z && connect e z y].

(* Characterization lemma for non-empty connect *)
Lemma connect_plusP (e : rel V) (x y : V) :
  reflect (exists p, exists3 z, z \in p & path e x p & y = last z p)
          (connect_plus e x y).
Proof.
apply/(iffP existsP).
  case=> z /andP[e_z] /connectP [p h_p h_y].
  by exists [:: z & p], z; rewrite /= ?inE ?eqxx ?e_z.
case=> [[|z p]] [w h_z //= /andP [h_e h_p] h_l].
by exists z; rewrite h_e; apply/connectP; exists p.
Qed.

Lemma eq_connect_plus (e e' : rel V) :
    e =2 e' -> connect_plus e =2 connect_plus e'.
Proof.
move=> eq_e x y; apply/connect_plusP/connect_plusP=>[] [p] [z z_in e_p ->];
  by exists p, z; rewrite // (eq_path eq_e) in e_p *.
Qed.

Lemma connect_plusP_v2 (e : rel V) (x y : V) :
  reflect (exists3 p, 0 < size p & path e x p & y = last x p)
          (connect_plus e x y).
Proof.
apply/(iffP existsP)=> [[z /andP[ez]]|[[|z p] h_s //]].
  by case/connectP=> [p hp hy]; exists [:: z & p]; rewrite //= ?ez.
by case/andP=> [he hp] hy; exists z; rewrite he; apply/connectP; exists p.
Qed.

End AuxGraph.

(*******************************************************************************)
Section BigCupSeq.
(*******************************************************************************)

Variables (T : finType) (I : eqType).
Implicit Types (P : pred I) (F :  I -> {set T}).

Lemma bigcup_seqP x P F l :
  reflect (exists2 i : I, i \in l & (x \in F i) && P i) (x \in \bigcup_(t <- l | P t) F t).
Proof.
rewrite big_tnth; apply/(iffP idP).
  by case/bigcupP=> i Hp Hin; exists (tnth (in_tuple l) i); rewrite ?mem_tnth ?Hin.
by case=> i /seq_tnthP[t ht] /andP[xf xp]; apply/bigcupP; exists t; rewrite -?ht.
Qed.

Lemma bigcups_seqP (U : pred T) (P : pred I) (F : I -> {set T}) (r : seq I) :
  reflect (forall i : I, i \in r -> P i -> F i \subset U)
          (\bigcup_(i <- r | P i) F i \subset U).
Proof.
apply/(iffP idP).
  by rewrite big_tnth; move/bigcupsP=> H i /seq_tnthP[idx -> hp]; exact: H.
by move=> H; rewrite big_tnth; apply/bigcupsP=> i ?; apply: H; rewrite ?mem_tnth.
Qed.

Lemma bigcup_sup_seq (j : I) (F : I -> {set T}) (l : seq I) :
    j \in l -> F j \subset \bigcup_(i <- l) F i.
Proof.
rewrite -mem_undup -(big_undup _ _ _ (@setUid _)) => hj.
by rewrite (bigD1_seq j) /= ?subsetUl ?undup_uniq.
Qed.

End BigCupSeq.

Arguments bigcups_seqP [T I U P F r].

(*******************************************************************************)
Section ForAllbAux.
(*******************************************************************************)

Variables (T : finType).
Implicit Types (P D : pred T).

Lemma sub_forall_inP D1 D2 P :
  D1 \subset D2 -> [forall x in D2, P x] -> [forall x in D1, P x].
Proof.
by move/subsetP=> hs /forall_inP ha; apply/forall_inP=> ? /hs ?; apply: ha.
Qed.

Lemma forall_implP P1 P2 :
  reflect (forall x : T, P1 x -> P2 x) [forall x, P1 x ==> P2 x].
Proof.
have PP x : reflect (P1 x -> P2 x) (P1 x ==> P2 x) by apply/implyP.
exact/(forallPP PP).
Qed.

Lemma eq_forall_inb P1 P2 (D : pred T)
  : {in D, P1 =1 P2} -> [forall x in D, P1 x] = [forall x in D, P2 x].
Proof.
by move=> hin; apply/eq_forallb=> x; case: (_ \in D) / boolP => //; exact/hin.
Qed.

Lemma eq_forall_mem D1 D2 P (hp : D1 =i D2) :
  [forall x in D1, P x] = [forall x in D2, P x].
Proof.
by apply/forall_inP/forall_inP=> h x hin; apply: h; rewrite ?hp // -hp.
Qed.

Lemma eq_forall_set1 P y : [forall x in [set y], P x] = P y.
Proof.
apply/forall_inP/idP=> [h|h m]; first by apply/h; rewrite inE.
by rewrite inE; move/eqP->.
Qed.

Lemma eq_forallU P D1 D2 :
  [forall x in predU D1 D2, P x] =
  [forall x in D1, P x] && [forall x in D2, P x].
Proof.
apply/forall_inP/andP=> [h|[/forall_inP h1 /forall_inP h2] x /orP].
  by split; apply/forall_inP=> x hin; apply/h/orP; [left| right].
by case; auto.
Qed.

Lemma eq_forall_setU P A1 A2 :
  [forall x in A1 :|: A2, P x] =
  [forall x in A1, P x] && [forall x in A2, P x].
Proof.
have eqU: A1 :|: A2 =i (predU (mem A1) (mem A2)).
  by move=> x; rewrite inE.
by rewrite (eq_forall_mem _ eqU) eq_forallU.
Qed.

Lemma forallb_subpred D P1 P2 (hs : subpred P1 P2) :
  [forall x in D, P1 x] -> [forall x in D, P2 x].
Proof. by move/forall_inP=> hP1; apply/forall_inP=> x /hP1; apply: hs. Qed.

End ForAllbAux.

(*******************************************************************************)
Section SetFold.

(** join for the set monad *)
Definition bindS {A B : finType} (i : {set A}) (f : A -> {set B}) : {set B} :=
  cover [set f x | x in i].

(** reflection lemma for binding *)
Lemma bindP (A B : finType) (i : {set A}) (f : A -> {set B}) (r : B) :
  reflect (exists2 s, s \in i & r \in f s) (r \in bindS i f).
Proof.
by rewrite /bindS cover_imset; exact: (iffP bigcupP); case=> s xin rin; exists s.
Qed.

(** monadic fold for the set monad: iteratively composing the result of applying a function [f],
seeded with an initial value [s0], to all elements of a list [l] *)
Fixpoint foldS {A : Type} {B : finType}
         (f : A -> B -> {set B}) (s0 : {set B}) (l : seq A) :=
  if l is [:: x & l] then bindS s0 (fun y => foldS f (f x y) l)
  else s0.

(** If functions [f] and [g] are extensionally equal, then we get the same output when binding
a set [s] with them. *)
Lemma eq_bindS (A B : finType) (f g : A -> {set B}) (s : {set A}) :
  f =1 g -> bindS s f = bindS s g.
Proof.
move=> h_f; apply/setP=> x; rewrite /bindS !cover_imset.
by apply/bigcupP/bigcupP; case=> y y_in x_in; exists y; rewrite // ?h_f // -h_f.
Qed.

(** The result of binding the union of two sets [s1] and [s2] with a function [f]
equals the result of taking the union between the binding of [s1] with [f] and
the binding of [s2] with [f] *)
Lemma bindSU (A B : finType) (f : A -> {set B}) (s1 s2 : {set A})  :
  bindS (s1 :|: s2) f = bindS s1 f :|: bindS s2 f.
Proof. by rewrite /bindS !cover_imset bigcup_setU. Qed.

(** Let [s] be a set and [f], [g] two functions. The result of taking the union
between the binding of [s] with [f] and the binding of [s] with [g] equals the
binding of [s] with the function that returns the point-wise union of [f] and [g] application *)
Lemma bindUS (A B : finType) (f g : A -> {set B}) (s : {set A})  :
  bindS s f :|: bindS s g = bindS s (fun x => f x :|: g x ).
Proof.
rewrite /bindS !cover_imset; apply/setP=> x; rewrite !inE; apply/orP/bigcupP.
  by case=> /bigcupP[y hy hfy]; exists y; rewrite // inE hfy ?orbT.
by case=> [y hy]; rewrite inE; case/orP=> hf; [left | right]; apply/bigcupP; exists y.
Qed.

(** If [f] and [g] are extensionally equal, then the results of taking their fold over a list [l],
seeded with an initial set [s], are equal *)
Lemma eq_foldS (A : eqType) (T : finType) f g (s : {set T}) (l : seq A) :
  {in l, f =2 g} -> foldS f s l = foldS g s l.
Proof.
move=> h_f; elim: l s h_f => //= x l ihl s h_f.
suff/eq_bindS->: (fun y : T => foldS f (f x y) l) =1
                 (fun y : T => foldS g (g x y) l) by [].
by move=> y; rewrite h_f ?ihl ?mem_head // => u hu k; rewrite h_f ?inE ?hu ?orbT.
Qed.

(** The result of folding a function [f] over a list [l], starting from the union
of sets [s1] and [s2] equals the union of folding [f] over [l] starting from [s1]
and of folding [f] over [l] starting from [s2] *)
Lemma foldSU A (T : finType) f (s1 s2 : {set T}) (l : seq A) :
  foldS f (s1 :|: s2) l = foldS f s1 l :|: foldS f s2 l.
Proof. by elim: l => //= x l ihl; rewrite bindSU. Qed.

End SetFold.

(*******************************************************************************)
