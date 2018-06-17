(******************************************************************************)
(* (c) 2017-2018 Mines ParisTech, LIRIS                                       *)
(*                                                                            *)
(* Some parts based on the math-comp library.                                 *)
(* Distributed under the terms of CeCILL-B.                                   *)
(*                                                                            *)
(*                                                                            *)
(* _Aims_ to be a certified Datalog Engine. Currently, axioms are used to     *)
(* extract to efficient implementations of Maps and Sets in OCaml, so handle  *)
(* with case. Additionally, the main theorem should be strengthened.          *)
(*                                                                            *)
(******************************************************************************)
From mathcomp Require Import all_ssreflect.
From VUP Require Import aux.

Set Warnings "-projection-no-head-constant".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* For our clausal records *)
Set Primitive Projections.

Delimit Scope vup_scope with V.
Open Scope vup_scope.

Module PP.

Record prod (A B:Type) : Type := { fst : A; snd: B; }.

Add Printing Let prod.

Notation "x * y" := (prod x y) : type_scope.
(* Overloading the regular notation will break ssr's rewrite ?(a,b) *)
Notation "'( x , y , .. , z )" := ({| fst := .. {| fst := x; snd := y; |} .. ; snd := z|}) : core_scope.

Delimit Scope pair_scope with PAIR.
Open Scope pair_scope.

(* Notations for pair/conjunction projections *)
Notation "p .1" := (fst p)
  (at level 2, left associativity, format "p .1") : pair_scope.
Notation "p .2" := (snd p)
  (at level 2, left associativity, format "p .2") : pair_scope.

Definition prod_curry A B C (f : A -> B -> C) := [fun x => f x.1 x.2].

Fixpoint zip S T (s : seq S) (t : seq T) {struct t} :=
  match s, t with
  | x :: s', y :: t' => '(x, y) :: zip s' t'
  | _, _ => [::]
  end.

End PP.
Import PP.

Section PrimPairTheory.

Definition pp_rep A B (x : A * B) : (Datatypes.prod A B) :=
  pair (fst x) (snd x).
Definition pp_con A B (x : Datatypes.prod A B) : A * B :=
  {| fst := Datatypes.fst x; snd := Datatypes.snd x; |}.
Definition pp_repK A B : cancel (@pp_rep A B) (@pp_con _ _).
Proof. by []. Defined.

Section PPEq.
Variable (A B: eqType).
Local Notation pp := (@prod A B).
Canonical pp_eqType     := Eval hnf in EqType     pp (CanEqMixin     (@pp_repK A B)).

Lemma xpair_eqE (x1 y1 : A) (x2 y2 : B) :
    ('(x1, x2) == '(y1, y2)) = (x1 == y1) && (x2 == y2).
Proof. by []. Qed.

End PPEq.
Section PPChoice.
Variable (A B: choiceType).
Local Notation pp := (@prod A B).
Canonical pp_choiceType := Eval hnf in ChoiceType pp (CanChoiceMixin (@pp_repK A B)).
End PPChoice.
Section PPCount.
Variable (A B: countType).
Local Notation pp := (@prod A B).
Canonical pp_countType  := Eval hnf in CountType  pp (CanCountMixin  (@pp_repK A B)).
End PPCount.
Section PPFin.
Variable (A B: finType).
Local Notation pp := (@prod A B).
Canonical pp_finType    := Eval hnf in FinType    pp (CanFinMixin    (@pp_repK A B)).
End PPFin.
End PrimPairTheory.

(* Unfolding help https://coq.inria.fr/refman/tactics.html#hevea_command184 *)

(******************************************************************************)
(*                                                                            *)
(* Parametric logic program syntax normalized wrt head symbols.               *)
(*                                                                            *)
(******************************************************************************)
Section ParamSyntax.
Section ParamDef.

(******************************************************************************)
(* Suffix list:                                                               *)
(*                                                                            *)
(*       a == atom                                                            *)
(*       l == literal                                                         *)
(*       b == conjuntive component                                            *)
(*       d == disjuntive component                                            *)
(*       c == clause                                                          *)
(*                                                                            *)
(******************************************************************************)

Variables (T : Type) (Σ : Type) (L : Type).

Record atom    := Atom    { syma : Σ; arga : T * T }.
Record lit     := Lit     { tagl : L; atoml: atom }.
Record cbody   := CBody   { litb : seq lit }.
Record clause  := Clause  { headc: T * T; bodyc : seq cbody }.

(* Some body theory *)

Definition bcons l b := {| litb := l :: litb b |}.

Notation "[ :: 'B' ]" := {| litb := [::] |} (at level 0, format "[ :: 'B' ]") : vup_scope.

Notation "[ :: 'B' l1 ]" := (bcons l1 {| litb := [::] |})
  (at level 0, format "[ ::  'B' l1 ]") : vup_scope.

Notation "[ :: 'B' l & b ]" := (bcons l b) (at level 0, only parsing) : vup_scope.

Notation "[ :: 'B' l1 , l2 , .. , ln & b ]" := (bcons l1 (bcons l2 .. (bcons ln b) ..))
  (at level 0, format
  "'[hv' [ :: 'B' '['  l1 , '/'  l2 , '/'  .. , '/'  ln ']' '/ '  &  b ] ']'"
  ) : vup_scope.

Lemma bconsE l ll : {| litb := l :: ll |} = bcons l {| litb := ll |}.
Proof. by []. Qed.

Lemma eq_litb_cons l1 cb1 l2 cb2 :
  [::B l1 & cb1] = [::B l2 & cb2] ->
  l1 = l2 /\ cb1 = cb2.
Proof. by case=> h1 h2; split => //; congr CBody. Qed.

Lemma cbody_rect
      (P : cbody -> Type)
      (H0 : P [::B])
      (Hn : forall (l : lit) (b : cbody), P b -> P [::B l & b]) :
  forall l : cbody, P l.
Proof. by case; elim=> // l hl ihl; apply: (Hn _ {| litb := hl |}). Defined.

Lemma cbody_ind
      (P : cbody -> Prop)
      (H0 : P [::B])
      (Hn : forall (l : lit) (b : cbody), P b -> P [::B l & b]):
  forall l : cbody, P l.
Proof. by case; elim=> // l hl ihl; apply: (Hn _ {| litb := hl |}). Defined.

(* Match lemma *)
CoInductive cbody_spec : cbody -> Type :=
 | CBodyNil : cbody_spec [::B]
 | CBodyCons l cb : cbody_spec [::B l & cb].

Lemma cbodyP cb : cbody_spec cb.
Proof. by case: cb; case=> [|l ll]; [|rewrite bconsE]; constructor. Qed.

Definition syml := syma \o atoml.
Definition argl := arga \o atoml.

Definition tsyml l := '(syml l, tagl l).

Definition litd d := flatten (map litb d).
Definition litc c := litd (bodyc c).

End ParamDef.

Open Scope vup_scope.
Prenex Implicits syma syml arga tagl atoml.

Section ParamFinite.

Variables (T : Type) (Σ : finType) (L : finType).

Inductive program := Program of {ffun Σ -> clause T Σ L}.
Coercion fun_of_prog p := let: Program c := p in c.

Implicit Types (a : atom T Σ).
Implicit Types (l : lit T Σ L).
Implicit Types (b : cbody T Σ L).
Implicit Types (d : seq (cbody T Σ L)).
Implicit Types (c : clause T Σ L).
Implicit Types (p : program).

(* Set of symbols mentioned the body of a clause *)
Definition symb b := \bigcup_(l <- litb b) [set (syma \o atoml) l].
Definition symd d := \bigcup_(b <- d) symb b.
Definition symc c := symd (bodyc c).
Definition symp p := \bigcup_s (symc (p s)).

(* Tagged-symbols *)
Definition tsymb b := \bigcup_(l <- litb b) [set tsyml l].
Definition tsymd d := \bigcup_(b <- d) tsymb b.
Definition tsymc c := tsymd (bodyc c).
Definition tsymp p := \bigcup_s (tsymc (p s)).

End ParamFinite.

(* Manipulation of parametric Term-syntax *)
Section ParamMorph.

Variables (Σ : Type) (L T U : Type) (f : T -> U).

Implicit Types (a : atom T Σ).
Implicit Types (l : lit T Σ L).
Implicit Types (b : cbody T Σ L).

Definition atomM    a := Atom (syma a) '(f (arga a).1, f (arga a).2).
Definition litM     l := Lit (tagl l) (Atom (syml l) '(f (argl l).1, f (argl l).2)).
Definition bodyM    b := CBody (map litM (litb b)).
Definition clauseM  c := Clause '(f (headc c).1, f (headc c).2) [seq bodyM l | l <- bodyc c].

(* Invariants over the morphisms *)
(* XXX: Use {morph} notation *)
Lemma symaM a : syma (atomM a) = syma a.
Proof. by []. Qed.

Lemma symlM l : syml (litM l) = syml l.
Proof. by []. Qed.

End ParamMorph.

(* Manipulation of parametric Tag-syntax *)
Section ParamTag.

Variables (Σ : Type) (L T U : Type) (g : L -> U).

Implicit Types (l : lit T Σ L).
Implicit Types (b : cbody T Σ L).

Definition litT     l := Lit (g (tagl l)) (atoml l).
Definition bodyT    b := CBody (map litT (litb b)).
Definition clauseT  c := Clause (headc c) [seq bodyT l | l <- bodyc c].

Lemma symlT l : syml (litT l) = syml l.
Proof. by []. Qed.


End ParamTag.

Section ParamCombined.

Variables (Σ : Type) (L T U V : Type) (f : T -> V) (g : L -> U).

Implicit Types (l : lit T Σ L).
Implicit Types (b : cbody T Σ L).

Lemma litM_litT l : litM f (litT g l) = litT g (litM f l).
Proof. by []. Qed.

Lemma bodyM_bodyT b : bodyM f (bodyT g b) = bodyT g (bodyM f b).
Proof. by rewrite /bodyM /bodyT -!map_comp. Qed.

End ParamCombined.

Section ParamFinMorph.

Variables (Σ L : finType) (T U : Type) (V : finType) (f : T -> U) (g : L -> V).

Implicit Types (a : atom T Σ).
Implicit Types (l : lit T Σ L).
Implicit Types (b : cbody T Σ L).
Implicit Types (p : program T Σ L).

Definition programM p := Program [ffun s => clauseM f (p s)].

Lemma symbM b : symb (bodyM f b) = symb b.
Proof. by rewrite /symb big_map; apply: eq_bigr. Qed.

Lemma tsymbM b : tsymb (bodyM f b) = tsymb b.
Proof. by rewrite /tsymb big_map; apply: eq_bigr. Qed.

(* Support is a morphism *)
Lemma symcM c : symc (clauseM f c) = @symc _ Σ L c.
Proof.
by rewrite /symc /symd big_map; apply: eq_bigr => l _; rewrite symbM.
Qed.

Lemma tsymcM c : tsymc (clauseM f c) = @tsymc _ Σ L c.
Proof.
by rewrite /tsymc /tsymd big_map; apply: eq_bigr => l _; rewrite tsymbM.
Qed.

Lemma sympM p : symp p = symp (programM p).
Proof. by apply: eq_bigr => c ?; rewrite ffunE symcM. Qed.

Lemma symbT b : symb (bodyT g b) = symb b.
Proof. by rewrite /symb big_map; apply: eq_bigr. Qed.

Lemma symcT c : symc (clauseT g c) = @symc T Σ L c.
Proof.
by rewrite /symc /symd big_map; apply: eq_bigr => l _; rewrite symbT.
Qed.

End ParamFinMorph.

Section ParamEq.

Variables (T Σ L : eqType).

Definition of_atom (a : atom T Σ) := '(syma a, arga a).
Definition to_atom (a : Σ * (T * T)) := Atom a.1 a.2.

Definition atom_sub : @subType (Σ * (T * T)) xpredT.
apply: (@NewType _ _ of_atom to_atom); last by [].
by move=> P K [s a]; have := K '(s, a).
Defined.

(* Canonical atom_subType    := Eval hnf in [newType for of_atom]. *)
Canonical atom_subType    := Eval hnf in atom_sub.
Canonical atom_eqType     := Eval hnf in EqType _     [eqMixin     of @atom _ _ by <: ].
(* Canonical atom_choiceType := Eval hnf in ChoiceType _ [choiceMixin of @atom _ _ by <:]. *)
(* Canonical atom_finType     := Eval hnf in ChoiceType _ [choiceMixin of lit by <:]. *)

Definition of_lit (l : lit T Σ L) := '(tagl l, atoml l).
Definition to_lit (l : L * atom T Σ) := Lit l.1 l.2.

Definition lit_sub : @subType (L * atom T Σ) xpredT.
apply: (@NewType _ _ of_lit to_lit); last by [].
by move=> P K [t a]; have := K '(t, a).
Defined.

Canonical lit_subType     := Eval hnf in lit_sub.
Canonical lit_eqType      := Eval hnf in EqType _     [eqMixin     of @lit _ _ _ by <: ].

Definition of_cbody (b : cbody T Σ L) := let: CBody b := b in b.
Definition to_cbody (l : seq (lit T Σ L)) := CBody l.

Definition cbody_sub : @subType (seq (lit T Σ L)) xpredT.
apply: (@NewType _ _ of_cbody to_cbody); last by case.
by move=> P K [t]; have := K t.
Defined.

Canonical cbody_subType   := Eval hnf in cbody_sub.
Canonical cbody_eqType    := Eval hnf in EqType _     [eqMixin     of @cbody _ _ _ by <: ].

End ParamEq.

Section ParamTheory.

Variables (Σ L : finType) (T T' : eqType).
Implicit Types (l : lit T Σ L).
Implicit Types (b : cbody T Σ L).
Implicit Types (c : clause T Σ L).
Implicit Types (p : program T Σ L).
Implicit Types (ss : {set Σ}).

Lemma syml_in_symb l b (l_in : l \in litb b) : syml l \in symb b.
Proof. by apply/bigcup_seqP; exists l; rewrite // inE eqxx. Qed.

Lemma tsyml_in_tsymb l b (l_in : l \in litb b) : tsyml l \in tsymb b.
Proof. by apply/bigcup_seqP; exists l; rewrite // inE eqxx. Qed.

Lemma symb_sub_symd b d (b_in : b \in d) : symb b \subset symd d.
Proof.
apply/bigcups_seqP=> l l_in _; rewrite sub1set.
by apply/bigcup_seqP; exists b; rewrite // syml_in_symb.
Qed.

Lemma tsymb_sub_tsymd b d (b_in : b \in d) : tsymb b \subset tsymd d.
Proof.
apply/bigcups_seqP=> l l_in _; rewrite sub1set.
by apply/bigcup_seqP; exists b; rewrite // tsyml_in_tsymb.
Qed.

Lemma symb_sub_symc b c (b_in : b \in bodyc c) : symb b \subset symc c.
Proof. exact: symb_sub_symd. Qed.

Lemma tsymb_sub_tsymc b c (b_in : b \in bodyc c) : tsymb b \subset tsymc c.
Proof. exact: tsymb_sub_tsymd. Qed.

Lemma tsymb_in_symb b s t:
  '(s, t) \in tsymb b -> s \in symb b.
Proof.
case/bigcup_seqP=> l lin; rewrite andbT inE => /eqP [Hs Ht].
by apply/bigcup_seqP; exists l; rewrite // inE Hs eqxx.
Qed.

Lemma tsymc_in_symc c s t:
  '(s, t) \in tsymc c -> s \in symc c.
Proof.
case/bigcup_seqP=> b bin; rewrite andbT => /tsymb_in_symb hs.
by apply/bigcup_seqP; exists b; rewrite ?bin ?hs.
Qed.

(* Lemma syml_notin_symb ss b c : *)
Lemma disjoint_symd_symb d b ss :
  b \in d ->
  [disjoint symd d & ss] ->
  [disjoint symb b & ss].
Proof. by move=> b_in /disjoint_trans; apply; apply: symb_sub_symd. Qed.

Lemma disjoint_tsymd_tsymb d b (ss : {set Σ * L}) :
  b \in d ->
  [disjoint tsymd d & ss] ->
  [disjoint tsymb b & ss].
Proof. by move=> b_in /disjoint_trans; apply; apply: tsymb_sub_tsymd. Qed.

Lemma disjoint_symc_symb ss b c :
  b \in bodyc c ->
  [disjoint symc c & ss] ->
  [disjoint symb b & ss].
Proof. exact: disjoint_symd_symb. Qed.

Lemma disjoint_tsymc_tsymb (ss : {set Σ * L}) b c :
  b \in bodyc c ->
  [disjoint tsymc c & ss] ->
  [disjoint tsymb b & ss].
Proof. exact: disjoint_tsymd_tsymb. Qed.

Lemma cl_syml_in_supp c l ss
      (hc : symc c \subset ss)
      (hl : l \in litc c) :
  syml l \in ss.
Proof.
case/flatten_mapP: hl => b b_in l_in.
move/bigcups_seqP/(_ b b_in erefl)/subsetP/(_ (syml l)): hc => -> //.
exact: syml_in_symb.
Qed.

Lemma cl_tsyml_in_supp c l (tss : {set Σ * L})
      (hc : tsymc c \subset tss)
      (hl : l \in litc c) :
  tsyml l \in tss.
Proof.
case/flatten_mapP: hl => b b_in l_in.
move/bigcups_seqP/(_ b b_in erefl)/subsetP/(_ (tsyml l)): hc => -> //.
exact: tsyml_in_tsymb.
Qed.

Lemma cb_syml_in_supp b c l ss
      (hc : symc c \subset ss)
      (hl : l \in litb b)
      (hb : b \in bodyc c) :
  syml l \in ss.
Proof. by apply/(cl_syml_in_supp hc); apply/flatten_mapP; exists b. Qed.

Lemma cb_tsyml_in_supp b c l (ss : {set Σ * L})
      (hc : tsymc c \subset ss)
      (hl : l \in litb b)
      (hb : b \in bodyc c) :
  tsyml l \in ss.
Proof. by apply/(cl_tsyml_in_supp hc); apply/flatten_mapP; exists b. Qed.

(* ss is a proper slice of program p iff all the clauses with head s
   \in ss only refer to symbols in ss *)
Definition wf_slice ss p := [forall s in ss, symc (p s) \subset ss].

(* TODO *)
Lemma wf_sliceP ss p
      (hs : wf_slice ss p) :
  {in ss, forall s, {subset symc (p s) <= ss}}.
Proof. by move=> s hin; apply/subsetP; move: s hin; apply/forall_inP. Qed.
(* should be forallPP + implP + subsetP *)

Lemma wf_slice_litP ss p l
      (hs : wf_slice ss p) :
  {in ss, forall s, l \in litc (p s) -> syml l \in ss}.
Proof.
by move=> s hin; have/subsetP := wf_sliceP hs hin; exact/cl_syml_in_supp.
Qed.

Lemma wf_sliceU ss1 ss2 p :
  wf_slice (ss1 :|: ss2) p =
  [forall s in ss1, symc (p s) \subset ss1 :|: ss2] &&
  [forall s in ss2, symc (p s) \subset ss1 :|: ss2].
Proof. by rewrite /wf_slice eq_forall_setU. Qed.

(* Weakening? Strengthening?

   Note that wf_slice is delicate as to adding of removing any symbol
   can totally break it. Example, the set {p,q} is primitive for
   program:

   p <- q.
   q <- p.
   r <- s.

   Also note that {r,p,q} can be never a proper slice.

   This is OK for full Datalog but a bit inconvenient in the
   non-recursive setting. In order to build a stronger theory we need
   something with more structure than {set Σ}.
 *)

End ParamTheory.
End ParamSyntax.

Notation "[ :: 'B' ]" := {| litb := [::] |} (at level 0, format "[ :: 'B' ]") : vup_scope.

Notation "[ :: 'B' l1 ]" := (bcons l1 {| litb := [::] |})
  (at level 0, format "[ :: 'B'  l1 ]") : vup_scope.

Notation "[ :: 'B' l & b ]" := (bcons l b) (at level 0, only parsing) : vup_scope.

Notation "[ :: 'B' l1 , l2 , .. , ln & b ]" := (bcons l1 (bcons l2 .. (bcons ln b) ..))
  (at level 0, format
  "'[hv' [ :: 'B' '['  l1 , '/'  l2 , '/'  .. , '/'  ln ']' '/ '  &  b ] ']'"
  ) : vup_scope.

Coercion litb : cbody >-> seq.
Prenex Implicits litb atomM litM bodyM clauseM programM.

(******************************************************************************)
(* Some helpers for dealing with variables and substitution                   *)
(******************************************************************************)
Section VarSyntax.

Variables (n : nat) (T : Type) (Σ : Type) (L : Type).

Inductive term :=
| Var of 'I_n
| Val of T.

Definition gr := {ffun 'I_n -> T}.

Implicit Types (g : gr) (t : term).

Definition grt g t :=
  match t with
  | Var n   => g n
  | Val c => c
  end.

Definition gatom := atom T Σ.
Definition oatom := atom term Σ.

Definition grh : gr -> term * term -> T * T := [fun gr t => '(grt gr t.1, grt gr t.2)].
Definition gra : gr -> oatom -> gatom := atomM \o grt.

Definition glit := lit T Σ L.
Definition olit := lit term Σ L.

Definition grl : gr -> olit -> glit := litM \o grt.

Definition gbody := cbody T Σ L.
Definition obody := cbody term Σ L.

(* Generic version *)
Definition Xbody X := cbody X Σ L.

Definition gclause := clause T Σ L.
Definition oclause := clause term Σ L.

Definition grb : gr -> obody    -> gbody    := bodyM    \o grt.
Definition grc : gr -> oclause  -> gclause  := clauseM  \o grt.
(* Definition grp : gr -> oprogram -> gprogram := programM \o grt. *)

Lemma grb_cons gr l bd :
  grb gr [::B l & bd ] = [::B grl gr l & grb gr bd ].
Proof. by []. Qed.

Definition lifta : gatom    -> oatom    := atomM   Val.
Definition liftl : glit     -> olit     := litM    Val.
Definition liftb : gbody    -> obody    := bodyM   Val.
Definition liftc : gclause  -> oclause  := clauseM Val.

Lemma liftb_cons l b : liftb [::B l & b] = [::B liftl l & liftb b].
Proof. by []. Qed.

Lemma lifta_inj : injective lifta.
Proof. by case=> ? [? ?]; case=> ? [? ?] [? ? ?]; congr (Atom _ '(_,_)). Qed.

(* Lemma liftl_inj : injective liftl. *)
(* Proof. case=> [t1 a1] [t2 a2] []. *)

End VarSyntax.

Section FinVarSyntax.

Variables (n : nat) (T : Type) (Σ L : finType).

Definition gprogram := program T Σ L.
Definition oprogram := program (term n T) Σ L.

End FinVarSyntax.

Section TermEq.

Variables (n : nat) (T : eqType).

Notation termRep := ('I_n + T)%type.

Definition term_rep (t : term n T) : termRep :=
  match t with | Var i => inl i | Val c => inr c end.

Definition term_con (r : termRep) : term n T :=
  match r with | inl i => Var _ i | inr c => Val _ c end.

(** cancelation lemma for terms *)
Lemma term_repK : cancel term_rep term_con.
Proof. by case. Qed.

(** canonical instances for terms *)
Canonical term_eqType := Eval hnf in EqType (term _ _) (CanEqMixin term_repK).
(* Canonical term_choiceType := Eval hnf in ChoiceType (term _ _) (CanChoiceMixin term_repK). *)

End TermEq.

Section GrTheory.

Variables (n : nat) (T : eqType) (Σ L : finType).
Implicit Types (ss : {set Σ}) (p : oprogram n T Σ L) (gr : gr n T).

(* Slicing *)
(* Lemma wf_slice_grP ss p gr : wf_slice ss p = wf_slice ss (grp gr p). *)
(* Proof. by apply: eq_forall_inb => s hs; rewrite ffunE symcM. Qed. *)

(* Lemma mem_litc_gr l gr cl : *)
(*   l \in litc (grc gr cl) = (l \in litc cl). *)

End GrTheory.

Section VarTheory.

Variable (n : nat) (Σ V L : Type).
Implicit Types (t : term n V) (a : atom (term n V) Σ).
Implicit Types (l : lit (term n V) Σ L) (cb : cbody (term n V) Σ L).

(* Variables of terms *)
Definition vart t  : {set 'I_n} := if t is Var v then [set v] else set0.
Definition vara a  : {set 'I_n} := vart (arga a).1 :|: vart (arga a).2.
Definition varl l  : {set 'I_n} := vara (atoml l).
Definition varb cb : {set 'I_n} := \bigcup_(l <- litb cb) varl l.
Definition varc cl : {set 'I_n} := \bigcup_(l <- litc cl) varl l.

(* Safety, all the disjuntive clauses must ground the head *)
Definition safe_cb hd cb :=
  [&& vart hd.1 \subset varb cb &
      vart hd.2 \subset varb cb ].

Definition safe_cl cl := all (safe_cb (headc cl)) (bodyc cl).
Definition safe_pr p  := forall s : Σ, safe_cl (p s).

End VarTheory.

Arguments lifta [n T Σ].
Arguments liftl [n T Σ L].
Arguments liftb [n T Σ L].

Section Substitution.

Variables (n : nat) (V : finType) (Σ : finType) (L : eqType).
Definition sub := nosimpl {ffun 'I_n -> option V}.
Definition ssub := {set sub}.

Implicit Types (t : term n V) (a : oatom n V Σ) (l : olit n V Σ L).
Implicit Types (s : sub) (ss : ssub) (v : 'I_n) (b : 'I_n * V).

Definition sub0 : sub := [ffun _ => None].

(** Variable is mapped/free by the substitution s *)
Definition mem_free  s v : bool := s v == None.

(** Binding b belongs to s *)
Definition mem_binding s b : bool := s b.1 == Some b.2.

Definition eqbind_class := sub.

Identity Coercion sub_of_eqbind : eqbind_class >-> sub.

Coercion pred_of_eq_bind (s : eqbind_class) : pred_class := [eta mem_binding s].

Canonical mem_bind_symtype := mkPredType mem_binding.

Lemma mem_bindE s b : b \in s = (s b.1 == Some b.2). Proof. by []. Qed.

Definition inE := (mem_bindE, inE).

(* New but untested definitions
CoInductive sub_spec (s : sub) (v : 'I_n) : option V -> Type :=
| subSome : forall c, (v, c) \in s -> sub_spec s v (Some c)
| subNone :           ~~ s v       -> sub_spec s v None.

Lemma subP s v : sub_spec s v (s v).
Proof. by case E: (s _) => [a|]; constructor; apply/eqP; rewrite ?E. Qed.
*)

CoInductive sub_spec (s : sub) (v : 'I_n) : option V -> Type :=
| subSome : forall c, '(v, c) \in s -> sub_spec s v (Some c)
| subNone :            mem_free s v -> sub_spec s v None.

Lemma subP s v : sub_spec s v (s v).
Proof. by case E: (s _) => [a|]; constructor; apply/eqP. Qed.

(** substitution [s2] extends [s1] *)
Definition le_sub s1 s2 :=
  [forall v : 'I_n, if s1 v is Some b1 then '(v, b1) \in s2 else true].

Notation "A \sub B" := (le_sub A B)
  (at level 70, no associativity) : bool_scope.

Lemma lesubP s1 s2 :
  reflect (forall b, b \in s1 -> b \in s2) (s1 \sub s2).
Proof.
apply/(iffP forallP) => [H b|H v]; rewrite ?mem_bindE; case E: (s1 _) => [e|] //.
  by have := H b.1; rewrite E => ?; case/eqP=> <-.
by apply: H; rewrite mem_bindE E.
Qed.

Lemma lesubss s : s \sub s.
Proof. exact/lesubP. Qed.

Lemma lesub_trans s1 s2 s3 : s2 \sub s3 -> s1 \sub s2 -> s1 \sub s3.
Proof. by move=> /lesubP H1 /lesubP H2; apply/lesubP=> b /H2; auto. Qed.

Lemma lesub0s s : sub0 \sub s.
Proof. by apply/lesubP=> ?; rewrite inE ffunE. Qed.

(** Extending a substitution [s] with a binding [(v,d)] *)
Definition add s v d := [ffun u => if u == v then Some d else s u].

(** If [v] was free in [s], substitution extension respects ordering. *)
Lemma sub_add s v d : mem_free s v -> s \sub (add s v d).
Proof.
move=> H; apply/lesubP=> -[u e].
rewrite !inE !ffunE /=; case: ifP => //= /eqP -> /eqP C.
by rewrite /mem_free C in H.
Qed.

Lemma sub_st_add v d s' s :
  s' \sub s -> s v = Some d -> s' v = None -> add s' v d \sub s.
Proof.
move=> Hsub Hs Hs'; apply/forallP=> v'; rewrite /add ffunE.
by case: eqP => [->| Hv]; first exact/eqP; move/forallP in Hsub; apply/Hsub.
Qed.

Lemma addE (s : sub) (v : 'I_n) d : (add s v d) v = Some d.
Proof. by rewrite ffunE eqxx. Qed.

Lemma add_add (s : sub) v d e : (add (add s v e) v d) = add s v d.
Proof. by apply/ffunP=> u; rewrite !ffunE; case: eqP. Qed.

(** Term substitution *)
Definition subt s t : term n V :=
  match t with
  | Val d => t
  | Var v   => if s v is Some d then Val _ d else t
  end.

Definition suba   s a : oatom n V Σ   := atomM (subt s) a.
Definition subl   s l : olit  n V Σ L := litM  (subt s) l.
Definition subb   s c : obody n V Σ L := bodyM (subt s) c.

Lemma subb_cons s l cb :
  subb s [::B l & cb] = [::B subl s l & subb s cb].
Proof. by []. Qed.

CoInductive sub_sub_spec (s r : sub) (v : 'I_n) (h : s \sub r) :
                    option V -> option V -> Type :=
| sSome : forall c, s v = Some c ->                 sub_sub_spec v h (Some c) (Some c)
| sMixx : forall c, s v = None   -> r v = Some c -> sub_sub_spec v h (Some c) None
| sNone :           r v = None   ->                 sub_sub_spec v h None None.

Lemma substP s1 s2 : reflect {subset s1 <= s2} (s1 \sub s2).
Proof.
apply/(iffP forallP)=> [H t|H v]; last by case: subP => // c ?; apply: H.
by move/eqP=> t_s1; have:= H t.1; rewrite t_s1.
Qed.

Lemma subsP s r v (h : s \sub r) : sub_sub_spec v h (r v) (s v).
Proof.
case: (s _) / subP => [c|] /= hv.
  by move/substP/(_ _ hv): (h) => /eqP ->; exact/sSome/eqP.
by case: (r _) / subP => [d|] E; [apply: sMixx; exact/eqP| exact/sNone/eqP].
Qed.

(** **** Substitution Extensionality Lemma *)
Lemma substE s1 s2 :
  reflect (forall d v, s1 v = Some d -> s2 v = Some d) (s1 \sub s2).
Proof.
apply/(iffP idP)=> [H d v| H]; first by case: subsP.
by apply/substP=> b; rewrite !inE => /eqP H1; apply/eqP/H.
Qed.

(** substitution domain: set of all variables it binds *)
Definition dom s := [set v : 'I_n | s v].

Lemma mem_freeE v s : mem_free s v = (v \notin dom s).
Proof. by rewrite /mem_free inE; case: (s v). Qed.

Lemma domP v s : reflect (exists c, s v = Some c) (v \in dom s).
Proof.
rewrite inE; apply: (iffP idP); case: subP => //; last by move=> ?; case.
by move=> c ? ?; exists c.
Qed.

Lemma vart_sub_dom t s :
  reflect (exists c : V, subt s t = Val _ c) (vart t \subset dom s) .
Proof.
case: t => [v|x]; rewrite /= ?(sub0set, sub1set, inE); last first.
  by constructor; exists x.
by case: subP => [c|]; constructor; [exists c | case].
Qed.

Lemma vara_sub_dom a s :
  reflect (exists ga, suba s a = lifta ga)
          (vara a \subset dom s).
Proof.
apply: (iffP subUsetP) => [[/vart_sub_dom[v1 hv1]/vart_sub_dom[v2 hv2]]|].
  by exists (Atom (syma a) '(v1,v2)); congr Atom; rewrite hv1 hv2.
by case=> [ga [hs ha1 ha2]]; split; apply/vart_sub_dom; eauto.
Qed.

Lemma varl_sub_dom l s :
  reflect (exists gl, subl s l = liftl gl)
          (varl l \subset dom s).
Proof.
case: l => [t a]; apply: (iffP (vara_sub_dom _ _)).
  by case=> ga gas; exists (Lit t ga); congr Lit.
by case=> gl [ht hs ha1 ha2]; exists (atoml gl); congr Atom; rewrite // ha1 ha2.
Qed.

Lemma mem_consW (T : eqType) (P : T -> Type) y (l : seq T) :
  (forall x, x \in y :: l -> P x) ->
  (forall x, x \in l -> P x).
Proof. by move=> H x xin; apply: H; rewrite inE xin orbT. Qed.

(* XXX: Cleanup *)
Lemma varb_sub_dom cb s :
  reflect (exists gcb, subb s cb = liftb gcb)
          (varb cb \subset dom s).
Proof.
apply: (iffP bigcups_seqP); elim: cb => [|l cb ihc] H //=.
+ by exists (CBody [::]).
+ have/varl_sub_dom[gl gls] := H l (mem_head _ _) erefl.
  have[gb gbs] := ihc (mem_consW H).
  exists [::B gl & gb].
  by congr (CBody (_ :: _)) => //; case: gb gbs => gbl /= [gbs].
+ case: H; case=> [[|gl gcb]] //; rewrite subb_cons.
  rewrite (liftb_cons _ _ {| litb := gcb |}).
  case/eq_litb_cons=> hl hcb l' /predU1P[->|hin] _.
    by apply/varl_sub_dom; exists gl.
  by apply/ihc=> //; exists {| litb := gcb |}.
Qed.

End Substitution.

Notation "A \sub B" := (le_sub A B)
  (at level 70, no associativity) : bool_scope.

Arguments sub0 [n V].
Arguments sub  [n V].
Arguments ssub [n V].

(******************************************************************************)
(*                                                                            *)
(* Theory for incremental labelled graphs                                     *)
(*                                                                            *)
(* We describe (finite) labelled graphs plus a "delta" operation, that is     *)
(* to say, an update to the graph, consisting of a disjoint set of            *)
(* removals/additions.                                                        *)
(*                                                                            *)
(* For convenience, we will capture the disjointness invariant separatedly    *)
(* from the delta itself, and we prodive a coercion of course.                *)
(*                                                                            *)
(******************************************************************************)
Section VUP.
Section LabeledGraph.

(* Set of constants and labels *)
Variables (V Σ : finType).

(* [EJGA,XXX]: Why don't we use `rel V` for our graphs? *)
(* Labelled relations, paths, and transitive closure. *)
Record egraph := EGraph { e_val : {set V * V } }.
Coercion set_of_egraph (g : egraph) := e_val g.

Definition egraph_sub : @subType {set V * V} xpredT.
apply: (@NewType _ _ set_of_egraph EGraph); last by case.
by move=> P K s; have := K s.
Defined.

Canonical egraph_subType      := Eval hnf in egraph_sub.
Canonical egraph_eqType       := Eval hnf in EqType _     [eqMixin     of @egraph by <: ].
Canonical egraph_choiceType   := Eval hnf in ChoiceType _ [choiceMixin of @egraph by <: ].
Canonical egraph_countType    := Eval hnf in CountType  _ [countMixin  of @egraph by <: ].
Canonical egraph_subCountType := Eval hnf in [subCountType of egraph].
Canonical egraph_finType      := Eval hnf in FinType    _ [finMixin    of @egraph by <: ].
Canonical egraph_subFinType   := Eval hnf in [subFinType of egraph].

Definition fun_of_egraph (g : egraph) := fun v1 v2 => '(v1,v2) \in e_val g.
Coercion fun_of_egraph : egraph >-> Funclass.

Definition g0 := EGraph set0.

Lemma egraphE (g : egraph) v1 v2 : g v1 v2 = ('(v1,v2) \in g).
Proof. by []. Qed.

(* Flip of a graph *)
Definition flipg (g : egraph) : egraph := {| e_val := [set '(v.2,v.1) | v in e_val g] |}.
Lemma flipgP v1 v2 (g : egraph) : (flipg g) v2 v1 = g v1 v2.
(* Lemma flipgP v1 v2 (g : egraph) : (v2, v1) \in flipg g = ((v1, v2) \in g). *)
Proof.
by apply/imsetP/idP=> [[[n1 n2] hn [-> ->]]|hg]; last by exists '(v1,v2).
Qed.

(* Labelled graph with closures; we index by labels plus closed type *)
Inductive lrel := LRel of {ffun Σ -> egraph}.
Coercion fun_of_lrel (G : lrel) := let: LRel f := G in f.

Canonical lrel_subType       := Eval hnf in [newType for fun_of_lrel].
Canonical lrel_eqType        := Eval hnf in EqType _     [eqMixin     of @lrel by <: ].

Lemma lrelP (i1 i2 : lrel) : (i1 =1 i2) <-> i1 = i2.
Proof.
case: i1 i2 => [i1] [i2]; split => [h| [->] x] //.
by congr LRel; apply/ffunP=> x; have := h x.
Qed.

(* Delta application *)
Lemma lrelE (G : lrel) v1 (l : Σ) v2 : G l v1 v2 = ('(v1,v2) \in G l).
Proof. by case: G => f; case: (f l). Qed.

(* Notation inE := (lrelE, inE). *)

(* Support for a labelled graph *)
Definition suppg (G : lrel) : {set Σ} := [set s | set0 != G s].

Lemma suppgN_mem G s a : s \notin suppg G -> a \notin G s.
Proof. by rewrite inE negbK => /eqP <-; rewrite inE. Qed.

Lemma suppgN G s a1 a2 : s \notin suppg G -> G s a1 a2 = false.
Proof. by move/suppgN_mem; rewrite lrelE => H; apply/negbTE. Qed.

Definition lg0 : lrel := LRel [ffun _ => g0].

Definition putl (i : lrel) s g : lrel :=
  LRel [ffun s' => EGraph (if s' == s then g else i s')].

(* Use smarter constructors *)
Definition addl s (g : egraph) (i : lrel) : lrel :=
  LRel [ffun s' => EGraph (if s' == s then g :|: i s' else i s')].

Definition reml s (g : egraph) (i : lrel) : lrel :=
  LRel [ffun s' => EGraph (if s' == s then i s' :\: g else i s')].

(* XXX: Fixme, unison of lrel *)
Definition lrelU (i1 i2 : lrel) : lrel :=
  LRel [ffun s => EGraph (i1 s :|: i2 s)].

Notation "i1 :||: i2" := (lrelU i1 i2) (at level 52, left associativity).

Lemma lrelUC (i1 i2 : lrel) : i1 :||: i2 = i2 :||: i1.
Proof. by apply/lrelP=> s; rewrite !ffunE setUC. Qed.

Lemma lrelUA (i1 i2 i3 : lrel) : i1 :||: (i2 :||: i3) = i1 :||: i2 :||: i3.
Proof. by apply/lrelP=> s; rewrite !ffunE setUA. Qed.

Lemma in_lrelU (i1 i2 : lrel) s v1 v2 :
  ('(v1,v2) \in (i1 :||: i2) s) = ('(v1,v2) \in i1 s) || ('(v1,v2) \in i2 s).
Proof. by rewrite ffunE inE. Qed.

(* Set of egdes involved in the graph, equivalent to the support of an
 * interpretation.
 *)
Definition edgeg (e : V * Σ * V) := let: '(_,s,_) := e in s.
Definition nodeg (e : V * Σ * V) := let: '(v1,_,v2) := e in (v1,v2).

(* Definition suppg (G : lrel) : {set Σ} := [set edgeg e | s in Σ, e in G s]. *)

(* Coercion from the set of egdes to its characteristic function. *)
(* Definition lrelF (G : lrel) := fun l v1 v2 => (v1,v2) \in (fun_of_lrel G l). *)
(* Coercion lrelF : lrel >-> Funclass. *)

(* Open question: How do we want to model Δ?

   We have several choices, we could for example model it as a
   function indexed by the label to a tuple of additions/removals.

   Whatever we do we need a way to reason modularly about a particular
   symbol, and that is the part of the theory that is not clear.
 *)

(* Deltas of labelled graphs are disjoint sets of edges *)
Structure raw_edelta := { addd : lrel; deld : lrel; }.
Definition wf_edelta Δ := [forall s, [disjoint (addd Δ) s & (deld Δ) s]].
(* Lack of naming produces a primitive record warning. *)
Structure edelta := { dval :> raw_edelta; _edelta_subproof : wf_edelta dval }.

Definition edelta_sub : @subType (raw_edelta) wf_edelta.
exact: (@SubType _ wf_edelta edelta dval Build_edelta).
Defined.
Canonical edelta_subType := Eval hnf in edelta_sub.
(* Canonical edelta_subType := Eval hnf in [subType for dval]. *)

Implicit Types (i : lrel) (Δ : edelta).

Definition suppΔ Δ := suppg (addd Δ) :|: suppg (deld Δ).

(* Apply a delta to a labelled graph *)
Definition appd (i : lrel) Δ : lrel :=
  LRel [ffun s => EGraph (i s :\: deld Δ s :|: addd Δ s)].

Notation "i :+: Δ" := (appd i Δ) (at level 52, left associativity).

Lemma in_appd s x i Δ :
  x \in (i :+: Δ) s = ((x \in i s) && (x \notin (deld Δ) s)) || (x \in (addd Δ) s).
Proof. by rewrite !ffunE !inE; congr orb; rewrite andbC. Qed.

Lemma suppΔN s i Δ : s \notin suppΔ Δ -> (i :+: Δ) s = i s.
Proof.
rewrite !inE negb_or !negbK => /andP[/eqP ha /eqP hr].
by rewrite !ffunE -ha -hr setD0 setU0.
Qed.

(* Delta composition *)
Definition compd i Δ Δ' := appd (appd i Δ) Δ'.
(* TODO: Delta update *)

Definition raw_putΔ Δ s (Δp Δn : egraph) :=
  {| addd := putl Δ.(addd) s Δp;
     deld := putl Δ.(deld) s (EGraph (Δn :\: Δp));
  |}.

Lemma wf_putΔ Δ s Δp Δn : wf_edelta (raw_putΔ Δ s Δp Δn).
Proof.
case: Δ => Δ H; apply/forallP=> s'; rewrite !ffunE.
case: eqP => ?; last exact: forallP H s'.
by rewrite disjoints_subset setCD /= setUC subsetUl.
Qed.

Definition putΔ Δ s Δp Δn := Build_edelta (wf_putΔ Δ s Δp Δn).

(* Update a delta with additions: We must perform the update such that
   the wf_invariant is preserved. *)
Definition raw_addΔ s g Δ : raw_edelta :=
  {| addd := addl s g (addd Δ);
     deld := reml s g (deld Δ);
  |}.

Lemma wf_addΔ s g Δ : wf_edelta (raw_addΔ s g Δ).
Proof.
case: Δ => Δ H; apply/forallP=> s'; rewrite !ffunE.
case: eqP => [->{s'}|//]; last by have/forallP := H.
have Hs := forallP H s; rewrite !disjoints_subset setCD setUC in Hs *.
by rewrite setSU.
Qed.

Definition addΔ s g Δ := Build_edelta (wf_addΔ s g Δ).

(* Update a delta with removal *)
Definition raw_remΔ s g Δ : raw_edelta :=
  {| addd := reml s g (addd Δ);
     deld := addl s g (deld Δ);
  |}.

Lemma wf_remΔ s g Δ : wf_edelta (raw_remΔ s g Δ).
Proof.
case: Δ => Δ H; apply/forallP=> s'; rewrite !ffunE.
case: eqP => [->{s'}|//]; last by have/forallP := H.
have Hs := forallP H s; rewrite !disjoints_subset setCU in Hs *.
by rewrite subDset setUIr setUCr setTI subsetU // Hs orbT.
Qed.

Definition remΔ s g Δ := Build_edelta (wf_remΔ s g Δ).

Lemma suppΔ_addΔ s g Δ : suppΔ (addΔ s g Δ) \subset (s |: suppΔ Δ).
Proof.
apply/subsetP=> r; rewrite !inE; case/orP; rewrite !ffunE; case: (r == s) / eqP => //=.
  by move=> _ ->.
by move=> _ ->; rewrite orbT.
Qed.

Lemma suppΔ_putΔ Δ s g1 g2 : suppΔ (putΔ Δ s g1 g2) \subset (s |: suppΔ Δ).
Proof.
apply/subsetP=> r; rewrite !inE; case/orP; rewrite !ffunE; case: (r == s) / eqP => //=.
  by move=> _ ->.
by move=> _ ->; rewrite orbT.
Qed.

Lemma suppgd_add s g Δ (hs : s \notin suppg Δ.(deld)) :
  suppg (addΔ s g Δ).(deld) = suppg Δ.(deld).
Proof.
apply/setP=> s'; rewrite !inE !ffunE.
case: ifP => // /eqP->; have <- : set0 = Δ.(deld) s.
  by apply/setP=> y; have := suppgN_mem y hs; rewrite inE; case: (y \in _).
by rewrite set0D.
Qed.

Lemma suppgd_put Δ s g1 (hs : s \notin suppg Δ.(deld)) :
  suppg (putΔ Δ s g1 g0).(deld) = suppg Δ.(deld).
Proof.
apply/setP=> s'; rewrite !inE !ffunE.
case: ifP => //= /eqP->{s'}; have <- : set0 = Δ.(deld) s.
  by apply/setP=> y; have := suppgN_mem y hs; rewrite inE; case: (y \in _).
by rewrite set0D.
Qed.

(* Compute a Δ from two graphs! *)

Lemma neg_wf_DsubF edb Δ s :
  s \notin suppg Δ.(deld) -> Δ.(addd) s \subset (edb :+: Δ) s.
Proof.
move/suppgN_mem=> hN; apply/subsetP=> s'.
by rewrite in_appd hN => ->; rewrite orbT.
Qed.

Lemma neg_wf_BsubF (edb : lrel) Δ s :
  s \notin suppg Δ.(deld) -> edb s \subset (edb :+: Δ) s.
Proof.
by move/suppgN_mem=> hN; apply/subsetP=> s'; rewrite in_appd hN => ->.
Qed.

Definition diffg (G1 G2 : egraph) : egraph * egraph :=
  '(EGraph(G2 :\: G1), EGraph(G1 :\: G2)).

Lemma disjoints_diffg G1 G2 : [disjoint (diffg G1 G2).1 & (diffg G1 G2).2].
Proof.
rewrite disjoints_subset /diffg /= setCD setDE.
have/subset_trans-> // := subsetIl G2 (~:G1).
exact: subsetUr.
Qed.

Lemma diffgP (G G' : egraph) :
  G' = EGraph ((EGraph G :|: (diffg G G').1) :\: (diffg G G').2).
Proof.
case: G G' => G [G']; congr EGraph; apply/setP=> x; rewrite !inE /=.
by case: (x \in G') / boolP; case: (x \in G) / boolP.
Qed.

(*******************************************************************************)
(* Non-incremental closure of graphs, can use Tarjan or any other method.      *)
(*******************************************************************************)
(* Definition starg (g : egraph) : egraph. *)
(* Proof using V. Admitted. *)
(* Lemma stargP g :starg g =2 connect g. *)
(* Admitted. *)

Definition plusg (g : egraph) : egraph.
Proof using V. Admitted.
Lemma plusgP g : plusg g =2 connect_plus g. Admitted.

(*
Definition starg (g : egraph) (Δp : egraph) (Δn : egraph) : egraph.
Proof using V. Admitted.
Lemma stargP (g Δp Δn : egraph) :
  let gu := g :|: Δp :\: Δn in
  starg g Δp Δn =2 connect [rel x y | (x,y) \in gu].
Proof using V. Admitted.

Definition plusg (g : egraph) (Δp : egraph) (Δn : egraph) : egraph.
Proof using V. Admitted.
Lemma plusgP (g Δp Δn : egraph) :
  let gu := g :|: Δp :\: Δn in
  plusg g Δp Δn =2 connect_plus [rel x y | (x,y) \in gu].
Proof using V. Admitted.
*)

(* Equality up to a set of labels *)
Section EqSg.
Implicit Types (G : lrel) (ss : {set Σ}).

Definition eqsg ss G1 G2 := [forall s in ss, G1 s == G2 s].

(* TODO, adjust level *)
Notation "A =[ ss ]= B" := (eqsg ss A B) (at level 54).

(* For rewriting *)
Lemma eqsgP ss G1 G2: reflect {in ss, G1 =1 G2} (G1 =[ss]= G2).
Proof. exact: eqfun_inP. Qed.

(* Theory *)
Lemma eqsg_refl ss G : G =[ss]= G.
Proof. exact/eqsgP. Qed.

(* eqsg is a morphism for subset *)
Lemma eqsg_sub G1 G2 ss1 ss2 :
  ss1 \subset ss2 ->
  G1 =[ss2]= G2 -> G1 =[ss1]= G2.
Proof. by move=> /subsetP hs /eqsgP hss2; apply/eqsgP=> s /hs; apply: hss2. Qed.

Lemma eqsgC G1 G2 ss : G1 =[ss]= G2 = G2 =[ss]= G1.
Proof. by apply/eqsgP/eqsgP=> H x ?; rewrite H. Qed.

Lemma eqsg_ladd G1 G2 ss (s : Σ) g :
  G1 =[ss]= G2 ->
  G1 =[ss :\ s]= addl s g G2.
Proof.
by move/eqsgP=> hs; apply/eqsgP=> r /setD1P[/negbTE hr /hs]->; rewrite !ffunE hr.
Qed.

Lemma eqsg_appd G1 G2 Δ1 Δ2 ss
      (hg : G1 =[ss]= G2)
      (ha : Δ1.(addd) =[ss]= Δ2.(addd))
      (hd : Δ1.(deld) =[ss]= Δ2.(deld)) :
  G1 :+: Δ1 =[ss]= G2 :+: Δ2.
Proof.
apply/eqsgP=> s hs; rewrite !ffunE.
by rewrite (eqsgP _ _ _ hg) ?(eqsgP _ _ _ ha) ?(eqsgP _ _ _ hd).
Qed.

Lemma eqsg_add_mod s ss edb Δ g
      (hs : s \notin ss) :
  let Δ' := addΔ s g Δ in
  edb :+: Δ =[ss]= edb :+: Δ'.
Proof.
apply/eqfun_inP=> r r_in; rewrite !ffunE; suff/negbTE -> : r != s by [].
by case: eqP => // h; rewrite h in r_in; congruence.
Qed.

Lemma eqsg_add_mod2 s ss Δ g
      (hs : s \notin ss) :
  let Δ' := addΔ s g Δ in
  Δ.(addd) =[ss]= Δ'.(addd).
Proof.
apply/eqfun_inP=> r r_in; rewrite !ffunE; suff/negbTE -> : r != s by [].
by case: eqP => // h; rewrite h in r_in; congruence.
Qed.

Lemma eqsg_put_addd_mod2 s ss Δ g g'
      (hs : s \notin ss) :
  let Δ' := putΔ Δ s g g' in
  Δ.(addd) =[ss]= Δ'.(addd).
Proof.
apply/eqfun_inP=> r r_in; rewrite !ffunE; suff/negbTE -> : r != s by [].
by case: eqP => // h; rewrite h in r_in; congruence.
Qed.

Lemma eqsg_del_mod2 s ss Δ g
      (hs : s \notin ss) :
  let Δ' := addΔ s g Δ in
  Δ.(deld) =[ss]= Δ'.(deld).
Proof.
apply/eqfun_inP=> r r_in; rewrite !ffunE; suff/negbTE -> : r != s by [].
by case: eqP => // h; rewrite h in r_in; congruence.
Qed.

Lemma eqsg_put_deld_mod2 s ss Δ g g'
      (hs : s \notin ss) :
  let Δ' := putΔ Δ s g g' in
  Δ.(deld) =[ss]= Δ'.(deld).
Proof.
apply/eqfun_inP=> r r_in; rewrite !ffunE; suff/negbTE -> : r != s by [].
by case: eqP => // h; rewrite h in r_in; congruence.
Qed.

Lemma eqsg_put_mod s ss edb Δ g1 g2
  (hs : s \notin ss) :
  let Δ' := putΔ Δ s g1 g2 in
  edb :+: Δ =[ss]= edb :+: Δ'.
Proof.
apply/eqfun_inP=> r r_in; rewrite !ffunE; suff/negbTE -> : r != s by [].
by case: eqP => // h; rewrite h in r_in; congruence.
Qed.

End EqSg.
End LabeledGraph.

Notation "i1 :||: i2" := (lrelU i1 i2) (at level 52).
Notation "i :+: Δ" := (appd i Δ) (at level 52).
Notation "A =[ ss ]= B" := (eqsg ss A B) (at level 54).
Arguments g0 [V].
Arguments lg0 [V Σ].
Arguments eqsgP [V Σ ss G1 G2].
Arguments set_of_egraph V g : simpl never.
Arguments fun_of_egraph V g : simpl never.
Arguments fun_of_lrel V Σ G : simpl never.
Arguments addl V Σ s g i : simpl never.
Arguments lrelU V Σ i1 i2 : simpl never.

Arguments suppgN [V Σ G s a1 a2].

Arguments grc [n T Σ L] gr c : simpl never.
Arguments bodyM [Σ L T U] f b : simpl never.

(* For the theory with extended "labels/support" *)
Section ExtLabelledGraph.

Variables (T : Type) (V Σ L : finType).
Implicit Types (Δ : edelta V [finType of Σ * L]).

Lemma neg_wf_cons l (b : cbody T Σ L) Δ :
  [disjoint tsymb [::B l & b] & suppg Δ.(deld)] =
  (tsyml l \notin suppg Δ.(deld)) &&
  [disjoint tsymb b & suppg Δ.(deld)].
Proof. by rewrite /tsymb big_cons disjoint_setU disjoint_set1. Qed.
End ExtLabelledGraph.

(* Support-indexed interpretations. *)
(* This is more convenient for our engine purposes, we could always
   do:

Definition sinterp (Σ : finType) := {ffun Σ -> {set V * V}}.

and then create new fintype for each set of support, however this is
quite cumbersome to update algoritmically; so we opt to use a subtype
of lrel.

*)

Section SupportedInt.

Variables (V Σ : finType) (s : {set Σ}).

(* Structure sinterp : Type := *)
(*   SupportedInterp { uI :> lrel V Σ; _ : suppg uI \subset s}. *)

(* Notation "'ℑ s" := (sinterp s) (at level 28). *)

End SupportedInt.

(* Regular Queries: With respect to the regular query definition in
   Reutter, Romero, and Vardi, we are slightly more general as we have
   chosen to extend our literal syntax to support transitive closure
   (tag == true), then, we can just require a strong stratification of
   the program without having to handle the special recursive case.

   [EJGA: I belive this is equivalent but should double check!]

   We also omit the distinguished symbol, and we will indeed take
   (those) in the top of the strata.

*)

Section RegularQueries.

(* Σ = intensional predicate names.
 * Ξ = extensional predicate names.
 *)
Variable (V Σ : finType) (n : nat).

(* Label for literals *)
Inductive L := Single | (* Star | *) Plus.

Definition L_eq x y :=
  match x, y with
  | Single, Single => true
  | Plus, Plus => true
  (* | Star, Star => true *)
  | _, _ => false
  end.

Section L_Eq.

Definition L_rep l : 'I_4 := match l with | Single => inord 0 | (* Star => inord 1 | *) Plus => inord 2 end.
Definition L_pre (n : 'I_4) := match val n with | 0 => Some Single (* | 1 => Some Star *) | 2  => Some Plus | _ => None end.

Lemma L_repK : pcancel L_rep L_pre.
Proof. by case; rewrite  /inord /L_pre val_insubd. Qed.

End L_Eq.

Canonical L_eqType     := Eval hnf in EqType     L (PcanEqMixin     L_repK).
Canonical L_choiceType := Eval hnf in ChoiceType L (PcanChoiceMixin L_repK).
Canonical L_countType  := Eval hnf in CountType  L (PcanCountMixin  L_repK).
Canonical L_finType    := Eval hnf in FinType    L (PcanFinMixin    L_repK).

(* Our set to Predicates is indeed the union *)
(* Definition R := [finType of Σ + Ξ]%type. *)

Definition rq_gatom     := gatom V Σ.
Definition rq_oatom n   := oatom n V Σ.
Definition rq_glit      := glit V Σ L.
Definition rq_olit n    := olit n V Σ L.
Definition rq_gbody     := gbody V Σ L.
Definition rq_obody n   := obody n V Σ L.
(* Generic version *)
Definition rq_Xbody     := Xbody Σ L.
Definition rq_oclause n := oclause  n V Σ L.
Definition rq n         := oprogram n V Σ [finType of L].

Implicit Types (ga : rq_gatom) (gl : rq_glit).

(* Intensional and extensional model *)
(* Variable (G : lrel V Σ). *)
(* XXX: Define mem instance for lrel *)
Section RQSemantics.

(* In this section we define the crucial component of our theorem,
   namely the semantics of queries. Later on, we will prove that our
   engine is correct wrt the below semantics.

   The main theorem informally says:

   "The output of the engine for a query Q over graph G is _sound_"

   Soundness means that the query Q is satisfied by the graph G. As a
   Regular Query is defined as a restrited Datalog program, in this
   case it means that the top-level model computed for the top-level
   clause is satisified. Informally:

Syntax:
───────

   Q  := list of clauses cl₁ ⋯ clₙ
   cl := a(x,y) :- l₁(m₁,n₁), ⋯, lₙ(mₙ,nₙ)
                ∨  h₁(m₁,n₁), ⋯, hₙ(mₙ,nₙ) ... ∨ ...
   l  := a | a- | a+ | a*
   a  ∈ Σ

Semantics:
──────────

   "is_sound(G, [cl1;...;cln]) iff G satisifies all cl_i"

   "satisfies(G, cl ≣ a(x,y) :- C1 ∨ ... ∨ Cn) iff
      ∀ (σ : grounding), if some σ(C_i) is satisfied, then σ(a(x,y)) is satisfied G"

   "csatisfies(G, l1(m1,n1), ...., l_k(m_k,n_k)) = l_i(m_i,n_i) ∈_l G"

   "a (m,n) ∈ₗ G == obvious, a ∈ G"

   "a+(m,n) ∈ₗ G == ??"  "a+(m,n) ∈ₗ G == tconnect m a n"

   "a*(m,n) ∈ₗ G == ??"

We enconde all of the following in Coq.

*)
Variable (G : lrel V [finType of Σ * L]).

(* Satisfaction for literals *)

(* This is the main novelty over the previous datalog semantics, we
   now incorporate a primitive notion of closure in our
   interpreations.

   A key component is the "connect" predicate borrowed from fingraph,
   that in our case, corresponds to the interpretation of the
   Kleene-style closure.

   In order to assign a semantics to the Kleene plus operator, we use
   the standard trick a+ ≡ aa*, written in Coq:
 *)
Definition sTl gl := G '(syml gl, tagl gl) (argl gl).1 (argl gl).2.
Definition sTb b := all sTl (litb b).

(* Another definition would use matching over the intepretation to
   generate the gr [note about safety thou] *)

(* [sTc G cl] = G is a model of clause [cl] *)
Definition sTc n (s : Σ) (c : rq_oclause n) :=
  (* ∀ (g:grounding), let gc be the g-grounded version of c *)
  [forall g : gr n V,
   (* if any of the grounded bodies is satisfied b G, then the
      grounded version of the head, [headc gc] is too *)
      has sTb (map (grb g) (bodyc c)) ==> prod_curry (G '(s,Single)) (grh g (headc c))].

Definition sTp n (p : rq n) := [forall s, sTc s (p s)].

Implicit Types (ss : {set Σ}) (p : rq n).
(* Supported satisfaction:
 * [ssTp G supp p] == true G is a model of p restricted to supp
 *)
Definition ssTp ss p :=
  (* ∀ s ∈ ss, G ⊨ pₛ    -- where pₛ is the clause for sym [s] *)
  [forall s in ss, sTc s (p s)].

End RQSemantics.

Section RQTheory.

(* Theory *)
Implicit Types (ss : {set Σ}) (p : rq n).
Implicit Types (G : lrel V [finType of Σ * L]).

Definition lsubrel G1 G2 :=
  [forall s, G1 s \subset G2 s].

Lemma sTl_sub G1 G2 l :
  G1 '(syml l, tagl l) \subset G2 '(syml l, tagl l) -> sTl G1 l -> sTl G2 l.
Proof. by move/subsetP; apply. Qed.

Lemma sTb_cons G l b : sTb G [::B l & b] = sTl G l && sTb G b.
Proof. by []. Qed.

Lemma sTb_sub G1 G2 b
      (hsub : forall t x, x \in symb b -> G1 '(x,t) \subset G2 '(x,t)) :
  sTb G1 b -> sTb G2 b.
Proof.
move/allP=> hb; apply/allP=> l hl; apply: sTl_sub (hb _ hl).
exact: hsub (syml_in_symb hl).
Qed.

Lemma subset_ssTp G ss1 ss2 p :
  ss2 \subset ss1 -> ssTp G ss1 p -> ssTp G ss2 p.
Proof. exact: sub_forall_inP. Qed.

Lemma ssTp_setU G p ss1 ss2 :
  ssTp G (ss1 :|: ss2) p = ssTp G ss1 p && ssTp G ss2 p.
Proof. exact: eq_forall_setU. Qed.

Lemma ssTp1 G p s : ssTp G [set s] p = sTc G s (p s).
Proof.
apply/forallP/idP=> [/(_ s)| Hc s']; rewrite !inE ?eqxx //=.
by case: eqP => [->|].
Qed.

Lemma in_ssTp G s ss p : s \in ss -> ssTp G ss p -> sTc G s (p s).
Proof. by move=> H /forallP/(_ s); rewrite H. Qed.

End RQTheory.

Section RQModTheory.

Implicit Types (G : lrel V [finType of Σ * L]) (Δ : edelta V [finType of Σ * L]).
Implicit Types (ss : {set Σ * L}) (p : rq n) (c : rq_oclause n).

(* Lemma wf_slice_inE ss p : p \in wf_slice ss = wf_slice ss p. *)
(* Proof. by []. Qed. *)

(* This is not true, as the support can be made disjoint ! *)
(* The definition of modular satisfaction is not correct *)
(* look at ci_wc_decomposition ss si *)

Lemma sat_wf_slice_litP ss G1 G2
      (he : G1 =[ss]= G2) :
  (* This predicate should have a name. *)
  {in [pred l | tsyml l \in ss], sTl G1 =1 sTl G2}.
Proof. by move=> l hl ; rewrite /sTl (eqsgP he). Qed.

Definition wc_sset ss := forall s t, '(s,t) \in ss -> forall t', '(s,t') \in ss.

Lemma wc_ssetP s ss :
  wc_sset ss ->
  wc_sset ([set '(s,Single) ; '(s,Plus)] :|: ss).
Proof.
by move=> H r t; rewrite !inE -orbA; case/or3P=> [/eqP[U K]|/eqP[U K]|U] [];
rewrite ?inE ?U ?K ?(H r t U) ?eqxx ?orbT.
Qed.

(* Down support *)
Definition Ds (supp : {set Σ * L}) := [set x.1 | x in supp].

Lemma DsU s t ss : Ds ('(s,t) |: ss) = s |: Ds ss.
Proof. by rewrite /Ds imsetU imset_set1. Qed.

Lemma DsP ts (supp : {set Σ * L}) : ts \in supp -> ts.1 \in Ds supp.
Proof. by move=> ?; apply/imsetP; exists ts. Qed.

Lemma wc_tsymc c ss (hwc : wc_sset ss) :
  symc c \subset Ds ss -> tsymc c \subset ss.
Proof.
move/subsetP=> H; apply/subsetP=> -[s t] hts.
have H' := tsymc_in_symc hts.
have/imsetP[[s' t'] hin ->] := H s H'.
exact: (hwc _ _ hin).
Qed.

Lemma wf_slice_clP ss G1 G2
      (he : G1 =[ss]= G2)
      (hs : wc_sset ss) :
  let ssu := Ds ss in
  {in wf_slice ssu, @ssTp G1 ssu =1 ssTp G2 ssu}.
Proof.
move=> ssu p hwf.
suff/eq_forall_inb: {in ssu, forall s, sTc G1 s (p s) = sTc G2 s (p s)} by [].
(* First resolve the head condition. *)
move=> s hin.
case/imsetP: (hin) => [[st su]] hin' ?; subst.
apply/eq_forallb=> /= gr; congr (_ ==> _); last first.
  by rewrite (eqsgP he) //; apply: (hs _ _ hin').
apply/eq_in_has=> /= cb hh; apply/eq_in_all=> /= l hl; apply/(sat_wf_slice_litP he).
(* Now we need to use the slice condition! *)
(* TODO Improve this: we shouldn't need to reason about groundings in this way. *)
rewrite inE; apply: (hs _ Single).
case/mapP: hh => /= [ncb hnin heq]; rewrite heq /= in hl.
case/mapP: hl => /= [ncl hlin ->].
rewrite symlM.
have U : ncl \in litc (p st) by apply/flatten_mapP; exists ncb.
have := wf_slice_litP hwf hin U.
by case/imsetP=> [[x1 x2]] /= h1 h3; subst; apply: (hs _ _ h1).
Qed.

Lemma sTa_mod s edb Δ (hΔ : s \notin suppΔ Δ) :
  (edb :+: Δ) s =2 edb s.
Proof. by rewrite suppΔN. Qed.

Lemma sTl_mod l edb Δ (hΔ : tsyml l \notin suppΔ Δ) :
  sTl (edb :+: Δ) l = sTl edb l.
Proof. by rewrite /sTl sTa_mod. Qed.

Lemma sTb_mod b edb Δ (hΔ : [disjoint tsymb b & suppΔ Δ]) :
  sTb (edb :+: Δ) b = sTb edb b.
Proof.
apply/allP/allP=> H l h_in; have hsym := tsyml_in_tsymb h_in;
have ha := disjoint_meml hΔ hsym.
  by rewrite -(sTl_mod _ ha) ?H.
by rewrite sTl_mod ?H.
Qed.

(* This condition will be refined on delta split *)
Lemma sTc_mod s c edb Δ
      (hs : '(s, Single) \notin suppΔ Δ)
      (hΔ : [disjoint tsymc c & suppΔ Δ]) :
  sTc (edb :+: Δ) s c = sTc edb s c.
Proof.
apply: eq_forallb => /= gr.
set has1 := has _ _; set has2 := has _ _.
have ->: has1 = has2.
  rewrite /has1 /has2 !has_map.
  apply/hasP/hasP=> -[b b_in bT]; exists b => //;
  have hd := disjoint_tsymc_tsymb b_in hΔ.
    by rewrite /= sTb_mod // tsymbM in bT.
  by rewrite /= sTb_mod // tsymbM.
by congr implb; rewrite sTa_mod.
Qed.

Lemma ssTp_mod p s (supp : {set Σ * L}) edb Δ g
  (hs : wc_sset supp)
  (hwf : p \in wf_slice (Ds supp))
  (hi : '(s, Single) \notin supp) :
  let Δ' := addΔ '(s, Single) g Δ in
  ssTp (edb :+: Δ') (s |: Ds supp) p =
  sTc (edb :+: Δ') s (p s) && ssTp (edb :+: Δ) (Ds supp) p.
Proof.
have hE := eqsg_add_mod edb Δ g hi.
by rewrite /= ssTp_setU (wf_slice_clP hE) // /ssTp eq_forall_set1.
Qed.

Lemma ssTp_mod_put p s t (supp : {set Σ * L}) edb Δ g1 g2
  (hs : wc_sset supp)
  (hwf : p \in wf_slice (Ds supp))
  (hi : '(s, t) \notin supp) :
  let Δ' := putΔ Δ '(s, t) g1 g2 in
  ssTp (edb :+: Δ') (s |: Ds supp) p =
  sTc (edb :+: Δ') s (p s) && ssTp (edb :+: Δ) (Ds supp) p.
Proof.
have hE := eqsg_put_mod edb Δ g1 g2 hi.
by rewrite /= ssTp_setU (wf_slice_clP hE) // /ssTp eq_forall_set1.
Qed.

End RQModTheory.

Section RQStrata.

(* We operate over a list of symbols, however it would be more
   convenient to have an indexed form for our programs. *)

(* Direct dependencies of a symbol as a finite function *)
Variables (p : rq n).

Definition strata := seq Σ.

Fixpoint is_strata_rec (todo : strata) done :=
  match todo with
  | [::]         => true
  | [:: s & str] => [&& is_strata_rec str (s |: done)
                     , s \notin done
                     & symc (p s) \subset done
                     ]
  end.

Definition is_strata str := is_strata_rec str set0.

(* Support of strata *)
Definition suppstr {S : finType} (str : seq S) : {set S} := [set x in str].

Lemma suppstrU {S : finType} se1 se2 : @suppstr S (se1 ++ se2) = suppstr se1 :|: suppstr se2.
Proof. by apply/setP=> x; rewrite !inE mem_cat. Qed.

Lemma suppstr_cons {S : finType} e e1 : @suppstr S (e :: e1) = e |: suppstr e1.
Proof. by apply/setP=> x; rewrite !inE. Qed.

End RQStrata.

Section Matching.

Notation sub  := (@sub n V).
Notation ssub := (@ssub n V).
Implicit Types (t : term n V) (a : rq_oatom n) (l : rq_olit n).
Implicit Types (s : sub) (ss : ssub) (v : 'I_n) (b : 'I_n * V).

Section NoDepGrounding.

(** Non-dependent grounding using default element *)
Variable def : V.

(** grounding a term [t] with a substitution [s] and the default element [def] *)
Definition gr_term_def s t : V :=
  match t with
  | Val c => c
  | Var i => odflt def (s i)
  end.

Definition gr_args_def s (args :  _) : V * V :=
  '(gr_term_def s args.1, gr_term_def s args.2).

Definition gr_atom_def s a :=
  atomM (gr_term_def s) a.

Definition gr_atoms_def s la :=
  map (gr_atom_def s) la.

Definition gr_to_sub (g : gr n V) : sub := [ffun x  => Some (g x)].

(* XXX Move and clean up. *)
Lemma in_dom_grt gr s t (hs : s \sub gr_to_sub gr) :
  vart t \subset dom s ->
  grt gr t = gr_term_def s t.
Proof.
case: t => [v|c] //=; rewrite sub1set; case/domP=> c hv; rewrite hv.
move/substP/(_ '(v,c)): hs; rewrite !inE hv ffunE eqxx (inj_eq (@Some_inj _)) /=.
by move=> /(_ erefl) /eqP.
Qed.

End NoDepGrounding.

Section BaseMatching.

(** matching a term [t] against a constant [d], starting from an
    initial substitution [s]. *)
Definition match_term d t s : option sub :=
  match t with
  | Val e => if d == e then Some s else None
  | Var v => if s v is Some e then
             (if d == e then Some s else None)
             else Some (add s v d)
  end.

Lemma match_term_complete d t s s' :
 s' \sub s -> subt s t = Val _ d ->
 exists r : sub, match_term d t s' = Some r /\ r \sub s.
Proof.
case: t => [v|c] //= Hsub; last first.
  by case=> ->; exists s'; split; rewrite /= ?eqxx.
case Hs : (s  _) => [e |] //; case=> He //; rewrite -He {d He}.
case Hs': (s' _) => [e'|] //; last first.
  by exists (add s' v e); split=> //; apply/sub_st_add.
by exists s'; case: eqP => // He; move/substE/(_ _ _ Hs'): Hsub; congruence.
Qed.

(* Egde matching *)
Definition match_atom (v : V * V) (t : term n V * term n V) s : option sub :=
  foldl (fun acc p => obind (match_term p.1 p.2) acc)
        (Some s) (zip [:: v.1; v.2] [:: t.1; t.2]).

Lemma match_atom_complete (v : V * V) (t : term n V * term n V) s s' :
 s' \sub s ->
 subt s t.1 = Val _ v.1 ->
 subt s t.2 = Val _ v.2 ->
 exists2 r : sub, match_atom v t s' = Some r & r \sub s.
Proof.
case: t v => [a1 a2] [v1 v2] hs ht1 ht2.
have [r0 [hm1 hm2]] := match_term_complete hs ht1.
have [r1 [hn1 hn2]] := match_term_complete hm2 ht2.
by exists r1; rewrite // /match_atom/obind /oapp /= hm1 hn1.
Qed.

Definition match_atom_all (i : egraph V) (t : term n V * term n V) s :=
  [set x | Some x \in [set match_atom ga t s | ga in i]].

Lemma match_atomsP t1 t2 (i : egraph V) r s :
  reflect (exists2 ga, ga \in i & Some r = match_atom ga '(t1, t2) s)
          (r \in match_atom_all i '(t1, t2) s).
Proof. by rewrite inE; exact: (iffP imsetP). Qed.

Implicit Types (i : lrel V [finType of Σ * L]).

Definition match_lit_all i l s : ssub :=
  let slice := i '(syml l, tagl l) in
  match_atom_all slice (argl l) s.

Lemma match_litsP l i r s :
  reflect (exists3 gl, Some r = match_atom (argl gl) (argl l) s &
                       tagl l = tagl gl /\ syml l = syml gl &
                       sTl i gl)
          (r \in match_lit_all i l s).
Proof.
(* Discrepancy here... *)
rewrite inE; apply/(iffP imsetP)=> [[[v1 v2] ht heqt]|[gl hgeq [-> ->] hst]].
  exists {|tagl:=tagl l;atoml:={|syma:=syml l;arga:='(v1,v2)|}|} => //.
by exists (argl gl) => //; move: hst; rewrite egraphE.
Qed.

(** matching a list of atoms [tl] agains ground atoms of an
    interpretation [i] *)
Definition match_body i (tl : rq_obody n) ss0 : ssub :=
  foldS (match_lit_all i) ss0 (litb tl).

Lemma to_subE t gr : subt (gr_to_sub gr) t = Val _ (grt gr t).
Proof. by case: t => [i|d] //=; rewrite ffunE. Qed.

Lemma to_gr_atomP a gr ga :
  suba (gr_to_sub gr) a = lifta ga <-> gra gr a = ga.
Proof.
split; last by move<-; congr Atom; rewrite !to_subE.
case; rewrite !to_subE => ? [h1] [h2]; congr Atom => //.
(* We are missing eta for pairs sadly... *)
by case: (arga a) (arga ga) h1 h2 => [? ?] [? ?] -> ->.
Qed.

Lemma to_gr_litP l gr gl :
  subl (gr_to_sub gr) l = liftl gl <-> grl gr l = gl.
Proof.
split.
  case; rewrite !to_subE => ? ? [?] [?]; congr (Lit _ (Atom _ _)) => //.
  by congr '(_,_).
by move<-; congr (Lit _ (Atom _ _)); rewrite !to_subE.
Qed.

Lemma match_body_cons l lb i r ss0 :
  reflect
    (exists2 s : sub,
         s \in ss0 &
         r \in match_body i (CBody lb) (match_lit_all i l s))
    (r \in match_body i (CBody (l :: lb)) ss0).
Proof. exact: bindP. Qed.

(* General repair lemma *)
Lemma match_body_complete s ss0 i (b : rq_obody n) gr :
 s \in ss0 ->
 s \sub gr_to_sub gr ->
 sTb i (grb gr b) ->
 exists2 r : sub, r \in match_body i b ss0 &
                  r \sub gr_to_sub gr.
Proof.
elim/cbody_ind: b s ss0 => [|hd tl IHl] s ss0 Hs H_sub H_mem.
  by exists s; [exact: Hs | exact: H_sub].
rewrite grb_cons sTb_cons in H_mem.
case/andP: H_mem => [H_in H_mem].
(* have/to_gr_litP[eq_v1 eq_v2] := @erefl _ (grl gr hd). *)
have [gl Hga_in]: exists2 gl, sTl i gl & grl gr hd = gl by exists (grl gr hd).
case/to_gr_litP=> eq_tag eq_sym eq_v1 eq_v2.
have [r' Hr' Hr'_sub] := match_atom_complete _ H_sub eq_v1 eq_v2.
have Hr'_all: r' \in match_lit_all i hd s.
  by apply/match_litsP; exists gl; rewrite ?eq_tag ?eq_sym ?eqxx.
have [r Hr Hr_sub] := IHl r' _ Hr'_all Hr'_sub H_mem.
by exists r => //; apply/match_body_cons; exists s.
Qed.

Lemma match_term_sub s1 s2 (x : V) (t : term n V) :
  Some s2 = match_term x t s1 -> s1 \sub s2.
Proof.
case: t => [v|c] /=; last by case: eqP => // _ [->]; apply: lesubss.
case: subP => [y|]; last by move => ? [->]; rewrite sub_add.
by case: eqP => // <- _ [<-]; apply: lesubss.
Qed.

Lemma sterm_sub t s1 s2 d :
  s1 \sub s2 -> subt s1 t = Val n d -> subt s2 t = Val n d.
Proof.
by case: t => //= v /substE H; case E: (s1 v) => [a1|//]; move/H: E ->.
Qed.

Lemma match_term_sound d t s r :
  Some r = match_term d t s -> subt r t = Val n d.
Proof.
case: t => /= [v|c]; last by case: eqP => [->|].
case: subP => [e|] hin; last by case => ->; rewrite ffunE eqxx.
by case: eqP => // -> [->]; rewrite (eqP hin).
Qed.

(** List Fold Soundness *)
Lemma foldl_0_gen {A} u (l : seq A) r
     (f : A -> sub -> option sub)
     (f_pmon : forall x s r, Some r = f x s -> s \sub r)
 : foldl (fun acc p => obind (f p) acc) u l = Some r ->
   exists2 s, Some s = u & s \sub r.
Proof.
elim: l u => [|hd tl IHl] //= => [Hu | u Hfold].
  by exists r; [done | apply/lesubss].
case: (IHl (obind (f hd) u) Hfold) => [s Hbind Hsub].
case E: u => [s'|]; rewrite E //= in Hbind.
by exists s'; [done | apply/(lesub_trans Hsub (@f_pmon hd s' s Hbind))].
Qed.

Lemma foldl_0 gar ar u r :
 foldl (fun acc p => obind [eta match_term p.1 p.2] acc) u (zip gar ar) = Some r ->
 exists2 s, Some s = u & s \sub r.
Proof. by apply: foldl_0_gen => x s r0; apply: match_term_sub. Qed.

Lemma match_atom_sub s1 s2 (v : V * V) (t : term n V * term n V) :
  Some s2 = match_atom v t s1 -> s1 \sub s2.
Proof.
rewrite /match_atom /=.
case M1: match_term => [r1|] //=; case M2: match_term => [r2|] // [->] {s2}.
have le1 := match_term_sub (esym M1).
have le2 := match_term_sub (esym M2).
exact: lesub_trans le1.
Qed.

Lemma match_atom_all_sub i (cb : rq_obody n) r ss0 :
  r \in match_body i cb ss0 -> exists2 s, s \in ss0 & s \sub r.
Proof.
case: cb=> cbl; elim: cbl ss0 => [| a l IHl] ss0.
  by move=> H; exists r; [exact: H | exact: lesubss].
case/bindP => [s Hs Hr]; exists s=> //.
have [s' /match_atomsP [ga Hga HH] Hs'] := IHl _ Hr.
exact: lesub_trans (match_atom_sub HH).
Qed.

Lemma match_atom_sound s r (v : V * V) (t : term n V * term n V) :
  Some r = match_atom v t s ->
  subt r t.1 = Val n v.1 /\ subt r t.2 = Val n v.2.
Proof.
rewrite /match_atom /=.
case M1: match_term => [r1|] //= ; case M2: match_term => [r2|] // [->].
have Hm := match_term_sub (esym M2).
have H1 := match_term_sound (esym M1).
have H2 := match_term_sound (esym M2).
by split; [exact: sterm_sub Hm H1 | exact: H2].
Qed.

Lemma match_body_sound i (cb : rq_obody n) r ss0 :
  r \in match_body i cb ss0 ->
  exists2 gcb : rq_gbody, subb r cb = liftb gcb & sTb i gcb.
Proof.
elim/cbody_ind: cb ss0 => [|a l IHl] ss0; first by exists [::B].
case/match_body_cons=> [s0 Hs0 Hrs].
have {IHl} [gtl [H_tl H_mem]] := IHl _ Hrs.
have {Hrs} [s Hs Hsub] := match_atom_all_sub Hrs.
have/match_litsP {Hs} [ga hgas [eq_tag eq_sym] hSt] := Hs.
case/match_atom_sound: hgas => [/sterm_sub H1 /sterm_sub H2].
exists [::B ga & gtl]; last by rewrite /sTb /= hSt.
by congr (CBody (Lit _ _::_)); rewrite // eq_sym H1 ?H2.
Qed.

End BaseMatching.
End Matching.

Notation "A \sub B" := (le_sub A B)
  (at level 70, no associativity) : bool_scope.

(* We develop an incremental engine based on the one in Dumbrava16,
   but with significant restrictions that make the engine more
   efficient and apt to evaluate regular queries. *)
Section RQEngine.

Notation sub  := (@sub n V).
Notation ssub := (@ssub n V).

Variables (def : V).
Implicit Types (s : Σ).
Implicit Types (supp done : {set Σ * L}).
Implicit Types (t : term n V).
Implicit Types (sub : sub).
Implicit Types (ss : ssub).
Implicit Types (b  : rq_obody n).
Implicit Types (d  : seq (rq_obody n)).
Implicit Types (gd : seq rq_gbody).
Implicit Types (c  : rq_oclause n).
Implicit Types (p  : rq n).
Implicit Types (edb: lrel V [finType of Σ * L]).
Implicit Types (Δ  : edelta V [finType of Σ * L]).

Section DeltaSelection.

(* Masks *)
Inductive M := B | D | F. (* Base | Delta | Full *)

(* It is very convenient for our equality to reduce *)
Definition M_rep' (m : M) : nat :=
  match m with | B => 0 | D => 1 | F => 2 end.

Definition M_con' (r : nat) : option M :=
  match r with | 0 => Some B | 1 => Some D | 2 => Some F | _ => None end.

(** cancelation lemma for terms *)
Lemma M_repK' : pcancel M_rep' M_con'.
Proof. by do! case. Qed.

Definition M_rep (m : M) : 'I_3 :=
  match m with | B => inord 0 | D => inord 1 | F => inord 2 end.

Definition M_con (r : 'I_3) : option M :=
  match val r with | 0 => Some B | 1 => Some D | 2 => Some F | _ => None end.

(** cancelation lemma for terms *)
Lemma M_repK : pcancel M_rep M_con.
Proof. by case; rewrite /M_con val_insubd. Qed.

(** canonical instances for terms *)
Canonical M_eqType     := Eval hnf in EqType     M (PcanEqMixin     M_repK').
Canonical M_choiceType := Eval hnf in ChoiceType M (PcanChoiceMixin M_repK).
Canonical M_countType  := Eval hnf in CountType  M (PcanCountMixin  M_repK).
Canonical M_finType    := Eval hnf in FinType    M (PcanFinMixin    M_repK).

(* Necessary for delta selection *)
Definition mselect m (i iΔ : egraph V) :=
  match m with
  | B => i
  | D => iΔ
  | F => EGraph (i :|: iΔ)
  end.

Definition dselect m edb Δ :=
  match m with
  | B => edb
  | D => addd Δ
  | F => edb :+: Δ
  end.

Variables X S : Type.
Implicit Types (tg : L).
Implicit Types (m : M).
Implicit Types (l : lit X S L).
Implicit Types (Δl : lit X S (L*M)).
Implicit Types (Δb : cbody X S (L*M)).

(* "Diff" tag for a literal *)
Definition model Δl := (tagl Δl).1.
Definition diffl Δl := (tagl Δl).2.

Definition maskl m l := litT  (fun tg => '(tg,m)) l.
Definition umaskl Δl := litT (@fst _ _) Δl.

Lemma masklK m : cancel (maskl m) umaskl.
Proof. by []. Qed.

Lemma umasklK m Δl : m = diffl Δl -> maskl m (umaskl Δl) = Δl.
Proof. by move->. Qed.

Definition maskb m xb := @bodyT S _ X _ (fun tg => '(tg,m)) xb.
Definition umaskb Δb := bodyT (@fst _ _) Δb.

Lemma maskbK m : cancel (maskb m) umaskb.
Proof. by move=> x; rewrite /umaskb /bodyT -map_comp //= map_id. Qed.

Lemma umaskb_cons Δl Δb :
  umaskb [::B Δl & Δb] = [::B umaskl Δl & umaskb Δb].
Proof. by []. Qed.

(* This is the key definition for delta matching: we generate a
   factoring such that for any

    b = [X, ...,X], ∃ m ⊆ (gen_mask ∪ [B,...,B]), ⟦b⟧ ⊆ ∪_m ⟦m⟧


   We do a simple diagonal factoring, which may not be the best
   but should work for now.

   [B, B, B] ∪
   -----------
   [D, F, F] ∪
   [B, D, F] ∪
   [B, B, D] = [F, F, F]

*)

(* Unfortunately the termination checker cannot see throu litb *)
Fixpoint body_mask ll : seq (cbody X S (L * M)) :=
  match ll with
  | [::]   =>
    [:: [::B]]
  (* We special case the last to avoid the base case *)
  | [:: l] =>
    [:: [::B maskl D l]]
  | [:: l & ll] =>
    [:: [::B maskl D l & maskb F {| litb := ll |}] &
        map (fun r => [::B maskl B l & r]) (body_mask ll)]
  end.

Lemma body_mask_cons l l' xb :
  body_mask [::B l, l' & xb] =
  [::      [::B maskl D l & maskb F [::B l' & xb]]
    & [seq [::B maskl B l & b'] | b' <- body_mask [:: l' & xb ] ] ].
Proof. by []. Qed.

End DeltaSelection.

Section DeltaBaseTheory.

Variables (X S : Type).

Lemma gr_body_mask gr (xb : obody n X S _) :
  body_mask (litb (grb gr xb)) = map (grb gr) (body_mask (litb xb)).
elim/cbody_rect: xb => //= l b ihb.
case: b / cbodyP ihb => // l' b' ihb.
rewrite !map_cons; congr cons => //.
  by rewrite !bconsE grb_cons; congr bcons; exact/esym/bodyM_bodyT.
by rewrite ihb -!map_comp.
Qed.

End DeltaBaseTheory.

Section DeltaEqTheory.

Variables X S : eqType.
Implicit Types (m : M).
Implicit Types (l : lit X S L).
Implicit Types (Δl : lit X S (L*M)).
Implicit Types (Δb : cbody X S (L*M)).

Lemma mem_body_mask_cons lΔ l xb:
  lΔ \in body_mask [::B l & xb] ->
  lΔ = [::B maskl D l & maskb F xb] \/
  lΔ \in [seq [::B maskl B l & b'] | b' <- body_mask xb].
Proof.
case: xb => [[//|l' ll]]; first by rewrite ?inE; move/eqP->; left.
by rewrite !bconsE body_mask_cons !inE; apply/predU1P.
Qed.

Lemma body_maskP Δl Δb (b : cbody X S L) :
  Δb \in body_mask b -> Δl \in litb Δb -> umaskl Δl \in litb b.
Proof.
elim/cbody_rect: b Δb => [|l b ihb] Δb; rewrite !inE; first by move/eqP->.
case/mem_body_mask_cons=>[->|].
  rewrite in_cons; case/predU1P=> [->|]; first by rewrite eqxx.
  by case/mapP=> l' hl' ->; rewrite hl' orbT.
case/mapP=> Δb' hΔb'_in ->{Δb}; rewrite inE.
case/predU1P=> [->|H]; first by rewrite masklK eqxx.
by rewrite (ihb _ _ H) // orbT.
Qed.

Lemma mem_body_mask Δb xb :
  Δb \in body_mask (litb xb) -> umaskb Δb = xb.
Proof.
elim/cbody_rect: xb Δb => [|l b ihb] Δb; first by rewrite inE => /eqP->.
case/mem_body_mask_cons=> [->|].
  by rewrite umaskb_cons masklK maskbK.
by case/mapP=> cb /ihb he ->; rewrite umaskb_cons he.
Qed.

End DeltaEqTheory.

Section DeltaFinTheory.

Variables (X : eqType) (S : finType).
Implicit Types (m : M).
Implicit Types (l : lit X S L).
Implicit Types (xb  : cbody X S L).
Implicit Types (Δl : lit X S (L*M)).
Implicit Types (Δb : cbody X S (L*M)).

Lemma tsymb_body_mask Δb xb :
  Δb \in body_mask xb -> tsymb (umaskb Δb) = tsymb xb.
Proof. by move=> H; have -> := mem_body_mask H. Qed.

End DeltaFinTheory.

Section DeltaSemantics.

Definition sTlΔ edb Δ lΔ := sTl (dselect (diffl lΔ) edb Δ) (umaskl lΔ).

Lemma sat_wf_slice_litΔP (ss : {set Σ * L}) edb Δ1 Δ2
      (hΔa : Δ1.(addd) =[ss]= Δ2.(addd))
      (hΔd : Δ1.(deld) =[ss]= Δ2.(deld)) :
  (* This predicate should have a name. *)
  {in [pred lΔ | tsyml (umaskl lΔ) \in ss], sTlΔ edb Δ1 =1 sTlΔ edb Δ2}.
Proof.
move=> l hl; rewrite /sTlΔ.
have hs: dselect (diffl l) edb Δ1 =[ss]= dselect (diffl l) edb Δ2.
  by rewrite /dselect; case: (diffl l); rewrite ?eqsg_appd ?eqsg_refl.
by apply: (sat_wf_slice_litP hs).
Qed.

Definition sTbΔ G Δ bΔ := all (sTlΔ G Δ) (litb bΔ).

Lemma sTbΔ_cons G Δ l xb :
  sTbΔ G Δ [::B l & xb] = sTlΔ G Δ l && sTbΔ G Δ xb.
Proof. by []. Qed.

Lemma sTbF edb Δ cb :
  sTb  (edb :+: Δ) cb = sTbΔ edb Δ (maskb F cb).
Proof. by elim/cbody_rect: cb => // l cb ihb; rewrite sTb_cons ihb. Qed.

Lemma sTbΔP edb Δ gb Δb
      (hdΔ : [disjoint tsymb gb & suppg Δ.(deld)])
      (gb_mask : Δb \in body_mask gb)
      (TΔb : sTbΔ edb Δ Δb)
  : sTb (edb :+: Δ) gb.
Proof.
elim/cbody_rect: gb hdΔ Δb gb_mask TΔb => // l b ihb.
rewrite neg_wf_cons; case/andP=> hdΔl hdΔ Δb.
case/mem_body_mask_cons=> [->|].
  rewrite sTb_cons sTbΔ_cons /sTlΔ -sTbF /= masklK => /andP[sTbD sTbF].
  by rewrite (sTl_sub _ sTbD) ?(sTb_sub _ sTbF) ?neg_wf_DsubF.
case/mapP=> /= gbΔ hb1 ->{Δb}; rewrite sTb_cons sTbΔ_cons.
case/andP=> hl /ihb{ihb} -> //; rewrite andbT.
by apply: sTl_sub hl; rewrite neg_wf_BsubF.
Qed.

End DeltaSemantics.

Section DeltaMatching.

Implicit Types (mask : seq M).
Implicit Types (ld: olit  n V Σ (L * M)).
Implicit Types (bd: obody n V Σ (L * M)).
Implicit Types (i iΔ : egraph V).

(* Match_atom_all with delta *)
Definition match_delta_atoms (i iΔ : egraph V) a sub m : ssub :=
  let bm :=
      if [|| m == B | m == F]
      then [set x | Some x \in [set match_atom ga a sub | ga in i]]
      else set0
  in let dm :=
      if [|| m == D | m == F]
      then [set x | Some x \in [set match_atom ga a sub | ga in iΔ]]
      else set0
  in bm :|: dm.

Lemma match_delta_atomsP (t : term n V * term n V) (i iΔ : egraph V) (r s : sub) m :
   reflect
     (exists2 ga,
        ga \in mselect m i iΔ & Some r = match_atom ga t s)
     (r \in match_delta_atoms i iΔ t s m).
Proof.
case: m; rewrite /match_delta_atoms !eqxx !inE /= ?orbF; try exact/imsetP.
set s1 := imset _ _; set s2 := imset _ _.
have -> : (Some r \in s1) || (Some r \in s2) = (Some r \in (s1 :|: s2)).
  by rewrite inE.
by rewrite -imsetU; apply/imsetP.
Qed.

Definition match_delta_lit_all edb Δ ld sub :=
  let slice_s := '(syml ld, (model ld)) in
  let (s_edb, s_Δ) := '(edb slice_s, Δ.(addd) slice_s) in
  match_delta_atoms s_edb s_Δ (argl ld) sub (diffl ld).

(* This only works for positive deltas. *)
Lemma match_delta_litsP Δl edb Δ (r s : sub)
      (hΔ : tsyml (umaskl Δl) \notin suppg (deld Δ)) :
  reflect
    (exists2 garg : V * V,
      Some r = match_atom garg (argl Δl) s &
      sTlΔ edb Δ {| tagl := tagl Δl; atoml := {| syma := syml Δl; arga := garg |} |})
    (r \in match_delta_lit_all edb Δ Δl s).
Proof.
by apply: (iffP (match_delta_atomsP _ _ _ _ _ _)); case=> hd;
   case: Δl hΔ; case=> lt; case=> la hΔ //= h1 h2; exists hd => //=;
   move: h1 h2; rewrite /sTlΔ /sTl ?lrelE //;
   rewrite ?in_appd ?inE // ?(suppgN_mem hd hΔ) ?andbT.
Qed.

Definition match_delta_body edb Δ bd ss0 : ssub :=
  foldS (match_delta_lit_all edb Δ) ss0 (litb bd).

Lemma match_delta_body_cons l xb edb Δ r ss0 :
  reflect
    (exists2 s : sub,
         s \in ss0 &
         r \in match_delta_body edb Δ xb (match_delta_lit_all edb Δ l s))
    (r \in match_delta_body edb Δ [::B l & xb] ss0).
Proof. exact: bindP. Qed.

Lemma match_delta_body_complete (s : sub) (ss0 : ssub) edb Δ bd (gr : gr n V) :
   s \in ss0 ->
   s \sub (gr_to_sub gr) ->
   [disjoint tsymb (umaskb bd) & suppg Δ.(deld)] ->
   sTbΔ edb Δ (grb gr bd) ->
   exists2 r : sub,
     r \in match_delta_body edb Δ bd ss0 &
     r \sub (gr_to_sub gr).
Proof.
elim/cbody_rect: bd s ss0 => //= [|l bd ihbd] s ss0 hs hsub; first by exists s.
rewrite umaskb_cons neg_wf_cons grb_cons sTbΔ_cons => /andP[Dl DΔ] /andP[hl hb].
have [gl Hga_in]: exists2 gl, sTlΔ edb Δ gl & grl gr l = gl by exists (grl gr l).
move=> Hu.
have: grl gr (umaskl l) = (umaskl gl).
  by rewrite -Hu; case: l {hl Hu Dl DΔ} => -[l1 l2] a.
case/to_gr_litP=> eq_tag eq_sym eq_v1 eq_v2.
have [r' Hr' Hr'_sub] := match_atom_complete _ hsub eq_v1 eq_v2.
have Hr'_all: r' \in match_delta_lit_all edb Δ l s.
  apply/match_delta_litsP=> //.
  exists (argl gl); rewrite ?Hr' //.
  suff [-> ->]: tagl l = tagl gl /\ syml l = syml gl by [].
  by rewrite -Hu.
have [r Hr Hr_sub] := ihbd r' _ Hr'_all Hr'_sub DΔ hb.
by exists r => //; apply/match_delta_body_cons; exists s.
Qed.

(* The lemma here says that for "model" it is good. *)
Definition fwd_delta_body edb Δ b : ssub :=
  \bigcup_(bΔ <- body_mask b) match_delta_body edb Δ bΔ [set sub0].

Lemma fwd_delta_body_complete
      (s : sub) (ss0 : ssub) edb Δ
      (b : rq_obody n) Δb (gr : gr n V)
      (hdΔ : [disjoint tsymb b & suppg Δ.(deld)]) :
  s \in ss0 ->
  s \sub gr_to_sub gr ->
  Δb \in body_mask (grb gr b) ->
  sTbΔ edb Δ Δb ->
  exists2 r : sub,
     r \in fwd_delta_body edb Δ b
   & r \sub gr_to_sub gr.
Proof.
move=> hs hsub hmb hT.
have [oΔb heq hmm] : exists2 oΔb, grb gr oΔb = Δb & oΔb \in body_mask b.
  by move: hmb; rewrite gr_body_mask; case/mapP=> [oΔb hob ->]; exists oΔb.
have Uu: sTbΔ edb Δ (grb gr oΔb) by rewrite heq.
have UU: [disjoint tsymb (umaskb oΔb) & suppg (deld Δ)].
  by rewrite (tsymb_body_mask hmm).
have h0: @sub0 n V \in [set sub0] by rewrite inE.
have hs0 := lesub0s (gr_to_sub gr).
have [r rin rsub] := match_delta_body_complete h0 hs0 UU Uu.
by exists r => //; apply/bigcup_seqP; exists oΔb => //; rewrite rin.
Qed.

Lemma match_delta_atom_sub edb Δ cb r ss0 :
  r \in match_delta_body edb Δ cb ss0 ->
  exists2 s, s \in ss0 & s \sub r.
Proof.
elim/cbody_rect: cb ss0 => [|l b IHb] ss0.
  by move=> H; exists r; [exact: H | exact: lesubss].
case/bindP => [s Hs Hr]; exists s=> //.
have [s' /match_delta_atomsP [ga Hga HH] Hs'] := IHb _ Hr.
exact: lesub_trans (match_atom_sub HH).
Qed.

Lemma match_delta_body_sound edb Δ cb r ss0 :
  [disjoint tsymb (umaskb cb) & suppg Δ.(deld)] ->
  r \in match_delta_body edb Δ cb ss0 ->
  exists2 gcb, subb r cb = liftb gcb & sTbΔ edb Δ gcb.
Proof.
elim/cbody_rect: cb ss0 => [| l b IHl] ss0; first by exists [::B].
rewrite umaskb_cons neg_wf_cons => /andP[hΔl hΔb].
case/match_delta_body_cons=> [s0 Hs0 Hrs].
have {IHl} [gtl [H_tl H_mem]] := IHl _ hΔb Hrs.
have {Hrs} [s Hs Hsub] := match_delta_atom_sub Hrs.
have/(match_delta_litsP _ _ _ hΔl) [ga hgas hTl] := Hs.
case/match_atom_sound: hgas => [/sterm_sub H1 /sterm_sub H2].
set kl := {| tagl := _; atoml := _ |} in hTl.
exists [::B kl & gtl]; last by rewrite sTbΔ_cons hTl.
by congr (CBody (Lit _ _ :: _)); rewrite // H1 ?H2.
Qed.

(* Weaker version as to finish the proof. Look into this. *)
Lemma fwd_delta_body_sound edb Δ (cb : rq_obody n) r ss0
      (hΔ : [disjoint tsymb cb & suppg Δ.(deld)]) :
  r \in fwd_delta_body edb Δ cb ->
  exists gcb : rq_gbody, subb r cb = liftb gcb.
  (* exists2 gcb : rq_gbody, subb r cb = liftb gcb & sTb (edb :+: Δ) gcb. *)
Proof.
case/bigcup_seqP=> [bΔ bin /andP[hs _]].
have hΔ': [disjoint tsymb (umaskb bΔ) & suppg (deld Δ)].
  by rewrite (tsymb_body_mask bin).
have [gΔb hEg hTg] := match_delta_body_sound hΔ' hs.
exists (umaskb gΔb).
rewrite (_ : liftb (umaskb gΔb) = subb r (umaskb bΔ)).
  by rewrite (mem_body_mask bin).
by move: hEg; rewrite /liftb /subb !bodyM_bodyT => <-.
Qed.

Definition fwd_delta_dbody edb Δ d : ssub :=
  \bigcup_(d <- d) fwd_delta_body edb Δ d.

Definition fwd_or_clause_delta edb Δ s arg body :=
  putΔ Δ '(s, Single)
       (EGraph [set gr_args_def def s arg
               | s in fwd_delta_dbody edb Δ body ]) g0.

Lemma sTl_maskP edb Δ gl
      (hΔ : tsyml gl \notin suppg Δ.(deld)) :
  sTl (edb :+: Δ) gl ->
  sTlΔ edb Δ (maskl D gl) \/
  sTlΔ edb Δ (maskl B gl).
Proof.
by rewrite /sTl lrelE in_appd (suppgN_mem _ hΔ) andbT; case/orP; [right|left].
Qed.

(* The main [super] technical lemma about the factorization, culmen of
   the development: *)
Lemma sTb_maskP edb Δ gb :
  [disjoint tsymb gb  & suppg Δ.(deld)] ->
  sTb (edb :+: Δ) gb ->
  (exists2 Δb, Δb \in body_mask gb & sTbΔ edb Δ Δb) \/
  sTb edb gb.
Proof.
elim/cbody_rect: gb => [|l b ihb] //; first by right.
rewrite neg_wf_cons sTb_cons => /andP[hΔl hΔb] /andP[hTl hTb].
case/cbodyP: b ihb hΔb hTb => [|l' b'] ihb hΔb hTb.
- rewrite sTb_cons andbT.
  have [hDl|hBl]:= sTl_maskP hΔl hTl; last by right.
  by left; exists [::B maskl D l]; rewrite ?inE // sTbΔ_cons hDl.
rewrite body_mask_cons.
have [[Δbt Δbt_in hTΔ]|hTB] := ihb hΔb hTb.
(* recursive call *)
+ have [hDl|hBl]:= sTl_maskP hΔl hTl.
  * left; exists [::B maskl D l & maskb F (bcons l' b')].
      by rewrite inE eqxx.
    by rewrite sTbΔ_cons hDl -sTbF hTb.
  left; exists [::B maskl B l & Δbt].
    by rewrite !inE; apply/orP; right; apply/mapP; exists Δbt.
  by rewrite sTbΔ_cons hBl hTΔ.
have [hDl|hBl]:= sTl_maskP hΔl hTl.
  left; exists [::B maskl D l & maskb F (bcons l' b')].
    by rewrite inE eqxx.
  by rewrite sTbΔ_cons hDl -sTbF hTb.
rewrite /sTlΔ /= masklK in hBl.
by right; rewrite sTb_cons hBl hTB.
Qed.
(* Not easy to write like this: ... *)
(* have [hDl|hBl]:= sTl_maskP hΔl hTl. *)
(*   left; exists [::B maskl D l & maskb F b]. *)
(*     by case/cbodyP: b {ihb hΔb hTb} => [|l' b']; rewrite ?body_mask_cons inE eqxx. *)
(*   by rewrite sTbΔ_cons hDl -sTbF. *)
(* have [[Δbt Δbt_in hTΔ]|hTB] := ihb hΔb hTb. *)
(*   case/cbodyP: b {ihb hΔb hTb} Δbt_in => [|l' b'] Δbt_in. *)
(*     left; exists [::B maskl D l ]. *)
(*       rewrite inE eqxx //. *)


Lemma fwd_or_clause_deltaP p s edb supp Δ done
  (* Safety *)
  (h_sf : safe_cl (p s))

  (* Strata conditions [can be improved] *)
  (hC : wc_sset done)
  (hw : p \in wf_slice (Ds done))
  (hi : '(s, Single) \notin done)
  (hc : tsymc (p s) \subset done)
  (hm : ssTp (edb :+: Δ) (Ds done) p)
  (hΔ : suppΔ Δ \subset done)

  (* Incremental conditions *)
  (hv : ssTp edb (Ds supp) p)
  (hs : '(s, Single) \in supp)
  (hdΔ : [disjoint tsymc (p s) & suppg Δ.(deld)]) :

  (* Main algorithm *)
  let c   := p s     in
  let arg := headc c in
  let body:= bodyc c in
  let Δ' := fwd_or_clause_delta edb Δ s arg body in
  ssTp (edb :+: Δ') (s |: Ds done) p.
Proof.
rewrite /fwd_or_clause_delta /= ssTp_mod_put // hm andbT.
set Δ' := putΔ _ _ _ _.
apply/forallP=> gr; apply/implyP=> hbody; rewrite /= lrelE in_appd.
have hsΔN: '(s, Single) \notin suppg Δ.(deld).
  rewrite subUset in hΔ; case/andP: hΔ => _ /subsetP hd.
  by apply/negP=> /hd; apply/negP.
have hsΔ' : suppg Δ'.(deld) = suppg Δ.(deld) by rewrite suppgd_put.
have hNΔ: '(s, Single) \notin suppg Δ'.(deld) by rewrite hsΔ'.
rewrite (suppgN_mem _ hNΔ) andbT.
have hs' := DsP hs.
have/implyP/(_ hs')/forallP/(_ gr)/implyP Hstc := (forallP hv) s.
set ohd := headc _ in Δ' hsΔ' hNΔ hbody Hstc *.
set obd := bodyc _ in Δ' hsΔ' hNΔ hbody Hstc *.
set ghd := '(_,_).
set gtl := [seq _ | _ <- _] in hbody Hstc *.
case/hasP: hbody => gb gb_in HsTb.
case/mapP: (gb_in) => oΔb ob_in ob_eq.
have hdΔ': [disjoint tsymb gb & suppg (deld Δ')].
  suff: [disjoint tsymb oΔb & suppg (deld Δ)].
    by rewrite ob_eq tsymbM suppgd_put.
  exact: (disjoint_tsymc_tsymb ob_in).
have [[Δb]|H]:= sTb_maskP hdΔ' HsTb; last first.
  have/Hstc: has (sTb edb) gtl; first by apply/hasP; exists gb.
  by rewrite /= lrelE => ->.
rewrite ob_eq{gb HsTb ob_eq hdΔ'} in gb_in *.
move=> hΔm hΔT.
have hss := set11 (@sub0 n V).
have h0 := lesub0s (gr_to_sub gr).
have hdwΔ: [disjoint tsymb oΔb & suppg (deld Δ)].
  exact: (disjoint_tsymc_tsymb ob_in).

have hmod: sTbΔ edb Δ' Δb = sTbΔ edb Δ Δb.
  apply: eq_in_all => l hia; apply: (@sat_wf_slice_litΔP done).
    by rewrite eqsgC; apply: (eqsg_put_addd_mod2 Δ _ _ hi).
    by rewrite eqsgC; apply: (eqsg_put_deld_mod2 Δ _ _ hi).
  rewrite inE.
  suff: tsyml (umaskl l) \in done by case: l {hia}.
  have Hl: (umaskl l) \in litb (grb gr oΔb).
    exact: (body_maskP hΔm).
  case/mapP: Hl => oul houl ->.
  have := cb_tsyml_in_supp hc houl ob_in.
  by have := cb_tsyml_in_supp hc houl ob_in.
rewrite hmod in hΔT.
have [r rin rsub] := fwd_delta_body_complete hdwΔ hss h0 hΔm hΔT.
apply/orP; right; rewrite !ffunE eqxx; apply/imsetP.
exists r; first by apply/bigcup_seqP; exists oΔb; rewrite // rin.

(* Now from hsubs we know that gr and bsub agree *)
(* That plus safety concludes the proof. *)
(* The original proof was a mess here, refactor. *)
case/allP/(_ _ ob_in)/andP: h_sf => [hfs1 hfs2].
have Hb: varb oΔb \subset dom r.
  have [cb' hcb'] := fwd_delta_body_sound [set r] hdwΔ rin.
  by apply/varb_sub_dom; exists cb'.
have V1: vart ohd.1 \subset dom r.
  exact/(subset_trans hfs1).
have V2: vart ohd.2 \subset dom r.
  exact/(subset_trans hfs2).
by rewrite /ghd !(in_dom_grt def rsub).
Qed.

Lemma suppΔ_fwd_or_clause_delta s args body edb Δ :
  suppΔ (fwd_or_clause_delta edb Δ s args body) \subset '(s, Single) |: suppΔ Δ.
Proof. by rewrite /fwd_or_clause_delta suppΔ_putΔ. Qed.

End DeltaMatching.

Section BaseMatching.

(* Called fwd_clause in the engine *)
Definition fwd_cbody edb Δ b : ssub :=
  match_body (edb :+: Δ) b [set sub0].

Definition fwd_dbody edb Δ d : ssub :=
  \bigcup_(d <- d) fwd_cbody edb Δ d.

Definition fwd_or_clause_base edb Δ s arg body :=
  putΔ Δ '(s, Single) (EGraph [set gr_args_def def s arg | s in fwd_dbody edb Δ body ]) g0.

(* The main job of this theorem is to:
 * - isolate the changes to the current strata.
 * - apply safety.
 *)
Lemma fwd_or_clause_baseP p s done edb Δ
  (h_sf : safe_cl (p s))
  (* Strata conditions [can be improved] *)
  (hC : wc_sset done)
  (hs : p \in wf_slice (Ds done))
  (hi : '(s, Single) \notin done)
  (hc : tsymc (p s) \subset done)
  (hm : ssTp (edb :+: Δ) (Ds done) p) :
  (* Main algorithm *)
  let c   := p s     in
  let arg := headc c in
  let body:= bodyc c in
  let Δ' := fwd_or_clause_base edb Δ s arg body in
  ssTp (edb :+: Δ') (s |: Ds done) p.
Proof.
rewrite /= ssTp_mod_put // hm andbT.
set hd := headc _; set bd := bodyc _; set Δ' := putΔ _ _ _ _.
apply/forallP=> gr; apply/implyP=> /hasP[cb cbin hcb].
rewrite /prod_curry /grh /= lrelE in_appd; apply/orP; right.
rewrite /Δ' /addl !ffunE eqxx.
set grs := gr_to_sub gr; apply/imsetP.
(* Modularity has to be applied on the tail *)

(* Note that we have some redundancy between the _mod lemmas and the
   slice_litP lemma. I'd be great to resolve it. Additionally, we
   could profit from [edb :+: Δ' = edb :+: Δ :+: { s -> ...}] then
   [disjoint symb b & { s -> ...} ] *)
have hmod: sTb (edb :+: Δ') cb = sTb (edb :+: Δ) cb.
  apply: eq_in_all => l hia; apply: (@sat_wf_slice_litP done).
    by rewrite eqsgC; apply/eqsg_put_mod.
  have cbin': cb \in bodyc (grc gr (p s)) by [].
  by apply/(cb_tsyml_in_supp _ hia cbin'); rewrite tsymcM.
have hss := set11 (@sub0 n V).
have h0 := lesub0s (gr_to_sub gr).
have [ncb nbin neq]: exists2 ncb, ncb \in bodyc (p s) & cb = grb gr ncb.
  exact/mapP.
rewrite hmod neq {Δ' hmod} in hcb.
have /= [bsub hbs hsubs] := match_body_complete hss h0 hcb.
exists bsub; first by apply/bigcup_seqP; exists ncb; rewrite // hbs.
(* Now from hsubs we know that gr and bsub agree *)
(* That plus safety concludes the proof. *)
(* The original proof was a mess here, refactor. *)
case/allP/(_ ncb nbin)/andP: h_sf => [hfs1 hfs2].
have Hb: varb ncb \subset dom bsub.
  have [cb' hcb' cb'S] := match_body_sound hbs.
  by apply/varb_sub_dom; exists cb'.
have V1: vart hd.1 \subset dom bsub.
  exact/(subset_trans hfs1).
have V2: vart hd.2 \subset dom bsub.
  exact/(subset_trans hfs2).
by rewrite !(in_dom_grt def hsubs).
Qed.
(* Proof for match_bodyP:
have [bsub hbs [hsubs hgr]] /= := match_bodyP _ hss h0 erefl hcb.
exists bsub; first by apply/bigcup_seqP; exists ncb; rewrite // hbs.
(* Now from hsubs we know that gr and bsub agree *)
(* That plus safety concludes the proof. *)
case/allP/(_ ncb nbin)/andP: h_sf => [hfs1 hfs2].
have Hb: varb ncb \subset dom bsub.
  by apply/varb_sub_dom; exists cb; rewrite hgr neq.
have V1: vart hd.1 \subset dom bsub.
  exact/(subset_trans hfs1).
have V2: vart hd.2 \subset dom bsub.
  exact/(subset_trans hfs2).
by rewrite !(in_dom_grt def hsubs).
end of proof for match_bodyP *)

Lemma suppΔ_fwd_or_clause_base s args body edb Δ :
  suppΔ (fwd_or_clause_base edb Δ s args body) \subset '(s, Single) |: suppΔ Δ.
Proof. by rewrite /fwd_or_clause_base suppΔ_putΔ. Qed.

(* A question here is where to do the grounding; in the original ML
   engine we used to do the grounding per conjuntive clause, but now
   here we take the union of the clauses instead. *)
Definition fwd_or_clause edb supp Δ s arg body : edelta _ _ :=
  let supp_cl := tsymd body     in
  let sadd_Δ  := suppg (addd Δ) in
  let srem_Δ  := suppg (deld Δ) in
  (* Deletion processing: if we have some negative delta, we force full recomputation *)
  if ~~ [disjoint supp_cl & srem_Δ] then
    fwd_or_clause_base edb Δ s arg body
    (*
    let Δ' := fwd_or_clause_base edb Δ s arg body in
    let diffΔ := diffg (edb (s,Single)) ((edb :+: Δ') (s,Single)) in
    putΔ Δ (s,Single) diffΔ.1 diffΔ.2
    *)
  (* Addition processing: if s is not in supp, we must do full recomputation *)
  else if '(s,Single) \notin supp
  then fwd_or_clause_base edb Δ s arg body
  (* else, if Δ⁺ doesn't intersect with the tail, we do nothing *)
  else if [disjoint supp_cl & sadd_Δ]
  then Δ
  (* otherwise we call the incremental delta processing *)
  else fwd_or_clause_delta edb Δ s arg body.

Arguments fwd_or_clause_base edb Δ s arg body : simpl never.
Arguments fwd_or_clause edb supp Δ s arg body : simpl never.

(* At this point we know:

   h1:   G    ⊨_{supp,s} p
   h2:   G, Δ ⊨_{supp}   p

   we want

      G, Δ' ⊨_{supp,s} p

   where Δ' = Δ ∪ { s -> fwd_or_clause arg body edb Δ }

 *)
End BaseMatching.

Lemma fwd_or_clauseP p s supp done edb Δ
  (h_sf : safe_cl (p s))
  (* Incrementality condition, edb is a model for supp *)
  (hv : ssTp edb (Ds supp) p)
  (* Strata conditions [can be improved] *)
  (hC : wc_sset done)
  (hs : p \in wf_slice (Ds done))
  (hi : '(s, Single) \notin done)
  (hc : tsymc (p s) \subset done)
  (hm : ssTp (edb :+: Δ) (Ds done) p)
  (hΔ : suppΔ Δ \subset done) :
  (* Main algorithm *)
  let c   := p s     in
  let arg := headc c in
  let body:= bodyc c in
  let Δ' := fwd_or_clause edb supp Δ s arg body in
  ssTp (edb :+: Δ') (s |: Ds done) p.
Proof.
rewrite /fwd_or_clause; case: ifPn; rewrite ?negbK => hrem.
  (* First case, negation. *)
  by have H := fwd_or_clause_baseP h_sf hC hs hi hc hm.
case: ifPn; rewrite ?negbK => hvs.
  exact: fwd_or_clause_baseP.
case: ifPn; rewrite ?negbK => hadd.
  (* We don't update. *)
  rewrite ssTp_setU hm andbT ssTp1 sTc_mod //.
      by apply/(in_ssTp _ hv); apply: DsP hvs.
    by apply/negP=> /(subsetP hΔ) hnin; rewrite hnin in hi.
  by rewrite disjoints_subset setCU subsetI !subsets_disjoint !setCK hadd.
set dummyl := {| tagl := (Single, B); atoml := {| syma := s; arga := '(def,def) |} |}.
exact: (fwd_or_clause_deltaP _ _ _ _ _ _ _ hv).
Qed.

Lemma suppΔ_fwd_or_clause s args body edb supp Δ :
  suppΔ (fwd_or_clause edb supp Δ s args body) \subset '(s, Single) |: suppΔ Δ.
Proof.
rewrite /fwd_or_clause; do !case: ifP => //.
+ by rewrite suppΔ_fwd_or_clause_base.
+ by rewrite suppΔ_fwd_or_clause_base.
+ by rewrite ?subsetUr.
+ by rewrite suppΔ_fwd_or_clause_delta.
Qed.

Lemma set1ss (T : finType) (x : T) : [set x; x] = [set x].
Proof. by apply/setP=> ?; apply/set2P/set1P; intuition. Qed.

Definition compute_closures edb Δ s : edelta _ _ :=
  let bg := (edb :+: Δ) '(s,Single) in
  (* let: Δstar := diffg bg (starg bg) in *)
  let sg := (edb :+: Δ) '(s,Plus)   in
  let Δplus := diffg sg (plusg bg) in
  (* let: Δ := putΔ Δ (s, Star) Δstar.1 Δstar.2 in *)
  let Δ := putΔ Δ '(s, Plus) Δplus.1 Δplus.2 in
  Δ.

(* The diff of the closure is correct. *)
Lemma update_closureP (bg sg : egraph V) :
  let ng := diffg sg (plusg bg) in
  (sg :|: ng.1) :\: ng.2 = plusg bg.
Proof. by rewrite {2}(diffgP sg (plusg bg)). Qed.

(* This is routine. *)
Lemma compute_closuresP p edb Δ s done :
  (* wc_sset done -> *)
  (* p \in wf_slice (Ds done) -> *)
  '(s, Plus) \notin done ->
  ssTp (edb :+: Δ) (Ds done) p ->
  ssTp (edb :+: compute_closures edb Δ s) (Ds ('(s,Plus) |: done)) p.
Proof.
Admitted.

Lemma suppΔ_compute_closures s edb Δ :
  suppΔ (compute_closures edb Δ s) \subset '(s, Plus) |: suppΔ Δ.
Proof. by rewrite /compute_closures suppΔ_putΔ. Qed.

(* We give the strata as an explicit list of symbols. *)
Fixpoint fwd_program p edb supp Δ done todo : edelta V _ :=
  match todo with
  | [::]        => Δ
  | [:: s & ss] =>
    let c   := p s in
    let arg := headc c in
    let body:= bodyc c in
    let Δ'  := fwd_or_clause edb supp Δ s arg body in
    let Δ'  := compute_closures edb Δ' s           in
    (* let s   := [set (s,Single);(s,Star);(s,Plus) ] in *)
    let s   := [set '(s,Single);(* (s,Star); *)'(s,Plus) ] in
    fwd_program p edb supp Δ' (s :|: done) ss
  end.

(* Given a well stratified program <p,str>, and a model <edb,Δ> for
   done, the fwd_program is a model for `done ∪ todo` *)
Theorem fwd_clauseP p edb supp Δ done todo
  (* The program meets the safety condition *)
  (h_sf : safe_pr p)
  (* The validated set is true *)
  (h_prev: ssTp edb (Ds supp) p) :

  (* The done set for is complete for the closures *)
  wc_sset done ->
  (* The processed part of the program is a wf strate [todo: fold1] *)
  wf_slice (Ds done) p ->
  (* Delta is restricted, we don't allow updates to intensional predicates *)
  suppΔ Δ \subset done ->
  (* The program is well-stratified and regular-recursive program
     [condition coming from reg queries] *)
  is_strata_rec p todo (Ds done) ->
  (* For the "done" part of the graph/query, edb / Δ is a model of p *)
  ssTp (edb :+: Δ) (Ds done) p ->
  (* Then let Δ' be the update for the "todo" part *)
  let Δ' := fwd_program p edb supp Δ done todo in
  (* Theorem: then edb / Δ' is a model for the full graph "todo ∪ done" *)
  ssTp (edb :+: Δ') (Ds done :|: suppstr todo) p.
  (* ssTp edb Δ p == edb / Δ is a model of [p] *)

Proof.
elim: todo Δ done => [|s str ihs] Δ done hC hs hΔ.
  by rewrite /= /suppstr setlist0 setU0.
rewrite /is_strata /=; case/and3P => hs1 hs2 hs3 hm.

set prog_fwd := fwd_or_clause _ _ _ _ _ _.
set prog_cls := compute_closures _ _ _.
set n_done := [set '(s,Single) ; '(s,Plus)] :|: done.

(* Misc. conditions. *)
have hnd : Ds n_done = (s |: Ds done).
  by rewrite /n_done /Ds !imsetU !imset_set1 /= set1ss.

have hsuppstr: Ds done :|: suppstr (s :: str) = Ds n_done :|: suppstr str.
  by rewrite hnd suppstr_cons setUCA setUA.

have hC':= @wc_ssetP s _ hC.

have hs': wf_slice (Ds n_done) p.
  rewrite hnd wf_sliceU // eq_forall_set1 subsetU ?hs3 ?orbT //.
  by apply/forall_inP=> z hsup; rewrite subsetU // ?hs3 (forall_inP hs) ?orbT.

have hΔ': suppΔ prog_cls \subset n_done.
  rewrite (subset_trans _ (setUS [set '(s,Single); '(s,Plus)] hΔ)) //.
  have/subset_trans->// := suppΔ_compute_closures s edb prog_fwd.
  rewrite [ [set '(s,Single)] :|: _ ]setUC -setUA setUS //.
  by have/subset_trans-> := suppΔ_fwd_or_clause s (headc (p s)) (bodyc (p s)) edb supp Δ.

have hstr: is_strata_rec p str (Ds n_done) by rewrite hnd.

have hm': ssTp (edb :+: prog_cls) (Ds n_done) p.
  have hs2': '(s, Single) \notin done by move: hs2; apply/contra/DsP.
  have hs3': tsymc (p s) \subset done by exact/wc_tsymc.

  have /= := fwd_or_clauseP (h_sf s) h_prev hC hs hs2' hs3' hm hΔ.
  set prog_fwd' := fwd_or_clause _ _ _ _ _ _; rewrite -(DsU _ Single) => hor.

  have hsS': '(s, Plus) \notin '(s,Single) |: done.
    have U: Plus != Single by apply/eqP.
    rewrite !inE negb_or xpair_eqE eqxx /= U.
    by move: hs2; apply/contra/DsP.
  by have hclos := compute_closuresP hsS' hor; rewrite /n_done -setUA setUCA.

by have := ihs prog_cls n_done hC' hs' hΔ' hstr hm'; rewrite hsuppstr.
Qed.

Print Assumptions fwd_clauseP.

End RQEngine.
End RegularQueries.
End VUP.
