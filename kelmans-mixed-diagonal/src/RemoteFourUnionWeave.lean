import RemoteFourMixedCycle
import RemoteCycleChainCover
import RemoteBudgetComponent

namespace KelmansCactus.AtomicBridge.RemoteFourUnionWeave
open SimpleGraph Finset
open RemoteBudgetComponent (Mate exchangeGraph)
open RemoteSubdivisionCore (Marks)
open RemoteCycleChain (weave label label_hit label_none weave_nodup weave_head old_weave labels_weave label_ends)
open RemoteSixMixed (Between)
open RemoteFourMixedCycle (Sealed diagonal_cycles)
variable {V I : Type*} {G : SimpleGraph V} (M : Marks G I)

def oldUnion (p q : Mate G) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ (p.mate x≠y ∨ q.mate x≠y)
  symm := by
    intro x y ⟨edge,h⟩
    exact ⟨edge.symm,h.elim (fun e=>Or.inl (fun t=>e (Mate.reverse t)))
      (fun e=>Or.inr (fun t=>e (Mate.reverse t)))⟩
  loopless := fun x h=>G.loopless x h.1

/-- At an active alternating vertex the used edge belongs to exactly one
complementary matching, hence is available in the other rank. -/
theorem active_strip_edge (p q : Mate G) {x y : V}
    (diff : p.mate x≠q.mate x) (e : (exchangeGraph p q).Adj x y) :
    (oldUnion p q).Adj x y := by
  rcases e with a|a
  · exact ⟨a ▸ p.edge x,Or.inr (fun b=>diff (a.trans b.symm))⟩
  · exact ⟨a ▸ q.edge x,Or.inl (fun b=>diff (b.trans a.symm))⟩

def rebuild (F : SimpleGraph V) : SimpleGraph (V⊕I) where
  Adj x y := M.expanded.Adj x y ∧ match x,y with
    | .inl u,.inl v => F.Adj u v
    | _,_ => True
  symm := by
    rintro (x|i) (y|j) ⟨a,b⟩
    · exact ⟨a.symm,b.symm⟩
    all_goals exact ⟨a.symm,trivial⟩
  loopless := fun x h=>M.expanded.loopless x h.1

theorem old_edge_lift (F : SimpleGraph V) (sub : F≤G)
    {x y : V} (e : F.Adj x y) (unmarked : ¬M.Removed x y) :
    (rebuild M F).Adj (.inl x) (.inl y) :=
  ⟨⟨sub e,unmarked⟩,e⟩

/-- The expanded strip remains in the actual union; inserted slot edges are
always available, but an unmarked old edge must belong to at least one rank. -/
theorem woven_in_rebuild (F : SimpleGraph V) (sub : F≤G) :
    ∀ {L : List V}, L.Chain' F.Adj → (weave (label M) L).Chain' (rebuild M F).Adj
  | [],_ => by simp [weave]
  | [_],_ => by simp [weave]
  | a::b::P,path => by
    obtain ⟨ab,bt⟩ := List.chain'_cons.mp path
    have rec := woven_in_rebuild F sub bt
    have start : ∀ z∈(weave (label M) (b::P)).head?, z=Sum.inl b := by simp [weave_head]
    cases hs : label M a b with
    | none =>
      rw [weave,hs]
      apply rec.cons'
      intro z hz
      rw [start z hz]
      exact old_edge_lift M F sub ab (label_none M hs)
    | some i =>
      rw [weave,hs]
      change (Sum.inl a :: Sum.inr i :: weave (label M) (b::P)).Chain' (rebuild M F).Adj
      have ends := M.both_ends (label_hit M hs)
      apply (rec.cons' ?_).cons'
      · intro z h
        have hz : z=Sum.inr i := by simpa [eq_comm] using h
        subst z
        exact ⟨ends.1,trivial⟩
      · intro z h
        rw [start z h]
        exact ⟨ends.2,trivial⟩

theorem weave_head_map : ∀ L : List V,
    (weave (label M) L).head?=L.head?.map Sum.inl
  | [] => rfl
  | a::L => weave_head _ a L

theorem weave_last_map : ∀ L : List V,
    (weave (label M) L).getLast?=L.getLast?.map Sum.inl
  | [] => rfl
  | [_] => rfl
  | a::b::P => by
    rw [weave]
    change ((Sum.inl a :: (label M a b).toList.map Sum.inr) ++
      weave (label M) (b::P)).getLast? = (b::P).getLast?.map Sum.inl
    obtain ⟨x,hx⟩ : ∃ x : V, (b::P).getLast?=Option.some x :=
      ⟨(b::P).getLast (by simp),List.getLast?_eq_getLast_of_ne_nil (by simp)⟩
    rw [List.getLast?_append,weave_last_map (b::P),hx]
    rfl

theorem weave_between (F : SimpleGraph V) (sub : F≤G)
    {L : List V} {a b : V} (path : Between F L a b) :
    Between (rebuild M F) (weave (label M) L) (.inl a) (.inl b) :=
  ⟨weave_nodup M _ (label_hit M) path.nodup,woven_in_rebuild M F sub path.chain,
    by rw [weave_head_map,path.head]; rfl,by rw [weave_last_map,path.last]; rfl⟩

theorem weave_disjoint {L R : List V} (apart : ∀ x∈L,x∉R) :
    ∀ x∈weave (label M) L,x∉weave (label M) R := by
  rintro (x|i) hL hR
  · exact apart x ((old_weave _ _ _).mp hL) ((old_weave _ _ _).mp hR)
  · have l := label_ends M _ (label_hit M) ((labels_weave _ _ _).mp hL)
    have r := label_ends M _ (label_hit M) ((labels_weave _ _ _).mp hR)
    exact apart _ l.1 r.1

/-- An original cheap-four release yields exposed diagonal paths in the union;
provided they are given as simple ordered strips, this theorem weaves every
actual retained subdivision on them and closes both possible mixed square
orientations. It is separate from covering other common ears. -/
theorem expanded_diagonal_cycles (p q : Mate G) (P Q : List V)
    {a b c d : V} (ac : Between (oldUnion p q) P a c) (bd : Between (oldUnion p q) Q b d)
    (ab : (oldUnion p q).Adj a b) (bc : (oldUnion p q).Adj b c)
    (cd : (oldUnion p q).Adj c d) (da : (oldUnion p q).Adj d a)
    (nab : ¬M.Removed a b) (nbc : ¬M.Removed b c)
    (ncd : ¬M.Removed c d) (nda : ¬M.Removed d a)
    (apart : ∀ v∈P,v∉Q) :
    Sealed (rebuild M (oldUnion p q)) (weave (label M) P++weave (label M) Q) (.inl a) (.inl d) ∧
    Sealed (rebuild M (oldUnion p q)) (weave (label M) P++(weave (label M) Q).reverse) (.inl a) (.inl b) := by
  have sub : oldUnion p q≤G := fun _ _ h=>h.1
  apply diagonal_cycles _ _ (weave_between M _ sub ac) (weave_between M _ sub bd)
    (old_edge_lift M _ sub ab nab) (old_edge_lift M _ sub bc nbc)
    (old_edge_lift M _ sub cd ncd) (old_edge_lift M _ sub da nda)
    (weave_disjoint M apart)


/-- Genuine mixed-rank transfer: coverage by diagonal strips, one arbitrary
whole common ear, and remaining divisible disjoint runs gives a full factor
in both the mixed rebuild and the original subdivision board. -/
theorem expanded_diagonal_factor [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]
    (p q : Mate G) (P Q : List V) {a b c d : V}
    (ac : Between (oldUnion p q) P a c) (bd : Between (oldUnion p q) Q b d)
    (ab : (oldUnion p q).Adj a b) (bc : (oldUnion p q).Adj b c)
    (cd : (oldUnion p q).Adj c d) (da : (oldUnion p q).Adj d a)
    (nab : ¬M.Removed a b) (nbc : ¬M.Removed b c)
    (ncd : ¬M.Removed c d) (nda : ¬M.Removed d a) (apart : ∀ v∈P,v∉Q)
    (E : List (V⊕I)) (x : V⊕I)
    (xIn : x∈weave (label M) P++weave (label M) Q)
    (en : E.Nodup) (ec : E.Chain' (rebuild M (oldUnion p q)).Adj)
    (ear : ∀ y∈E.head?, (rebuild M (oldUnion p q)).Adj x y)
    (separ : Disjoint (weave (label M) P++weave (label M) Q).toFinset E.toFinset)
    (size : 3∣(weave (label M) P++weave (label M) Q).length+E.length)
    (rest : Finset (V⊕I))
    (runs : RemoteGapRunPacking.RunCover (rebuild M (oldUnion p q)) rest)
    (disjoint : Disjoint ((weave (label M) P++weave (label M) Q).toFinset∪E.toFinset) rest)
    (full : ((weave (label M) P++weave (label M) Q).toFinset∪E.toFinset)∪rest=Finset.univ) :
    SquareCap.HasFactor (rebuild M (oldUnion p q)) ∧ SquareCap.HasFactor M.expanded := by
  have cycles := expanded_diagonal_cycles M p q P Q ac bd ab bc cd da nab nbc ncd nda apart
  have nearFact := RemoteFourMixedCycle.absorb_ear cycles.1 xIn en ec ear separ size
  have all := RemoteVacancyRails.factor_disjUnion nearFact (RemoteGapRunPacking.runCover_factor runs) disjoint
  rw [full] at all
  refine ⟨all,?_⟩
  obtain ⟨tiles,legal,pairwise,cover⟩ := all
  refine ⟨tiles,fun T t=>?_,pairwise,cover⟩
  obtain ⟨card,c,cm,near⟩ := legal T t
  exact ⟨card,c,cm,fun y hy ne=>(near y hy ne).1⟩

#print axioms expanded_diagonal_factor
#print axioms active_strip_edge
#print axioms expanded_diagonal_cycles
end KelmansCactus.AtomicBridge.RemoteFourUnionWeave
