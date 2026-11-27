import PairComponents180
set_option warningAsError true
namespace Minimal180.Controlled
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Exact old-graph test for returning x and one other leaf b. Its right side
can be computed for every b from one decomposition of the retained core. -/
theorem pair_exchange_iff (J : SimpleGraph V) (C Z : Finset V) (x y b : V)
    (xy : x≠y) (tip : NeedsTip J C (univ\C) x y) (bc : b∈C.erase x)
    (zs : Z⊆(univ\C).erase y) :
    let R := (univ\C)\Z
    let L := (C.erase x).erase b ∪ Z
    let G := J⊔SimpleGraph.edge x y
    (Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q) ↔
      (∀ a∈R,Dominates J (part J R a) b ∨ (J.Adj x b ∧ (within J R).Reachable a y)) ∧
      (∀ q∈demand J R C Z x,q=b ∨ J.Adj q b) := by
  classical
  let R := (univ\C)\Z
  let L := (C.erase x).erase b ∪ Z
  let G := J⊔SimpleGraph.edge x y
  let Q := insert b (insert x R)
  obtain ⟨bx,bC⟩ := mem_erase.mp bc
  have xc := tip.1
  have yc := (mem_sdiff.mp tip.2.1).2
  have zs' {t : V} (z : t∈Z) : t≠y ∧ t∉C :=
    ⟨(mem_erase.mp (zs z)).1,(mem_sdiff.mp (mem_of_mem_erase (zs z))).2⟩
  have xz : x∉Z := fun h => (zs' h).2 xc
  have bz : b∉Z := fun h => (zs' h).2 bC
  have yz : y∉Z := fun h => (zs' h).1 rfl
  have yr : y∈R := mem_sdiff.mpr ⟨tip.2.1,yz⟩
  have br : b∉R := fun h => (mem_sdiff.mp (mem_sdiff.mp h).1).2 bC
  have xr : x∉R := fun h => (mem_sdiff.mp (mem_sdiff.mp h).1).2 xc
  have by' : b≠y := fun e => yc (e ▸ bC)
  have no : ¬Dominates J R x := by
    rintro ⟨a,ha,e⟩
    exact tip.2.2.2.1 ⟨a,(mem_sdiff.mp ha).1,e⟩
  have split : univ\L=Q := by
    ext a
    by_cases ab : a=b
    · subst a; simp [L,Q,bz]
    by_cases ax : a=x
    · subst a; simp [L,Q,xz]
    simp only [L,Q,R,mem_sdiff,mem_univ,true_and,mem_union,mem_erase,mem_insert,ax,ab,
      not_false_eq_true,false_or]
    tauto
  have other {q : V} (h : q∈L) : q≠x ∧ q≠y ∧ q≠b := by
    rcases mem_union.mp h with h|h
    · obtain ⟨qb,qcx⟩ := mem_erase.mp h
      obtain ⟨qx,qc⟩ := mem_erase.mp qcx
      exact ⟨qx,fun e => yc (e ▸ qc),qb⟩
    · exact ⟨fun e => xz (e ▸ h),(zs' h).1,fun e => bz (e ▸ h)⟩
  have orig {q a : V} (h : q∈L) (e : G.Adj q a) : J.Adj q a := by
    rcases e with e|e
    · exact e
    · rcases ((edge_adj ..).mp e).1 with h'|h'
      · exact ((other h).1 h'.1).elim
      · exact ((other h).2.1 h'.1).elim
  have dom : (∀ q∈L,Dominates G Q q) ↔ (∀ q∈demand J R C Z x,q=b ∨ J.Adj q b) := by
    constructor
    · intro all q h
      obtain ⟨place,nr,nx⟩ := (mem_demand ..).mp h
      by_cases qb : q=b
      · exact Or.inl qb
      have ql : q∈L := by
        rcases mem_union.mp place with k|k
        · exact mem_union_left _ (mem_erase.mpr ⟨qb,k⟩)
        · exact mem_union_right _ k
      obtain ⟨a,ha,e⟩ := all q ql
      have ed := orig ql e
      rcases mem_insert.mp ha with ab|ha
      · exact Or.inr (ab ▸ ed)
      rcases mem_insert.mp ha with ax|ar
      · exact (nx (ax ▸ ed)).elim
      · exact (nr ⟨a,ar,ed⟩).elim
    · intro serve q h
      by_cases domR : Dominates J R q
      · obtain ⟨a,ar,e⟩ := domR
        exact ⟨a,mem_insert_of_mem (mem_insert_of_mem ar),Or.inl e⟩
      by_cases qx : J.Adj q x
      · exact ⟨x,mem_insert_of_mem (mem_insert_self ..),Or.inl qx⟩
      have place : q∈C.erase x∪Z := by
        rcases mem_union.mp h with k|k
        · exact mem_union_left _ (mem_of_mem_erase k)
        · exact mem_union_right _ k
      rcases serve q ((mem_demand ..).mpr ⟨place,domR,qx⟩) with qb|e
      · exact ((other h).2.2 qb).elim
      · exact ⟨b,mem_insert_self ..,Or.inl e⟩
  change (Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q) ↔ _
  rw [split]
  exact and_congr (pair_core_iff J R x y b xy bx by' br xr yr no) dom

/-- Two or more releases and a single returned vertex with the old-graph
properties suffice to beat the full lower optimum. -/
theorem first_of_pair_exchange (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w b : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C Z : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (bc : b∈C.erase x) (zs : Z⊆(U\C).erase y)
    (len : 2≤Z.card)
    (join : let R := (univ\C)\Z
      ∀ a∈R,Dominates J (part J R a) b ∨ (J.Adj x b ∧ (within J R).Reachable a y))
    (serve : ∀ q∈demand J ((univ\C)\Z) C Z x,q=b ∨ J.Adj q b) : FirstForm J U x y w := by
  classical
  have zs' : Z⊆(univ\C).erase y := by
    intro t h
    obtain ⟨ty,tc⟩ := mem_erase.mp (zs h)
    exact mem_erase.mpr ⟨ty,mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp tc).2⟩⟩
  have test := pair_exchange_iff J C Z x y b xy tip bc zs'
  dsimp only at test
  have win := test.mpr ⟨join,serve⟩
  apply (second_split_iff J hc hn x y w xy old xw wy U C cu count tip).mpr
  exact ⟨{b},singleton_subset_iff.mpr bc,Z,zs,by simpa only [card_singleton] using len,
    by simpa only [sdiff_singleton_eq_erase] using win⟩

#print axioms pair_exchange_iff
#print axioms first_of_pair_exchange
end Minimal180.Controlled
