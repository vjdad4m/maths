import DefectiveCharge189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.DefectiveCharge
open private Graffiti189LongestPath.boundary_card_of_connectivity
  Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two from SmallSeparator189
set_option warningAsError true
set_option maxHeartbeats 3000000
namespace Graffiti189LongestPath.DefectiveWideCut
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- For a shore cut X, a side C of size t with no other internal external
edges must be empty when 2|X|+t+2<|A|. Consequently the
smaller side of any shore cut of size s is empty if 3s+4<|A|. -/
theorem defective_small_side_of_shore_cut (hc : G.Connected) (k : Nat)
    (A B U C X : Finset V) (x : V)
    (conn : ∀ D : Finset V,D.card<k → (G.induce ((↑D : Set V)ᶜ)).Connected)
    (exactB : B.card≤k+1) (ab : Disjoint A B) (ub : Disjoint U B)
    (au : Disjoint A U) (large : k≤U.card) (_kp : 0<k)
    (closedA : ∀ u∈A,∀ v∉A,G.Adj u v → v∈B)
    (closedU : ∀ u∈U,∀ v∉U,G.Adj u v → v∈B)
    (cap : ∀ v,(DistanceTwo G v).card≤k+2)
    (root : ∀ v∈A,v=x ∨ G.Adj x v)
    (CA : C⊆A) (XA : X⊆A) (dis : Disjoint C X)
    (inside : ∀ u∈C,∀ v∈A,G.Adj u v → v∈C∪X)
    (small : 2*X.card+C.card+3<A.card) :
    C=∅ := by
  classical
  apply eq_empty_iff_forall_not_mem.mpr
  intro v vc
  let j : ↥(A : Set V) := ⟨v,CA vc⟩
  let J := G.induce (A : Set V)
  let N := (J.neighborFinset j).image Subtype.val
  let Q := C.filter (G.Adj v)
  let Z := (G.neighborFinset v).filter (fun z => z∉A)
  let R := (DistanceTwo G v)∩B
  let W := insert v Q
  let D := ((X∪(C\W))∪Z)∪R
  have f (z : V) : z∈N ↔ z∈A ∧ G.Adj v z := by
    constructor
    · intro hz
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
      exact ⟨w.property,(J.mem_neighborFinset _ _).mp hw⟩
    · rintro ⟨za,ed⟩
      exact mem_image.mpr ⟨⟨z,za⟩,(J.mem_neighborFinset _ _).mpr ed,rfl⟩
  have ncard : N.card=J.degree j := by
    rw [←J.card_neighborFinset_eq_degree,card_image_of_injective _ Subtype.val_injective]
  have into : N⊆Q∪X := by
    intro z zn
    obtain ⟨za,ed⟩ := (f z).mp zn
    rcases mem_union.mp (inside v vc z za ed) with zc|zx
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨zc,ed⟩))
    · exact mem_union.mpr (Or.inr zx)
  have nupper := (card_le_card into).trans (card_union_le Q X)
  have nz : N∪Z=G.neighborFinset v := by
    ext z
    rw [mem_union,f,mem_filter,G.mem_neighborFinset]
    by_cases q : z∈A <;> simp [q]
  have nd : Disjoint N Z := disjoint_left.mpr (fun _ h h' => (mem_filter.mp h').2 ((f _).mp h).1)
  have cost := congrArg Finset.card nz
  rw [card_union_of_disjoint nd,ncard,G.card_neighborFinset_eq_degree] at cost
  have ch := defective_universal_shore_charge hc (k+2) k A U B conn exactB ab ub au large
    closedA closedU cap root j
  change A.card+G.degree v+R.card≤2*J.degree j+(k+2)+2 at ch
  have ws : W⊆C := by
    intro z zw
    rcases mem_insert.mp zw with rfl|hz
    · exact vc
    · exact (mem_filter.mp hz).1
  have wSize : W.card=Q.card+1 := card_insert_of_not_mem (fun h => (G.loopless v) (mem_filter.mp h).2)
  have how : (C\W).card+W.card=C.card := card_sdiff_add_card_eq_card ws
  have d1 := card_union_le X (C\W)
  have d2 := card_union_le (X∪(C\W)) Z
  have d3 := card_union_le ((X∪(C\W))∪Z) R
  have dc : D.card<k := by
    dsimp only [D]
    omega
  have nb (z : V) (zb : z∈B) : z∉A := fun h => disjoint_left.mp ab h zb
  have zB (z : V) (zz : z∈Z) : z∈B := by
    obtain ⟨a,b⟩ := mem_filter.mp zz
    exact closedA v (CA vc) z b ((G.mem_neighborFinset _ _).mp a)
  have wd : Disjoint W D := disjoint_left.mpr (by
    intro z zw h
    rw [show D=((X∪(C\W))∪Z)∪R from rfl] at h
    rcases mem_union.mp h with h|h
    · rcases mem_union.mp h with h|h
      · rcases mem_union.mp h with h|h
        · exact disjoint_left.mp dis (ws zw) h
        · exact (mem_sdiff.mp h).2 zw
      · exact nb z (zB z h) (CA (ws zw))
    · exact nb z (mem_inter.mp h).2 (CA (ws zw)))
  obtain ⟨u,uu⟩ := card_pos.mp (by omega : 0<U.card)
  have ua : u∉A := fun h => disjoint_left.mp au h uu
  have ub' : u∉B := fun h => disjoint_left.mp ub uu h
  have uw : u∉W := fun h => ua (CA (ws h))
  have ud : u∉D := by
    intro h
    rcases mem_union.mp h with h|h
    · rcases mem_union.mp h with h|h
      · rcases mem_union.mp h with h|h
        · exact ua (XA h)
        · exact ua (CA (mem_sdiff.mp h).1)
      · exact ub' (zB u h)
    · exact ub' (mem_inter.mp h).2
  have bd : ∀ u∈W,∀ z∉W,G.Adj u z → z∈D := by
    intro w ww z zw ed
    by_cases za : z∈A
    · rcases mem_union.mp (inside w (ws ww) z za ed) with zc|zx
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl
          (mem_union.mpr (Or.inr (mem_sdiff.mpr ⟨zc,zw⟩))))))
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_union.mpr (Or.inl zx)))))
    have zb := closedA w (CA (ws ww)) z za ed
    by_cases vz : G.Adj v z
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr
        (mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr vz,za⟩))))
    rcases mem_insert.mp ww with e|q
    · exact (vz (e ▸ ed)).elim
    · have ve : v≠z := fun e => za (e ▸ CA vc)
      exact mem_union.mpr (Or.inr (mem_inter.mpr ⟨Graffiti189LongestPath.mem_distanceTwo.mpr
        (Graffiti189LongestPath.dist_two hc ve vz (mem_filter.mp q).2 ed),zb⟩))
  have vk := Graffiti189LongestPath.boundary_card_of_connectivity k conn
    (mem_insert_self v Q) uw ud wd bd
  exact (not_lt_of_ge vk) dc

/-- No shore cut of size s with 3s+4<|A| separates any two vertices. -/
theorem defective_shore_cut_no_split (hc : G.Connected) (k : Nat)
    (A B U X C E : Finset V) (x : V)
    (conn : ∀ D : Finset V,D.card<k → (G.induce ((↑D : Set V)ᶜ)).Connected)
    (exactB : B.card≤k+1) (ab : Disjoint A B) (ub : Disjoint U B)
    (au : Disjoint A U) (large : k≤U.card) (kp : 0<k)
    (closedA : ∀ u∈A,∀ v∉A,G.Adj u v → v∈B)
    (closedU : ∀ u∈U,∀ v∉U,G.Adj u v → v∈B)
    (cap : ∀ v,(DistanceTwo G v).card≤k+2)
    (root : ∀ v∈A,v=x ∨ G.Adj x v)
    (XA : X⊆A) (part : C∪E=A\X) (dis : Disjoint C E)
    (no : ∀ u∈C,∀ v∈E,¬G.Adj u v)
    (small : 3*X.card+6<A.card) :
    C=∅ ∨ E=∅ := by
  classical
  have cc : C⊆A\X := fun _ h => part ▸ mem_union.mpr (Or.inl h)
  have ec : E⊆A\X := fun _ h => part ▸ mem_union.mpr (Or.inr h)
  have sz := congrArg Finset.card part
  rw [card_union_of_disjoint dis] at sz
  have eq := card_sdiff_add_card_eq_card XA
  by_cases e : C.card≤E.card
  · left
    apply defective_small_side_of_shore_cut hc k A B U C X x conn exactB ab ub au large kp
      closedA closedU cap root (fun _ h => (mem_sdiff.mp (cc h)).1) XA
      (disjoint_left.mpr (fun _ h h' => (mem_sdiff.mp (cc h)).2 h')) ?_ (by omega)
    intro u uc v va uv
    by_cases vx : v∈X
    · exact mem_union.mpr (Or.inr vx)
    have vce : v∈C∪E := part.symm ▸ mem_sdiff.mpr ⟨va,vx⟩
    exact (mem_union.mp vce).elim (fun h => mem_union.mpr (Or.inl h))
      (fun h => (no u uc v h uv).elim)
  · right
    apply defective_small_side_of_shore_cut hc k A B U E X x conn exactB ab ub au large kp
      closedA closedU cap root (fun _ h => (mem_sdiff.mp (ec h)).1) XA
      (disjoint_left.mpr (fun _ h h' => (mem_sdiff.mp (ec h)).2 h')) ?_ (by omega)
    intro u ue v va uv
    by_cases vx : v∈X
    · exact mem_union.mpr (Or.inr vx)
    have vce : v∈C∪E := part.symm ▸ mem_sdiff.mpr ⟨va,vx⟩
    exact (mem_union.mp vce).elim (fun h => (no v h u ue uv.symm).elim)
      (fun h => mem_union.mpr (Or.inl h))

#print axioms defective_small_side_of_shore_cut
#print axioms defective_shore_cut_no_split
end Graffiti189LongestPath.DefectiveWideCut
