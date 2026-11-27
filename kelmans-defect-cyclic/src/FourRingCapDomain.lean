import FourRingThreeConnected

open Finset SimpleGraph
namespace KelmansCactus.FourRingCutAux
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def colourClass (c : V→Bool) (b : Bool) : Finset V := univ.filter (fun v=>c v=b)

omit [DecidableEq V] in
@[simp] theorem mem_colour_class {c : V→Bool} {b : Bool} {v : V} :
    v∈colourClass c b ↔ c v=b := by simp [colourClass]

def exitNeighbors (c : V→Bool) (v : V) : Finset V :=
  (G.neighborFinset v).filter (fun x=>c x=false)

theorem card_boundary_eq_exitSum (c : V→Bool) :
    (boundary G c).card=∑ v∈colourClass c true,(exitNeighbors G c v).card := by
  classical
  let row : V→Finset (V×V) := fun v=>(exitNeighbors G c v).image (fun x=>(v,x))
  have dis : (↑(colourClass c true):Set V).PairwiseDisjoint row := by
    intro a _ b _ ne
    apply disjoint_left.mpr
    intro x ha hb
    obtain ⟨i,_,en⟩ := mem_image.mp ha
    obtain ⟨j,_,em⟩ := mem_image.mp hb
    exact ne (congrArg (fun x : V×V=>x.1) (en.trans em.symm))
  have eq : boundary G c=(colourClass c true).biUnion row := by
    ext x
    constructor
    · intro hx
      obtain ⟨yes,no,e⟩ := mem_boundary.mp hx
      apply mem_biUnion.mpr
      refine ⟨x.1,mem_colour_class.mpr yes,mem_image.mpr ⟨x.2,?_,rfl⟩⟩
      exact mem_filter.mpr ⟨(mem_neighborFinset _ _ _).mpr e,no⟩
    · rintro m
      obtain ⟨v,yes,hm⟩ := mem_biUnion.mp m
      obtain ⟨u,um,rfl⟩ := mem_image.mp hm
      obtain ⟨a,b⟩ := mem_filter.mp um
      exact mem_boundary.mpr ⟨mem_colour_class.mp yes,b,(mem_neighborFinset _ _ _).mp a⟩
  rw [eq,card_biUnion dis]
  exact sum_congr rfl (fun _ _=>card_image_of_injective _ (fun _ _ e=>congrArg (fun p : V×V=>p.2) e))

theorem exit_len_le_one (c : V→Bool) (cub : ∀ v,G.degree v=3)
    {v a b : V} (va : G.Adj v a) (vb : G.Adj v b) (ne : a≠b)
    (insideA : c a=true) (insideB : c b=true) :
    (exitNeighbors G c v).card≤1 := by
  classical
  let N := G.neighborFinset v
  let P := ({a,b}:Finset V)
  have pin : P⊆N := by
    intro x hx
    simp only [P,mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact (mem_neighborFinset _ _ _).mpr va
    · exact (mem_neighborFinset _ _ _).mpr vb
  have sub : exitNeighbors G c v⊆N\P := by
    intro x hx
    obtain ⟨nx,no⟩ := mem_filter.mp hx
    refine mem_sdiff.mpr ⟨nx,?_⟩
    intro hx
    simp only [P,mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl
    · rw [insideA] at no; contradiction
    · rw [insideB] at no; contradiction
  have q := card_le_card sub
  have b := card_sdiff_add_card_eq_card pin
  have p : P.card=2 := by simp [P,ne]
  have n : N.card=3 := cub v
  omega

def TriangleFree (G : SimpleGraph V) : Prop :=
  ∀ x y z, G.Adj x y→G.Adj y z→G.Adj z x→False

/-- At order at least five in a simple cubic graph, a triangle
is a nontrivial three-edge cut. -/
theorem triangle_free_of_small_trivial (cub : ∀ v,G.degree v=3)
    (big : 5≤Fintype.card V) (small : SmallTrivial G) : TriangleFree G := by
  classical
  intro x y z xy yz zx
  let P : Finset V := {x,y,z}
  let c : V→Bool := fun v=>decide (v∈P)
  have yes (v : V) : c v=true ↔ v∈P := by simp [c]
  have size : P.card=3 := by simp [P,xy.ne,yz.ne,zx.ne,zx.ne.symm]
  have eq : colourClass c true=P := by ext v; rw [mem_colour_class,yes]
  have low : (boundary G c).card≤3 := by
    rw [card_boundary_eq_exitSum G,eq]
    have nz : ∀ v∈P,(exitNeighbors G c v).card≤1 := by
      intro v vm
      have y1 : c x=true := (yes _).mpr (by simp [P])
      have y2 : c y=true := (yes _).mpr (by simp [P])
      have y3 : c z=true := (yes _).mpr (by simp [P])
      simp only [P,mem_insert,mem_singleton] at vm
      rcases vm with rfl|rfl|rfl
      · exact exit_len_le_one G c cub xy zx.symm yz.ne y2 y3
      · exact exit_len_le_one G c cub xy.symm yz zx.ne.symm y1 y3
      · exact exit_len_le_one G c cub zx yz.symm xy.ne y1 y2
    calc
      _ ≤ ∑ _∈P,1 := sum_le_sum nz
      _ = 3 := by simp [size]
  rcases small c low with U|W
  · have e := U x y ((yes _).mpr (by simp [P])) ((yes _).mpr (by simp [P]))
    exact xy.ne e
  · let Q := (univ:Finset V)\P
    have cnt := card_sdiff_add_card_eq_card (subset_univ P)
    rw [card_univ,size] at cnt
    have two : 2≤Q.card := by
      change ((univ:Finset V)\P).card+3=Fintype.card V at cnt
      change 2≤((univ:Finset V)\P).card
      omega
    have once : Q.card≤1 := by
      apply card_le_one_iff.mpr
      intro a b ma mb
      exact W _ _ (by simpa [c] using (mem_sdiff.mp ma).2) (by simpa [c] using (mem_sdiff.mp mb).2)
    omega

#print axioms card_boundary_eq_exitSum
#print axioms triangle_free_of_small_trivial
end
end KelmansCactus.FourRingCutAux
