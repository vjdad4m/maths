import LargeIndependentEars384b
import LargeSingleLowEdge384b
import PositiveSplit384b

namespace Graffiti384b.DiversityEleven
open Finset SimpleGraph
open private TrianglePrune.Closed from TrianglePrune384b
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem low_degree {x : V} (h : x∈nonleaves G \ high G) : G.degree x=2 := by
  obtain ⟨xn,xh⟩ := mem_sdiff.mp h
  have up : ¬3≤G.degree x := fun d => xh (mem_filter.mpr ⟨mem_univ _,d⟩)
  have dn := (mem_filter.mp xn).2
  omega

private theorem whole_neighbors {u x y : V} (d : G.degree u=2)
    (ux : G.Adj u x) (uy : G.Adj u y) (xy : x≠y) :
    G.neighborFinset u = {x,y} := by
  symm
  apply eq_of_subset_of_card_le
  · exact insert_subset ((G.mem_neighborFinset ..).mpr ux)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr uy))
  · rw [card_pair xy,card_neighborFinset_eq_degree,d]

private theorem triangle_low_exact (sup : Supported G)
    {a b c : V} (ab : G.Adj a b) (ac : G.Adj a c) (bc : G.Adj b c)
    (al : a∈nonleaves G \ high G) (bl : b∈nonleaves G \ high G)
    (cl : c∈nonleaves G \ high G) : gamma G≤bound G := by
  classical
  let C : Finset V := {a,b,c}
  have na := whole_neighbors G (low_degree G al) ab ac bc.ne
  have nb := whole_neighbors G (low_degree G bl) ab.symm bc ac.ne
  have nc := whole_neighbors G (low_degree G cl) ac.symm bc.symm ab.ne
  have sep : TrianglePrune.Closed G C := by
    intro x xm y xy
    have mem := (G.mem_neighborFinset ..).mpr xy
    have xm' : x=a ∨ x=b ∨ x=c := by simpa [C] using xm
    rcases xm' with h|h|h
    · subst x
      rw [na,mem_insert,mem_singleton] at mem
      exact mem_insert.mpr (Or.inr (by simpa using mem))
    · subst x
      rw [nb,mem_insert,mem_singleton] at mem
      exact mem_insert.mpr (mem.elim Or.inl
        (fun h=>Or.inr (mem_insert.mpr (Or.inr (mem_singleton.mpr h)))))
    · subst x
      rw [nc,mem_insert,mem_singleton] at mem
      exact mem_insert.mpr (mem.elim Or.inl
        (fun h=>Or.inr (mem_insert.mpr (Or.inl h))))
  have comp : TrianglePrune.Closed G Cᶜ := by
    intro x xm y xy
    exact mem_compl.mpr (fun ym => (mem_compl.mp xm) (sep y ym x xy.symm))
  have score {x : V} (xl : x∈nonleaves G \ high G) : trianglesAt G x=1 := by
    have top := Repair.triangles_le_choose G x
    rw [low_degree G xl] at top
    have norm : Nat.choose 2 2=1 := by decide
    rw [norm] at top
    have pos := positive_of_nonleaf G sup (mem_sdiff.mp xl).1
    omega
  have pal : C.image (trianglesAt G)={1} := by
    ext n
    constructor
    · intro nm
      obtain ⟨x,xm,rfl⟩ := mem_image.mp nm
      have xx : x=a ∨ x=b ∨ x=c := by simpa [C] using xm
      rcases xx with rfl|rfl|rfl
      · exact mem_singleton.mpr (score al)
      · exact mem_singleton.mpr (score bl)
      · exact mem_singleton.mpr (score cl)
    · intro nm
      exact mem_image.mpr ⟨a,by simp [C],(score al).trans (mem_singleton.mp nm).symm⟩
  apply exact_of_positive_split G (A:=C) (B:=Cᶜ)
    (Finset.disjoint_left.mpr (fun _ am bm => (mem_compl.mp bm) am)) sep comp
    (fun x _=>by simp)
  left
  simp [localPositive,pal]

private theorem low_pair_shape (sup : Supported G) (bad : bound G<gamma G)
    {x y : V} (xl : x∈nonleaves G \ high G) (yl : y∈nonleaves G \ high G)
    (xy : G.Adj x y) :
    ∃ z∈high G, G.neighborFinset x={y,z} ∧ G.neighborFinset y={x,z} := by
  obtain ⟨z,xz,yz⟩ := sup xy
  have nzx := whole_neighbors G (low_degree G xl) xy xz yz.ne
  have nzy := whole_neighbors G (low_degree G yl) xy.symm yz xz.ne
  have nz : z∈nonleaves G := by
    have sub : ({x,y} : Finset V)⊆G.neighborFinset z := insert_subset
      ((G.mem_neighborFinset ..).mpr xz.symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset ..).mpr yz.symm))
    have d := card_le_card sub
    rw [card_pair xy.ne,card_neighborFinset_eq_degree] at d
    exact mem_filter.mpr ⟨mem_univ _,d⟩
  by_cases zh : z∈high G
  · exact ⟨z,zh,nzx,nzy⟩
  · exact (not_le_of_gt bad (triangle_low_exact G sup xy xz yz xl yl
        (mem_sdiff.mpr ⟨nz,zh⟩))).elim

/-- In a failing lower profile all low-low edges, if present, are one and
the same pendant pair. -/
theorem low_edge_unique (sup : Supported G)
    (t : (types G).card=11) (nine : (high G).card=9) (bad : bound G<gamma G)
    {x y a b : V} (xl : x∈nonleaves G \ high G) (yl : y∈nonleaves G \ high G)
    (al : a∈nonleaves G \ high G) (bl : b∈nonleaves G \ high G)
    (xy : G.Adj x y) (ab : G.Adj a b) : (a=x ∧ b=y) ∨ (a=y ∧ b=x) := by
  classical
  obtain ⟨z,zh,nx,ny⟩ := low_pair_shape G sup bad xl yl xy
  have unique {u v w : V} (v0 : v∉high G)
      (n : G.neighborFinset u={w,z}) (uv : G.Adj u v) : v=w := by
    have m := (G.mem_neighborFinset ..).mpr uv
    rw [n,mem_insert,mem_singleton] at m
    exact m.resolve_right (fun h=>v0 (h ▸ zh))
  by_cases ax : a=x
  · exact Or.inl ⟨ax,unique (mem_sdiff.mp bl).2 nx (ax ▸ ab)⟩
  by_cases ay : a=y
  · exact Or.inr ⟨ay,unique (mem_sdiff.mp bl).2 ny (ay ▸ ab)⟩
  obtain ⟨w,wh,na,_⟩ := low_pair_shape G sup bad al bl ab
  have xa : ¬G.Adj x a := fun h=>ay (unique (mem_sdiff.mp al).2 nx h)
  have low : Disjoint ({x,a} : Finset V) (high G) := by
    refine Finset.disjoint_left.mpr (fun v vm vh => ?_)
    rcases (show v=x ∨ v=a by simpa using vm) with rfl|rfl
    · exact (mem_sdiff.mp xl).2 vh
    · exact (mem_sdiff.mp al).2 vh
  have dg : ∀v∈({x,a} : Finset V),2≤G.degree v := by
    intro v vm
    rcases (show v=x ∨ v=a by simpa using vm) with rfl|rfl
    · exact (low_degree G xl).ge
    · exact (low_degree G al).ge
  have ind : ∀v∈({x,a} : Finset V),∀u∈({x,a} : Finset V),¬G.Adj v u := by
    intro v vm u um
    have vm' : v=x ∨ v=a := by simpa using vm
    have um' : u=x ∨ u=a := by simpa using um
    rcases vm' with h|h <;> subst v <;> rcases um' with h|h <;> subst u
    · exact G.loopless _
    · exact xa
    · exact fun h=>xa h.symm
    · exact G.loopless _
  have tP : ∀ v∈high G,(∃e∈({x,a} : Finset V),G.Adj e v)→v∈({z,w} : Finset V) := by
    intro v vh h
    obtain ⟨e,em,ev⟩ := h
    have n := (G.mem_neighborFinset ..).mpr ev
    rcases (show e=x ∨ e=a by simpa using em) with rfl|rfl
    · rw [nx,mem_insert,mem_singleton] at n
      exact mem_insert.mpr (Or.inl (n.resolve_left (fun q=>(mem_sdiff.mp yl).2 (q ▸ vh))))
    · rw [na,mem_insert,mem_singleton] at n
      exact mem_insert.mpr (Or.inr (mem_singleton.mpr
        (n.resolve_left (fun q=>(mem_sdiff.mp bl).2 (q ▸ vh)))))
  have c := card_insert_le z ({w} : Finset V)
  rw [card_singleton] at c
  have win := exact_of_ear_footprint G t nine low dg ind tP
    (by rw [card_pair (Ne.symm ax)]; omega)
  exact (not_le_of_gt bad win).elim

/-- The 14- and 15-nonleaf ranges of the nine-high supported lower profile
are exact at diversity eleven. -/
theorem exact_large_lower_profile (sup : Supported G)
    (t : (types G).card=11) (nine : (high G).card=9)
    (large : 14≤(nonleaves G).card) : gamma G≤bound G := by
  by_contra! bad
  by_cases has : ∃x∈nonleaves G \ high G,∃y∈nonleaves G \ high G,G.Adj x y
  · obtain ⟨x,xl,y,yl,xy⟩ := has
    have win := exact_large_single_low_edge G sup t nine large xy xl yl
      (fun a al b bl ab=>low_edge_unique G sup t nine bad xl yl al bl xy ab)
    exact not_le_of_gt bad win
  · exact not_le_of_gt bad (exact_at_least_fourteen_of_independent_ears G sup t nine large
      (fun x xl y yl xy=>has ⟨x,xl,y,yl,xy⟩))

#print axioms low_edge_unique
#print axioms exact_large_lower_profile
end Graffiti384b.DiversityEleven
