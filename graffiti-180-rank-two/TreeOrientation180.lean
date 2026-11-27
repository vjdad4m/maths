import TwoPorts180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Orienting a finite tree toward an arbitrary base gives every nonbase
vertex a unique descending neighbor and accounts for every edge. -/
theorem orient_tree (T : SimpleGraph V) (tree : T.IsTree) (r : V) :
    ∃ p : V→V, (∀ v≠r,Arc T r (p v) v) ∧
      ∀ a b, T.Adj a b → (a≠r ∧ p a=b) ∨ (b≠r ∧ p b=a) := by
  classical
  obtain ⟨p,spec,_⟩ := parent_edge_count T tree r (univ : Finset V)
  let f (v : V) := s(v,p v)
  have inj {i j} (ir : i≠r) (jr : j≠r) (same : f i=f j) : i=j := by
    rcases Sym2.eq_iff.mp same with h|⟨h,k⟩
    · exact h.1
    · have a := (spec i ir).2
      have b := (spec j jr).2
      rw [k] at a
      rw [← h] at b
      omega
  have sub : (univ.erase r).image f⊆T.edgeFinset := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := mem_image.mp he
    exact mem_edgeFinset.mpr (spec i (mem_erase.mp hi).1).1
  have card := card_image_of_injOn (s:=univ.erase r) (f:=f)
    (fun i hi j hj equ => inj (mem_erase.mp hi).1 (mem_erase.mp hj).1 equ)
  have erase := card_erase_add_one (mem_univ r)
  rw [card_univ] at erase
  have all := eq_of_subset_of_card_le sub (by have := tree.card_edgeFinset; omega)

  have edge (a b : V) (ab : T.Adj a b) : (a≠r ∧ p a=b) ∨ (b≠r ∧ p b=a) := by
    have m : s(a,b)∈T.edgeFinset := mem_edgeFinset.mpr ab
    rw [←all] at m
    obtain ⟨i,im,pair⟩ := mem_image.mp m
    rcases Sym2.eq_iff.mp pair with ⟨ia,ib⟩|⟨ib,ia⟩
    · subst a; exact Or.inl ⟨(mem_erase.mp im).1,ib⟩
    · subst b; exact Or.inr ⟨(mem_erase.mp im).1,ia⟩
  refine ⟨p,fun v vr => ⟨(spec v vr).1.symm,(spec v vr).2,?_⟩,edge⟩
  intro z zv d
  rcases edge v z zv.symm with a|b
  · exact a.2.symm
  · have dz := (spec z b.1).2
    rw [b.2] at dz
    omega

/-- Some singly marked vertex has a neighbor missed by both marks. -/
theorem free_attachment {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V}
    (h : FailedTwo G r odd A) :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    ∃ t∈D, ∃ w, G.Adj t w ∧ w∉A∪P := by
  classical
  intro P D
  have overlap : ¬Disjoint A P := fun dis =>
    (Nat.not_lt_of_ge (disjoint_marks G h.connected h.block h.order h.rank r odd A h.independent dis)) h.bad
  obtain ⟨v,va,vp⟩ := Finset.not_disjoint_iff.mp overlap
  have vd : v∉D := fun m => (mem_sdiff.mp m).2 (mem_inter.mpr ⟨va,vp⟩)
  obtain ⟨w,wm,low⟩ := exists_min_image (univ\D) (fun z => G.dist z r) ⟨v,mem_sdiff.mpr ⟨mem_univ _,vd⟩⟩
  have wd := (mem_sdiff.mp wm).2
  have wr : w≠r := fun eq => wd (eq ▸ (show r∈D from h.root_disagreement))
  obtain ⟨t,wt,dw⟩ := Graffiti169.exists_predecessor G h.connected r w wr
  have td : t∈D := by
    apply Classical.byContradiction
    intro no
    have le := low t (mem_sdiff.mpr ⟨mem_univ _,no⟩)
    omega
  have flip : t∈P ↔ w∉P := (vertical_adj wt.symm dw odd).2
  have no : ¬(t∈A ∧ w∈A) := fun m => h.independent t m.1 w m.2 wt.ne.symm wt.symm
  refine ⟨t,td,w,wt.symm,?_⟩
  change w∉(A∪P)\(A∩P) at wd
  have mt := mem_sdiff.mp td
  simp only [mem_sdiff,mem_union,mem_inter] at wd mt ⊢
  tauto

#print axioms orient_tree
#print axioms free_attachment
end Minimal180.RootEar
