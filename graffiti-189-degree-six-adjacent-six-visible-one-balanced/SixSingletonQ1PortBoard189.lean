import SixSingletonQ1Labels189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph Finset
open private Cmp from SixCutFar189
open private Vis from AdjacentCutFiveComponents189
open private Dark Common from SixSingletonGeometry189
open private EA EB from SixSingletonMultiZeroGeom189
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b s : V} {D : Cmp G a b}
set_option linter.unusedSectionVars false

structure Q1PortBoard (D : Cmp G a b) (s : V) (nleft : ℕ) where
  label : Fin 9→V
  aEq : label 6=a
  bEq : label 7=b
  sEq : label 8=s
  portImage : univ.image (fun i : Fin 6=>label (widenQ1 (by decide : 6≤9) i))=Vis D
  left : ∀ i : Fin 6, (i.val < nleft) → label (widenQ1 (by decide : 6≤9) i) ∈ EA D
  right : ∀ i : Fin 6, (nleft ≤ i.val) → (i.val < nleft + 2) → label (widenQ1 (by decide : 6≤9) i) ∈ EB D
  common : ∀ i : Fin 6, (nleft + 2 ≤ i.val) → label (widenQ1 (by decide : 6≤9) i) ∈ Common D

private theorem common_count (F : SixVisibleData G D s) :
    (EA D).card+(EB D).card+(Common D).card=(Vis D).card := by
  have eab : Disjoint (EA D) (EB D) := disjoint_left.mpr (fun _ h j=>(mem_sdiff.mp h).2 (mem_sdiff.mp j).1)
  have ck : Disjoint (EA D∪EB D) (Common D) := by
    apply disjoint_left.mpr
    intro x hz zk
    rcases mem_union.mp hz with u|v
    · exact (mem_sdiff.mp u).2 (mem_inter.mp zk).2
    exact (mem_sdiff.mp v).2 (mem_inter.mp zk).1
  rw [←F.visiblePart,card_union_of_disjoint ck,card_union_of_disjoint eab]

theorem q1_port_board_one (F : SixVisibleData G D s) (v6 : (Vis D).card=6)
    (ea : (EA D).card=1) (eb : (EB D).card=2) : Nonempty (Q1PortBoard D s 1) := by
  classical
  have kc : (Common D).card=3 := by have h:=common_count F; omega
  obtain ⟨x,xs⟩ := card_eq_one.mp ea
  obtain ⟨y,y',_,ys⟩ := card_eq_two.mp eb
  obtain ⟨c,c',c'',_,_,_,cs⟩ := card_eq_three.mp kc
  let q : Fin 9→V := ![x,y,y',c,c',c'',a,b,s]
  refine ⟨⟨q,rfl,rfl,rfl,?_,?_,?_,?_⟩⟩
  · rw [←F.visiblePart,xs,ys,cs]
    ext w
    rw [mem_image]
    simp only [mem_univ,true_and,mem_union,mem_insert,mem_singleton]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp [q,widenQ1]
    rintro ((h|h|h)|h|h|h)
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
    · exact ⟨3,h.symm⟩
    · exact ⟨4,h.symm⟩
    exact ⟨5,h.symm⟩
  · intro i hi
    fin_cases i <;> dsimp at hi <;> first | omega | simp [q,widenQ1,xs]
  · intro i li hi
    fin_cases i <;> dsimp at hi li <;> first | omega | simp [q,widenQ1,ys]
  · intro i li
    fin_cases i <;> dsimp at li <;> first | omega | simp [q,widenQ1,cs]

theorem q1_port_board_two (F : SixVisibleData G D s) (v6 : (Vis D).card=6)
    (ea : (EA D).card=2) (eb : (EB D).card=2) : Nonempty (Q1PortBoard D s 2) := by
  classical
  have kc : (Common D).card=2 := by have h:=common_count F; omega
  obtain ⟨x,x',_,xs⟩ := card_eq_two.mp ea
  obtain ⟨y,y',_,ys⟩ := card_eq_two.mp eb
  obtain ⟨c,c',_,cs⟩ := card_eq_two.mp kc
  let q : Fin 9→V := ![x,x',y,y',c,c',a,b,s]
  refine ⟨⟨q,rfl,rfl,rfl,?_,?_,?_,?_⟩⟩
  · rw [←F.visiblePart,xs,ys,cs]
    ext w
    rw [mem_image]
    simp only [mem_univ,true_and,mem_union,mem_insert,mem_singleton]
    constructor
    · rintro ⟨i,rfl⟩
      fin_cases i <;> simp [q,widenQ1]
    rintro (((h|h)|(h|h))|(h|h))
    · exact ⟨0,h.symm⟩
    · exact ⟨1,h.symm⟩
    · exact ⟨2,h.symm⟩
    · exact ⟨3,h.symm⟩
    · exact ⟨4,h.symm⟩
    exact ⟨5,h.symm⟩
  · intro i hi
    fin_cases i <;> dsimp at hi <;> first | omega | simp [q,widenQ1,xs]
  · intro i li hi
    fin_cases i <;> dsimp at hi li <;> first | omega | simp [q,widenQ1,ys]
  · intro i li
    fin_cases i <;> dsimp at li <;> first | omega | simp [q,widenQ1,cs]

#print axioms q1_port_board_one
#print axioms q1_port_board_two
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
