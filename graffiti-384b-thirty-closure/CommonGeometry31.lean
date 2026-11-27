import ThirtyFinish31

namespace Graffiti384b.OneCommon
open Finset SimpleGraph
open private ForcedCubics.third_contact from SharedSaving33
open private ThreeChoice.pair_turan from ThreeGeometry33
open private Repair.nbr_add Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure Board (G : SimpleGraph V) [DecidableRel G.Adj] where
  u : V
  s : V
  c : V
  du : G.degree u=3
  su : trianglesAt G u=2
  ds : G.degree s=3
  ss : trianglesAt G s=3
  sep : ¬G.Adj u s
  common : G.neighborFinset u∩G.neighborFinset s={c}

namespace Board
variable (M : Board G)
def U := (G.neighborFinset M.u).erase M.c
def L := (G.neighborFinset M.s).erase M.c
def B := G.neighborFinset M.u∪G.neighborFinset M.s
def W := (insert M.u (insert M.s M.B))ᶜ
def pins (x y : V) := (({M.c}:Finset V)∪M.U.erase x)∪M.L.erase y

theorem contacts : G.Adj M.u M.c ∧ G.Adj M.s M.c := by
  have m : M.c∈G.neighborFinset M.u∩G.neighborFinset M.s := M.common ▸ mem_singleton_self _
  exact ⟨(G.mem_neighborFinset ..).mp (mem_inter.mp m).1,(G.mem_neighborFinset ..).mp (mem_inter.mp m).2⟩

theorem sizes : M.U.card=2 ∧ M.L.card=2 := by
  obtain ⟨uc,sc⟩ := M.contacts
  simp [U,L,card_erase_of_mem ((G.mem_neighborFinset ..).mpr uc),
    card_erase_of_mem ((G.mem_neighborFinset ..).mpr sc),M.du,M.ds]

theorem dis : Disjoint M.U M.L := by
  apply disjoint_left.mpr; intro v vu vl
  have h := mem_inter.mpr ⟨(mem_erase.mp vu).2,(mem_erase.mp vl).2⟩
  rw [M.common,mem_singleton] at h
  exact (mem_erase.mp vu).1 h

theorem parts : ({M.c}:Finset V)∪M.U∪M.L=M.B := by
  ext v
  obtain ⟨uc,sc⟩ := M.contacts
  by_cases vc : v=M.c
  · subst v; simp [B,uc]
  · simp [U,L,B,vc]

theorem outside (v : V) : v∈M.W ↔ v≠M.u ∧ v≠M.s ∧ v∉M.B := by simp [W,not_or]

theorem pool_size (n : Fintype.card V=30) : M.W.card=23 := by
  have us : M.u≠M.s := by intro eq; have := M.su; rw [eq,M.ss] at this; contradiction
  have ui : M.u∉M.B := by simp [B,(show ¬G.Adj M.s M.u from fun h => M.sep h.symm)]
  have si : M.s∉M.B := by simp [B,M.sep]
  have bc := card_union_add_card_inter (G.neighborFinset M.u) (G.neighborFinset M.s)
  rw [M.common,card_singleton,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,M.du,M.ds] at bc
  change M.B.card+1=3+3 at bc
  rw [W,card_compl,card_insert_of_not_mem (show M.u∉insert M.s M.B by simp [us,ui]),
    card_insert_of_not_mem si,n]; omega

theorem pin_count (v x y : V) :
    nbr G v (M.pins x y)=(nbr G v {M.c}+nbr G v (M.U.erase x))+nbr G v (M.L.erase y) := by
  have cu : Disjoint {M.c} M.U := by simp [U]
  have cl : Disjoint {M.c} M.L := by simp [L]
  rw [pins,Repair.nbr_add G v (disjoint_union_left.mpr ⟨cl.mono_right (erase_subset ..),
    M.dis.mono (erase_subset ..) (erase_subset ..)⟩),Repair.nbr_add G v (cu.mono_right (erase_subset ..))]

theorem pin_subset (x y : V) : M.pins x y⊆M.B := by
  rw [←M.parts]; exact union_subset_union (union_subset_union Subset.rfl (erase_subset ..)) (erase_subset ..)

theorem split (x y : V) (xm : x∈M.U) (ym : y∈M.L) :
    M.B=M.pins x y∪{x,y} := by
  rw [←M.parts,pins]; ext z
  simp only [mem_union,mem_singleton,mem_erase,mem_insert]
  by_cases a : z=x <;> by_cases b : z=y <;> simp_all

theorem pool_score {w : V} (wm : w∈M.W)
    (cover : ∀ C,G.IsNClique 5 C → 3≤(C∩M.B).card) :
    let b := nbr G w M.W
    let h := nbr G w {M.c}+nbr G w M.U+nbr G w M.L
    trianglesAt G w≤(b+h).choose 2 ∧
      (h≤2 → b+h≤10 → trianglesAt G w≤RankTable.cap (b+h) 3) := by
  classical
  let N := G.neighborFinset w
  have wu : ¬G.Adj w M.u := fun e => ((M.outside w).mp wm).2.2 (mem_union_left _ ((G.mem_neighborFinset ..).mpr e.symm))
  have ws : ¬G.Adj w M.s := fun e => ((M.outside w).mp wm).2.2 (mem_union_right _ ((G.mem_neighborFinset ..).mpr e.symm))
  have wb : Disjoint M.W M.B := disjoint_left.mpr (fun z zm => ((M.outside z).mp zm).2.2)
  have eq : (M.W∪M.B).filter (G.Adj w)=N := by
    ext z; simp only [N,mem_filter,mem_neighborFinset]
    constructor
    · exact And.right
    · intro wz
      by_cases zb : z∈M.B
      · exact ⟨mem_union_right _ zb,wz⟩
      · exact ⟨mem_union_left _ ((M.outside z).mpr ⟨fun h => wu (h ▸ wz),fun h => ws (h ▸ wz),zb⟩),wz⟩
  have sum : nbr G w (M.W∪M.B)=G.degree w := (congrArg card eq).trans (card_neighborFinset_eq_degree ..)
  have cu : Disjoint {M.c} M.U := by simp [U]
  have cl : Disjoint {M.c} M.L := by simp [L]
  have bs : nbr G w M.B=nbr G w {M.c}+nbr G w M.U+nbr G w M.L := by
    rw [←M.parts,Repair.nbr_add G w (disjoint_union_left.mpr ⟨cl,M.dis⟩),Repair.nbr_add G w cu]
  rw [Repair.nbr_add G w wb,bs] at sum
  refine ⟨(sum.symm ▸ Repair.triangles_le_choose G w),?_⟩
  intro small dsmall
  have free (Q : Finset V) (sub : Q⊆N) (clique : G.IsNClique (3+1) Q) : False := by
    have five := clique.insert (fun z zm => (G.mem_neighborFinset ..).mp (sub zm))
    have many := cover _ five
    have inc : (insert w Q)∩M.B⊆M.B.filter (G.Adj w) := by
      intro z zm; obtain ⟨zq,zb⟩ := mem_inter.mp zm
      have ne : z≠w := fun h => ((M.outside w).mp wm).2.2 (h ▸ zb)
      exact mem_filter.mpr ⟨zb,(G.mem_neighborFinset ..).mp (sub ((mem_insert.mp zq).resolve_left ne))⟩
    have up : 3≤nbr G w M.B := many.trans (card_le_card inc)
    omega
  have hi := ThreeChoice.pair_turan G N (by decide : 0<3) free
  have ns : N.card=G.degree w := card_neighborFinset_eq_degree ..
  change trianglesAt G w≤_ at hi
  rw [ns,←sum] at hi
  exact hi.trans_eq (RankTable.cap_table ⟨_,by omega⟩ ⟨3,by decide⟩ (by decide))

end Board
end Graffiti384b.OneCommon
#print axioms Graffiti384b.OneCommon.Board.pool_score
#print axioms Graffiti384b.OneCommon.Board.pool_size
