import RankOneTests180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem failed_cost (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A X : Finset V) (ai : Indep G A) (bi : TwoColor G (univ\X))
    (bad : ¬Protected G r p A) :
    let K := A∩insert r (parity G r p)
    2*allowance G r p A+2≤2*(X\K).card+(repairNeighbors G X K).card := by
  intro K
  have ki : Indep G K := fun x xm y ym => ai x (mem_inter.mp xm).1 y (mem_inter.mp ym).1
  obtain ⟨Z,col,keep,cap⟩ := transversal_repair G X K ki bi
  have insufficient : ¬Fintype.card V-Z.card≤allowance G r p A :=
    fun pay => bad ((protected_iff G gc hn r p A ai).mpr ⟨Z,col,keep,pay⟩)
  omega

omit [Fintype V] in
theorem pair_free (a b : V) (K : Finset V) (ak : a∈K) (bk : b∉K) : ({a,b}:Finset V)\K={b} := by
  ext x
  by_cases eq : x=b <;> simp [eq,bk,ak]
  aesop

theorem solo_neighbors (G : SimpleGraph V) (a b : V) (K : Finset V) (bk : b∉K) :
    repairNeighbors G {a,b} K⊆(G.neighborFinset a).erase b := by
  intro y ym
  obtain ⟨outside,x,xm,ed⟩ := mem_filter.mp ym
  have pair := (mem_inter.mp xm).1
  have xa := (mem_insert.mp pair).resolve_right (fun m => bk (mem_singleton.mp m ▸ (mem_inter.mp xm).2))
  exact mem_erase.mpr ⟨fun eq => (mem_sdiff.mp outside).2 (mem_insert_of_mem (mem_singleton.mpr eq)),
    (G.mem_neighborFinset _ _).mpr (xa ▸ ed)⟩

/-- Necessary alternatives for every two-vertex transversal at a failed
uncredited marking. The neighborhood overlap counts common neighbors. -/
theorem pair_obstruction (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (bad : ¬Protected G r p A)
    (a b : V) (ab : a≠b) (bi : TwoColor G (univ\{a,b})) :
    let K := A∩insert r (parity G r p)
    let c := (G.neighborFinset a∩G.neighborFinset b).card
    ¬G.Adj a b ∧ ((a∈K ∧ b∉K ∧ G.degree a=4) ∨
      (b∈K ∧ a∉K ∧ G.degree b=4) ∨
      (a∈K ∧ b∈K ∧ G.degree a+c≤G.degree b+2 ∧ G.degree b+c≤G.degree a+2 ∧
       6≤(G.neighborFinset a∪G.neighborFinset b).card)) := by
  classical
  intro K c
  let X : Finset V := {a,b}
  let B := allowance G r p A
  have high : 2<Fintype.card V := by
    by_contra! small
    exact bad (protected_bip G gc hn (bip_of_short G hn small) r p A ai)
  have notOne : bipartiteNum G+1<Fintype.card V := by
    by_contra! small
    exact bad (protected_rank_one G gc hn small r p A ai)
  have rank : Fintype.card V≤bipartiteNum G+2 := by
    have count := card_sdiff_add_card_eq_card (subset_univ X)
    have sz := size_bip G bi
    change (univ\X).card≤bipartiteNum G at sz
    rw [card_univ,show X.card=2 from card_pair ab] at count
    omega
  have min : 2≤B := by have := rank_allowance G gc hn rank r p A ai;change 2≤allowance G r p A;omega
  have cost := failed_cost G gc hn r p A X ai bi bad
  change 2*B+2≤2*(X\K).card+(repairNeighbors G X K).card at cost
  have lim {x : V} (xm : x∈K) : G.degree x-2≤B := protected_degree G gc high r x p A ai xm
  have solo {x y : V} (eq : X={x,y}) (xm : x∈K) (ym : y∉K) : G.degree x=4 ∧ ¬G.Adj x y := by
    have cap := card_le_card (solo_neighbors G x y K ym)
    have del := card_le_card (erase_subset y (G.neighborFinset x))
    rw [card_neighborFinset_eq_degree] at del
    have co := cost
    rw [eq,pair_free x y K xm ym,card_singleton] at co
    have bound := lim xm
    have four : G.degree x=4 := by omega
    refine ⟨four,fun ed => ?_⟩
    have exactCount := card_erase_add_one ((G.mem_neighborFinset x y).mpr ed)
    rw [card_neighborFinset_eq_degree] at exactCount;omega
  by_cases am : a∈K <;> by_cases bm : b∈K
  · have nedge : ¬G.Adj a b := ai a (mem_inter.mp am).1 b (mem_inter.mp bm).1 ab
    have empty : X\K=∅ := sdiff_eq_empty_iff_subset.mpr (insert_subset am (singleton_subset_iff.mpr bm))
    rw [empty,card_empty,Nat.mul_zero,zero_add] at cost
    have sub : repairNeighbors G X K⊆G.neighborFinset a∪G.neighborFinset b := by
      intro y ym
      obtain ⟨x,xm,e⟩ := (mem_filter.mp ym).2
      rcases mem_insert.mp (mem_inter.mp xm).1 with xa|xb
      · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr (xa ▸ e))
      · exact mem_union_right _ ((G.mem_neighborFinset _ _).mpr (mem_singleton.mp xb ▸ e))
    have cap := card_le_card sub
    have sz := card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
    rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at sz
    change (G.neighborFinset a∪G.neighborFinset b).card+c=G.degree a+G.degree b at sz
    have la := lim am
    have lb := lim bm
    exact ⟨nedge,Or.inr (Or.inr ⟨am,bm,by omega,by omega,by omega⟩)⟩
  · obtain ⟨four,no⟩ := solo rfl am bm
    exact ⟨no,Or.inl ⟨am,bm,four⟩⟩
  · obtain ⟨four,no⟩ := solo (pair_comm a b) bm am
    exact ⟨fun e => no e.symm,Or.inr (Or.inl ⟨bm,am,four⟩)⟩
  · have empty : repairNeighbors G X K=∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro y ym
      obtain ⟨x,xm,_⟩ := (mem_filter.mp ym).2
      obtain ⟨xx,xk⟩ := mem_inter.mp xm
      rcases mem_insert.mp xx with xa|xb
      · exact am (xa ▸ xk)
      · exact bm (mem_singleton.mp xb ▸ xk)
    have le := card_le_card (sdiff_subset (s:=X) (t:=K))
    rw [show X.card=2 from card_pair ab] at le
    rw [empty,card_empty] at cost;omega

#print axioms failed_cost
#print axioms solo_neighbors
#print axioms pair_obstruction
end Minimal180.Transversals
