import RankOneTests180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem witness_core (G : SimpleGraph V) (r : V) (p : Bool) (A C Z : Finset V)
    (rc : r∈C) (con : Con G C) (dom : ∀ v∉C,Dominates G C v) (col : TwoColor G Z)
    (keep : A∩insert r (parity G r p)⊆Z)
    (pay : 1+(A∩parity G r p).card+C.card≤Z.card) : Protected G r p A := by
  classical
  let P := parity G r p
  have leaves := weightedCore G C (eligible A P r) con dom
  have eq : eligible A P r\C=(A∪P)\C := by
    ext x
    by_cases xr : x=r
    · subst x;simp [rc]
    · simp [eligible_iff,xr]
  rw [eq] at leaves
  have sum := card_union_add_card_inter A P
  have split := card_sdiff_add_card_inter (A∪P) C
  have cap := card_le_card (inter_subset_right (s₁:=A∪P) (s₂:=C))
  change 1+(A∩P).card+C.card≤Z.card at pay
  exact ⟨Z,col,keep,by change 1+A.card+P.card≤weightedLeaves G (eligible A P r)+Z.card;omega⟩

theorem dom_marked_odd (G : SimpleGraph V) (gc : G.Connected) {r y : V}
    (dom : DomEdge G r y) (A : Finset V) (ai : Indep G A) (ra : r∈A) : Protected G r true A := by
  classical
  let P := parity G r true
  have rp : r∉P := by simp [P,dist_self]
  have empty : A∩P=∅ := by
    apply eq_empty_iff_forall_not_mem.mpr
    intro x m
    obtain ⟨xa,xp⟩ := mem_inter.mp m
    have xr : x≠r := fun eq => rp (eq ▸ xp)
    have non := ai x xa r ra xr
    have xy := (dom.2 x xr (fun eq => non (eq ▸ dom.1.symm))).resolve_left non
    have up := gc.dist_triangle (u:=x) (v:=y) (w:=r)
    rw [dist_eq_one_iff_adj.mpr xy,dist_eq_one_iff_adj.mpr dom.1.symm] at up
    have ne := mt dist_eq_one_iff_adj.mp non
    have pos := gc.pos_dist_of_ne xr
    change x∈parity G r true at xp
    simp only [mem_parity,Bool.toNat_true] at xp
    omega
  have pins : A∩insert r P⊆{r} := by
    intro x xm
    obtain ⟨xa,xp⟩ := mem_inter.mp xm
    rcases mem_insert.mp xp with eq|pm
    · exact mem_singleton.mpr eq
    · have mem : x∈A∩P := mem_inter.mpr ⟨xa,pm⟩
      rw [empty] at mem;simp at mem
  by_cases hub : Universal G r
  · let Z := ({r}:Finset V)∪{y}
    have dis : Disjoint ({r}:Finset V) {y} := by simp [dom.1.ne.symm]
    have bi : TwoColor G Z := ⟨{r},{y},dis,rfl,by simp [Indep],by simp [Indep]⟩
    apply witness_core G r true A {r} Z (mem_singleton_self _) (con_single ..)
      (fun v out => ⟨r,mem_singleton_self _,hub v (by simpa using out)⟩) bi
      (pins.trans subset_union_left)
    change 1+(A∩P).card+_≤_
    simp only [Z,empty,card_empty,card_union_of_disjoint dis,card_singleton];omega
  · obtain ⟨z,zr,non⟩ : ∃ z,z≠r ∧ ¬G.Adj z r := by simpa [Substitution.Universal] using hub
    have zy : z≠y := fun eq => non (eq ▸ dom.1.symm)
    let Z := ({z,r}:Finset V)∪{y}
    have dis : Disjoint ({z,r}:Finset V) {y} := by simp [zy.symm,dom.1.ne.symm]
    have bi : TwoColor G Z := ⟨{z,r},{y},dis,rfl,pair_indep G non,by simp [Indep]⟩
    have rc : r∈({r,y}:Finset V) := mem_insert_self ..
    refine witness_core G r true A {r,y} Z rc (con_insert G (con_single G y) (mem_singleton_self _) dom.1) ?_ bi ?_ ?_
    · intro v out
      have ne : v≠r ∧ v≠y := by simpa using out
      exact (dom.2 v ne.1 ne.2).elim (fun e => ⟨r,rc,e⟩) (fun e => ⟨y,by simp,e⟩)
    · exact pins.trans (singleton_subset_iff.mpr (show r∈Z by simp [Z]))
    · change 1+(A∩P).card+_≤_
      simp only [Z,empty,card_empty,card_union_of_disjoint dis,card_pair zr,card_pair dom.1.ne,card_singleton];omega

/-- At an endpoint of a dominating edge the extra root can be required
with zero isolation credit, regardless of odd-cycle transversal number. -/
theorem dominating_protection (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    {r y : V} (dom : DomEdge G r y) (p : Bool) (A : Finset V) (ai : Indep G A) :
    Protected G r p A := by
  classical
  by_cases high : 2<Fintype.card V
  · by_cases extra : p=true ∧ r∈A
    · obtain ⟨rfl,ra⟩ := extra;exact dom_marked_odd G gc dom A ai ra
    obtain ⟨Z,col,keep,ok⟩ := dominating_pins G gc high dom p A ai
    refine ⟨Z,col,?_,ok⟩
    intro x xm
    obtain ⟨xa,xp⟩ := mem_inter.mp xm
    apply keep (mem_inter.mpr ⟨xa,?_⟩)
    rcases mem_insert.mp xp with xr|pm
    · subst x;cases p
      · simp [mem_parity,dist_self]
      · exact False.elim (extra ⟨rfl,xa⟩)
    · exact pm
  · exact protected_bip G gc hn (bip_of_short G hn (by omega)) r p A ai

#print axioms witness_core
#print axioms dom_marked_odd
#print axioms dominating_protection
end Minimal180.Transversals
