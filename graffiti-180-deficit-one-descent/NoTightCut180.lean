import MarkedFork180

set_option warningAsError true
namespace Minimal180.DescentOne
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- If deletion of a port leaves an odd obstruction, every independent
set misses both ends of some edge avoiding that port. -/
theorem missed_edge (J : SimpleGraph V) {I : Finset V} (ind : Indep J I) (t : V)
    (odd : ¬TwoColor J (univ.erase t)) : ∃ a b, J.Adj a b ∧ a∉I ∧ b∉I ∧ a≠t ∧ b≠t := by
  classical
  by_contra! no
  apply odd
  apply (color_function J _).mpr
  refine ⟨fun i => decide (i∈I),?_⟩
  intro a am b bm e
  have atip := (mem_erase.mp am).1
  have btip := (mem_erase.mp bm).1
  by_cases ai : a∈I <;> by_cases bi : b∈I
  · exact (ind a ai b bi e.ne e).elim
  · simp [ai,bi]
  · simp [ai,bi]
  · exact (btip (no a b e ai bi atip)).elim

/-- Lower bipartization deficit one is incompatible with the full tight
rooted-sparse horizontal cut-triangle hypotheses. This eliminates even
the apparent doubly marked equality case. -/
theorem no_tight_cut_one {J : SimpleGraph V} {S T : Finset V} {x y w : V}
    {r : ↥S} {odd : Bool} {A : Finset V} (one : bipartiteNum J+1=Fintype.card V) :
    ¬TightCut J S T x y w r odd A := by
  classical
  intro h
  let G := J⊔edge x y
  let P := parity G r.val odd
  let U := eligible A P r.val
  have gain := deficit_one_cut_gain h one
  obtain ⟨criterion,collapse⟩ := h.defect_one_gain_iff one
  have marked := criterion.mp gain
  have eq : A=P := collapse marked
  have wm : w∈A := (mem_union.mp marked).elim id (fun p => eq ▸ p)
  have mask : U=A := by
    change eligible A P r.val=A
    rw [←eq]
    ext i
    constructor
    · intro v; exact (eligible_iff.mp v).1.elim id id
    · intro v
      apply eligible_iff.mpr
      by_cases ir : i=r.val
      · exact ⟨Or.inl v,Or.inr ⟨ir ▸ v,ir ▸ v⟩⟩
      · exact ⟨Or.inl v,Or.inl ir⟩
  have tight := h.tight
  change weightedLeaves J U+bipartiteNum J=1+A.card+P.card at tight
  rw [mask,←eq] at tight
  have jr := h.rank
  have drop : bipartiteNum G<bipartiteNum J := by change bipartiteNum J=bipartiteNum G+1 at jr; omega
  have missing {t : V} (tip : t=x ∨ t=y) : ¬TwoColor J (univ.erase t) := by
    intro color
    have size := card_erase_add_one (mem_univ t)
    rw [card_univ] at size
    have top : MaxSet J (univ.erase t) := ⟨color,by omega⟩
    have pins := locked_seam h.split h.nearTip h.outsideNear h.distinct drop top
    rcases tip with rfl|rfl
    · exact (mem_erase.mp pins.1).1 rfl
    · exact (mem_erase.mp pins.2.2).1 rfl
  obtain ⟨z,wz,zx,zy⟩ := third_seam_neighbor h.connected h.order h.split h.nearTip h.outsideFar
    h.farTip h.outsideNear h.leftSpoke h.rightSpoke h.block h.sparse
  have ai : Indep J A := fun i ia j ja ne e => h.independent i ia j ja ne (Or.inl e)
  have find {t v : V} (tip : t=x ∨ t=y) (vz : ¬J.Adj v z) :
      ∃ a b, J.Adj a b ∧ a∉A ∧ b∉A ∧ a∉({t,v,z}:Finset V) := by
    obtain ⟨a,b,ab,am,bm,atip,btip⟩ := missed_edge J ai t (missing tip)
    by_cases ain : a∈({t,v,z}:Finset V)
    · refine ⟨b,a,ab.symm,bm,am,?_⟩
      intro bin
      simp only [mem_insert,mem_singleton] at ain bin
      rcases ain.resolve_left atip with av|az <;> rcases bin.resolve_left btip with bv|bz
      · exact ab.ne (av.trans bv.symm)
      · exact vz (av ▸ bz ▸ ab)
      · exact vz (bv ▸ az ▸ ab.symm)
      · exact ab.ne (az.trans bz.symm)
    · exact ⟨a,b,ab,am,bm,ain⟩
  have extra : ∃ a b, J.Adj a b ∧ a∉A ∧ b∉A ∧ a∉({x,y,z}:Finset V) := by
    rcases h.split.either z with zs|zt
    · have no : ¬J.Adj y z := by
        intro e
        rcases h.split.edges e with l|q
        · exact h.outsideNear l.1
        · exact wz.ne.symm (h.split.common zs q.2)
      exact find (Or.inl rfl : x=x ∨ x=y) no
    · have no : ¬J.Adj x z := by
        intro e
        rcases h.split.edges e with l|q
        · exact wz.ne.symm (h.split.common l.2 zt)
        · exact h.outsideFar q.1
      obtain ⟨a,b,ab,am,bm,off⟩ := find (Or.inr rfl : y=x ∨ y=y) no
      exact ⟨a,b,ab,am,bm,by simpa only [insert_comm x y] using off⟩
  obtain ⟨a,b,ab,am,bm,off⟩ := extra
  have low := marked_fork J h.connected (by have := h.order; omega) A ai wm h.leftSpoke.symm h.rightSpoke wz h.distinct zx zy ab am bm off
  omega

#print axioms missed_edge
#print axioms no_tight_cut_one
end Minimal180.DescentOne
