import TwoLeafBudget

namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {X : Set V} {z r a b x y : V}

/-- In the singleton cut with a traceable singleton deletion, two distinct
ports each missing at most one ordinary vertex imply traceability. -/
theorem SingletonCut.traceable_of_two_almost_complete (F : SingletonCut G X z r a b)
    (P : PathOn G {v | v ≠ z}) (one : ∀ w ∈ X, ¬ G.Adj r w → w = x)
    (two : ∀ w ∈ X, ¬ G.Adj a w → w = y) : Traceable G := by
  classical
  by_contra no
  let B := F.swap_first_two
  obtain ⟨xX,rx,xa,xb,dx⟩ := F.unique_miss_degree_and_contacts no P one
  obtain ⟨yX,ay,yr,yb,dy⟩ := B.unique_miss_degree_and_contacts no P two
  have xy : x ≠ y := fun e => ay (e ▸ xa.symm)
  have xmem : x ∈ P.terminalQuartet := by
    obtain ⟨m,hm,off⟩ := F.misses_flank no P (Finset.mem_insert_self r _)
    exact one m (F.flanks_in_shore no P m hm) off ▸ hm
  have ymem : y ∈ P.terminalQuartet := by
    obtain ⟨m,hm,off⟩ := B.misses_flank no P (Finset.mem_insert_self a _)
    exact two m (B.flanks_in_shore no P m hm) off ▸ hm
  have notXY := P.terminalQuartet_independent no x xmem y ymem
  obtain ⟨p,pX,xp,tipX⟩ := F.ordinary_tip xX rx xa xb dx
  obtain ⟨q,_,_,tipY⟩ := B.ordinary_tip yX ay yr yb dy
  have py : p ≠ y := fun e => notXY (e ▸ xp)
  let R := {w : V | w ∈ X ∧ w ≠ x ∧ w ≠ y ∧ w ≠ p}
  have outside : R.Nonempty := by
    apply Set.nonempty_iff_ne_empty.mpr
    intro empty
    have sub : P.terminalQuartet ⊆ ({x,y,p} : Finset V) := by
      intro w hw
      have wX := F.flanks_in_shore no P w hw
      by_contra absent
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at absent
      have wr : w ∈ R := ⟨wX,absent.1,absent.2.1,absent.2.2⟩
      exact (show w ∈ (∅ : Set V) from empty ▸ wr)
    have ct := Finset.card_le_card sub
    rw [P.terminalQuartet_card no,F.cubic] at ct
    simp [xy,xp.ne,py.symm] at ct
  have aR : a ∉ R := fun h => F.offX a (by simp) h.1
  have zR : z ∉ R := fun h => F.zX h.1
  have rR : r ∉ R := fun h => F.offX r (by simp) h.1
  have bR : b ∉ R := fun h => F.offX b (by simp) h.1
  have xR : x ∉ R := fun h => h.2.1 rfl
  have yR : y ∉ R := fun h => h.2.2.1 rfl
  have pR : p ∉ R := fun h => h.2.2.2 rfl
  have offZ {w : V} (wX : w ∈ X) : ¬ G.Adj z w := fun e => F.offX w ((F.cut.2 w).mp e) wX
  have zOff {w : V} (wX : w ∈ X) : z ≠ w := fun e => F.zX (e.symm ▸ wX)
  have cutOff {c w : V} (hc : c ∈ ({r,a,b} : Finset V)) (hw : w ∈ X) : c ≠ w :=
    fun e => F.offX c hc (e.symm ▸ hw)
  have complete : ∀ w ∈ R, G.Adj a w := fun w hw => Classical.byContradiction fun miss =>
    hw.2.2.1 (two w hw.1 miss)
  have zr := (F.cut.2 r).mpr (by simp)
  have za := (F.cut.2 a).mpr (by simp)
  have zb := (F.cut.2 b).mpr (by simp)
  have triple : Triple G R := triple_of_two_tips F.budget (zOff xX).symm
    (fun e => offZ xX e.symm) xa.symm za.symm xR zR complete
    (fun w hw e => hw.2.2.2 (tipX w hw.1 e)) (fun _ h => offZ h.1)
  obtain ⟨t,tX,tx,ty,tp,pt⟩ := exit_between_two_leaves F.connX pX tipX tipY outside
  obtain ⟨e,_,tail⟩ := pointed_residual (z := t) (show t ∈ R from ⟨tX,tx,ty,tp⟩) aR complete triple
  let L := [z,r,y,b,x,p]
  let U := {v : V | v ∈ L}
  have rmem : r ∈ ({r,a,b} : Finset V) := by simp
  have amem : a ∈ ({r,a,b} : Finset V) := by simp
  have bmem : b ∈ ({r,a,b} : Finset V) := by simp
  have nd : L.Nodup := by
    simp [L,zr.ne,zb.ne,zOff xX,zOff yX,zOff pX,cutOff rmem yX,F.rb,cutOff rmem xX,
      cutOff rmem pX,(cutOff bmem yX).symm,xy.symm,py.symm,cutOff bmem xX,cutOff bmem pX,xp.ne]
  have chain : L.Chain' G.Adj := by simp [L,List.chain'_cons,zr,yr.symm,yb,xb.symm,xp]
  let core : PathOn G U := ⟨L,by simp [L],chain,nd,fun _ => Iff.rfl⟩
  have left : Traverses G U z p := ⟨core,rfl,rfl⟩
  have dis : Disjoint U (insert a R) := by
    apply Set.disjoint_left.mpr
    intro v hv hv'
    simp only [U,Set.mem_setOf_eq,L,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv' with va|vR
    · subst v
      rcases hv with h|h|h|h|h|h
      · exact za.ne h.symm
      · exact F.ra h.symm
      · exact cutOff amem yX h
      · exact F.ab h
      · exact cutOff amem xX h
      · exact cutOff amem pX h
    · rcases hv with h|h|h|h|h|h
      · exact zR (h ▸ vR)
      · exact rR (h ▸ vR)
      · exact yR (h ▸ vR)
      · exact bR (h ▸ vR)
      · exact xR (h ▸ vR)
      · exact pR (h ▸ vR)
  have full : U ∪ insert a R = Set.univ := by
    apply Set.eq_univ_of_forall
    intro w
    by_cases inU : w ∈ U
    · exact Or.inl inU
    right
    have absent : w ≠ z ∧ w ≠ r ∧ w ≠ y ∧ w ≠ b ∧ w ≠ x ∧ w ≠ p := by
      simpa only [U,Set.mem_setOf_eq,L,List.mem_cons,List.not_mem_nil,or_false,not_or] using inU
    rcases F.cover w with wX|wz|wr|wa|wb
    · exact Or.inr ⟨wX,absent.2.2.2.2.1,absent.2.2.1,absent.2.2.2.2.2⟩
    · exact (absent.1 wz).elim
    · exact (absent.2.1 wr).elim
    · exact Or.inl wa
    · exact (absent.2.2.2.1 wb).elim
  obtain ⟨H,_,_⟩ := left.join tail dis pt
  exact no (traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp ⟨full ▸ H⟩))

#print axioms SingletonCut.traceable_of_two_almost_complete
end Graffiti199Depleted.Catalogue.Incomplete


