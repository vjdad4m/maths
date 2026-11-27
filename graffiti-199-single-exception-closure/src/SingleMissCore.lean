import CatalogueSingleton
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {X : Set V} {z r a b x : V}

theorem SingletonCut.single_miss_core (F : SingletonCut G X z r a b) (no : ¬ Traceable G)
    (P : PathOn G {v | v ≠ z}) (almost : ∀ w ∈ X, ¬ G.Adj r w → w = x) :
    ∃ p ∈ X, G.Adj x p ∧ (∀ v ∈ X, G.Adj x v → v = p) ∧
      ({v | v ∈ X ∧ v ≠ x ∧ v ≠ p ∧ ¬ G.Adj p v} : Set V).Pairwise G.Adj ∧
      ¬ Nonempty (PathOn G {v | v ∈ X ∧ v ≠ x}) := by
  classical
  obtain ⟨xX,rx,xa,xb,dx⟩ := F.unique_miss_degree_and_contacts no P almost
  obtain ⟨p,pX,xp,one⟩ := F.ordinary_tip xX rx xa xb dx
  have complete {w : V} (wX : w ∈ X) (wx : w ≠ x) : G.Adj r w :=
    Classical.byContradiction fun miss => wx (almost w wX miss)
  have rX := F.offX r (by simp)
  have aX := F.offX a (by simp)
  have bX := F.offX b (by simp)
  have xr : x ≠ r := fun e => rX (e ▸ xX)
  have zr := (F.cut.2 r).mpr (by simp)
  have za := (F.cut.2 a).mpr (by simp)
  have zb := (F.cut.2 b).mpr (by simp)
  refine ⟨p,pX,xp,one,?_,?_⟩
  · intro u hu v hv uv
    obtain ⟨uX,ux,up,pu⟩ := hu
    obtain ⟨vX,vx,vp,pv⟩ := hv
    have rp := complete pX xp.ne.symm
    have ru := complete uX ux
    have rv := complete vX vx
    by_contra nonedge
    obtain ⟨f,h0,h1,h2,h3,root⟩ := four_ordering (G := G) (r := r) (x := p) (y := u) (z := v)
      (by simp [rp.ne,ru.ne,rv.ne,up.symm,vp.symm,uv]) rp
      (Or.inl ⟨ru.symm,fun e => pu e.symm⟩)
      (Or.inl ⟨rv.symm,fun e => pv e.symm,fun e => nonedge e.symm⟩)
    have side : ∀ i : Fin 4, i ≠ 0 → f i ∈ X := by
      intro i hi
      fin_cases i
      · exact (hi rfl).elim
      · exact h1.symm ▸ pX
      · exact h2.symm ▸ uX
      · exact h3.symm ▸ vX
    have off : ∀ i, x ≠ f i := by
      intro i
      fin_cases i
      · exact h0.symm ▸ xr
      · exact h1.symm ▸ xp.ne
      · exact h2.symm ▸ ux.symm
      · exact h3.symm ▸ vx.symm
    obtain ⟨j,ne,other⟩ := (F.quartet_contacts f h0 side root).1 x xX off 1 (h1.symm ▸ xp)
    fin_cases j
    · exact rx (h0 ▸ other.symm)
    · exact ne rfl
    · exact up (one _ uX (h2 ▸ other))
    · exact vp (one _ vX (h3 ▸ other))
  · rintro ⟨Q⟩
    let L := [a,x,b,z,r]
    let U := {v : V | v ∈ L}
    have xz : x ≠ z := fun e => F.zX (e ▸ xX)
    have nd : L.Nodup := by
      simp [L,xa.ne.symm,F.ab,za.ne.symm,F.ra.symm,xb.ne,xz,xr,zb.ne.symm,F.rb.symm,zr.ne]
    have chain : L.Chain' G.Adj := by simp [L,List.chain'_cons,xa.symm,xb,zb.symm,zr]
    let core : PathOn G U := ⟨L,by simp [L],chain,nd,fun _ => Iff.rfl⟩
    have dis : Disjoint U {v | v ∈ X ∧ v ≠ x} := by
      apply Set.disjoint_left.mpr
      intro v hv hi
      simp only [U,Set.mem_setOf_eq,L,List.mem_cons,List.not_mem_nil,or_false] at hv
      rcases hv with e|e|e|e|e
      · exact aX (e ▸ hi.1)
      · exact hi.2 e
      · exact bX (e ▸ hi.1)
      · exact F.zX (e ▸ hi.1)
      · exact rX (e ▸ hi.1)
    have front := (Q.covers Q.first).mp (List.head_mem Q.nonempty)
    let H := core.join Q dis (show G.Adj r Q.first from complete front.1 front.2)
    have cover : U ∪ {v | v ∈ X ∧ v ≠ x} = Set.univ := by
      apply Set.eq_univ_of_forall
      intro v
      rcases F.cover v with vX|h|h|h|h
      · by_cases vx : v = x
        · exact Or.inl (by simp [U,L,vx])
        · exact Or.inr ⟨vX,vx⟩
      all_goals exact Or.inl (by simp [U,L,h])
    exact no (traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp ⟨cover ▸ H⟩))

#print axioms SingletonCut.single_miss_core
end Graffiti199Depleted.Catalogue.Incomplete
