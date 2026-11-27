import NestedCoreSingletonGate133
namespace Graffiti133NestedSingleGate
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Eighth Graffiti133P8Heawood
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def AdjacentSites (i k : Fin 7) : Bool := decide (k=i ∨ k=i+1)
def AdjacentChain (i : Fin 7) : Fin 10→Fin 10→Prop :=
  ext (ext (ext (@Cyclic 7) (AdjacentSites i)) (@OnlyLast 7)) (LastAndSite none)
instance (i : Fin 7) : DecidableRel (AdjacentChain i) :=
  inferInstanceAs (DecidableRel (ext (ext (ext (@Cyclic 7) (AdjacentSites i)) (@OnlyLast 7)) (LastAndSite none)))

theorem adjacent_tail_certificate : ∀ i : Fin 7,
    (∀ a b : Fin 9,tail i (some (i+1)) a=tail i (some (i+1)) b→a=b) ∧
    (∀ a b : Fin 9,a<b→(AdjacentChain i (tail i (some (i+1)) a)
      (tail i (some (i+1)) b)↔a.val+1=b.val)) := by decide

private theorem adjacent_pair_tail_witness
    (H : Hole G 7) (i : Fin 7)
    (z r s : V) (zo : Outside H.c z) (ro : Remote H r) (so : Outside H.c s)
    (sz : s≠z) (rz : G.Adj r z) (sr : G.Adj s r) (szno : ¬G.Adj s z)
    (zi : ∀ k,G.Adj z (H.c k)↔k=i ∨ k=i+1)
    (sj : ∀ k,G.Adj s (H.c k)↔(none : Option (Fin 7))=some k) :
    ∃ f : Fin 9→V,InducedPath G f := by
  let M : Model G (@Cyclic 7) := ⟨H.c,H.inj,fun a b=>(H.adj a b).symm⟩
  have zAdj (k : Fin 7) : AdjacentSites i k=true ↔ G.Adj z (M.f k) := by
    simpa [AdjacentSites,M] using (zi k).symm
  let N := M.extend z zo zAdj
  have rFresh : N.Fresh r := by
    intro k
    refine Fin.lastCases ?_ (fun p=>?_) k
    · rw [show N.f (Fin.last 7)=z from Model.extend_f_new M z zo zAdj]
      exact rz.ne
    · rw [show N.f p.castSucc=M.f p from Model.extend_f_old M z zo zAdj p]
      exact ro.1 p
  have rAdj (k : Fin 8) : OnlyLast k=true↔G.Adj r (N.f k) := by
    refine Fin.lastCases ?_ (fun p=>?_) k
    · rw [show N.f (Fin.last 7)=z from Model.extend_f_new M z zo zAdj]
      simpa [OnlyLast] using rz
    · rw [show N.f p.castSucc=M.f p from Model.extend_f_old M z zo zAdj p]
      have ps : p.castSucc≠Fin.last 7 := by
        intro eq
        have q := congrArg Fin.val eq
        have l := p.isLt
        change p.val=7 at q
        omega
      exact ⟨fun h=>(ps (of_decide_eq_true h)).elim,fun h=>(ro.2 p h).elim⟩
  let P := N.extend r rFresh rAdj
  have sFresh : P.Fresh s := by
    intro k
    refine Fin.lastCases ?_ (fun p=>?_) k
    · rw [show P.f (Fin.last 8)=r from Model.extend_f_new N r rFresh rAdj]
      exact sr.ne
    · rw [show P.f p.castSucc=N.f p from Model.extend_f_old N r rFresh rAdj p]
      refine Fin.lastCases ?_ (fun q=>?_) p
      · rw [show N.f (Fin.last 7)=z from Model.extend_f_new M z zo zAdj]
        exact sz
      · rw [show N.f q.castSucc=M.f q from Model.extend_f_old M z zo zAdj q]
        exact so q
  have sAdj (k : Fin 9) : LastAndSite none k=true↔G.Adj s (P.f k) := by
    refine Fin.lastCases ?_ (fun p=>?_) k
    · rw [show P.f (Fin.last 8)=r from Model.extend_f_new N r rFresh rAdj]
      simpa [LastAndSite] using sr
    · rw [show P.f p.castSucc=N.f p from Model.extend_f_old N r rFresh rAdj p]
      have ps : p.castSucc≠Fin.last 8 := by
        intro eq
        have q := congrArg Fin.val eq
        have l := p.isLt
        change p.val=8 at q
        omega
      simp only [LastAndSite,decide_eq_true_eq,ps,false_or]
      refine Fin.lastCases ?_ (fun q=>?_) p
      · rw [show N.f (Fin.last 7)=z from Model.extend_f_new M z zo zAdj]
        have no : ¬∃ k : Fin 7,(none : Option (Fin 7))=some k ∧ ((Fin.last 7).castSucc : Fin 9).val=k.val := by
          rintro ⟨k,_,e⟩
          have kl := k.isLt
          change 7=k.val at e
          omega
        exact ⟨fun h=>(no h).elim,fun h=>(szno h).elim⟩
      · rw [show N.f q.castSucc=M.f q from Model.extend_f_old M z zo zAdj q]
        constructor
        · rintro ⟨k,h,e⟩
          have eq : q=k := Fin.ext e
          exact (sj q).mpr (eq.symm ▸ h)
        · intro h
          exact ⟨q,(sj q).mp h,rfl⟩
  let Q : Model G (AdjacentChain i) := P.extend s sFresh sAdj
  have cert := adjacent_tail_certificate i
  exact ⟨Q.f ∘ tail i (some (i+1)),Q.inj.comp (fun a b e=>cert.1 a b e),
    fun a b lt=>(Q.adj ..).symm.trans (cert.2 a b lt)⟩

theorem remote_neighbor_must_share_adjacent_pair_gate
    (H : Hole G 7) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    {z r s : V} (zo : Outside H.c z) (ro : Remote H r) (so : Remote H s)
    (i : Fin 7) (zi : ∀ k,G.Adj z (H.c k)↔k=i ∨ k=i+1)
    (rz : G.Adj r z) (rs : G.Adj r s) : G.Adj s z := by
  by_contra no
  have sz : s≠z := fun eq=>so.2 i (eq.symm ▸ (zi i).mpr (Or.inl rfl))
  exact h9 (adjacent_pair_tail_witness H i z r s zo ro so.1 sz rz rs.symm no zi
    (fun k=>⟨fun e=>(so.2 k e).elim,fun e=>Option.noConfusion e⟩))

theorem remote_at_adjacent_pair_gate_has_at_most_one_remote_neighbor
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    {z r s t : V} (zo : Outside H.c z) (ro : Remote H r) (so : Remote H s) (tRemote : Remote H t)
    (i : Fin 7) (zi : ∀ k,G.Adj z (H.c k)↔k=i ∨ k=i+1)
    (rz : G.Adj r z) (rs : G.Adj r s) (rt : G.Adj r t) : s=t :=
  h4 r z s t rz.ne rs (remote_neighbor_must_share_adjacent_pair_gate H h9 zo ro so i zi rz rs).symm
    rt (remote_neighbor_must_share_adjacent_pair_gate H h9 zo ro tRemote i zi rz rt).symm

#print axioms remote_neighbor_must_share_adjacent_pair_gate
#print axioms remote_at_adjacent_pair_gate_has_at_most_one_remote_neighbor
end Graffiti133NestedSingleGate
