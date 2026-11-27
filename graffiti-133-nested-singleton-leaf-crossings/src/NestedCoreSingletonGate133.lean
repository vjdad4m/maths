import C7MultiP8AdjCharge133

namespace Graffiti133NestedSingleGate
open SimpleGraph Finset Graffiti133 Graffiti133NoFive Graffiti133Eighth Graffiti133P8Heawood
open scoped Classical BigOperators
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000
set_option maxRecDepth 100000
variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def Remote (H : Hole G 7) (y : V) : Prop :=
  Outside H.c y ∧ ∀ i,¬G.Adj y (H.c i)

def OnlyLast {n : Nat} (k : Fin (n+1)) : Bool := decide (k=Fin.last n)
def JustSite (i k : Fin 7) : Bool := decide (k=i)
def LastAndSite (j : Option (Fin 7)) (k : Fin 9) : Bool :=
  decide (k=Fin.last 8 ∨ ∃ i : Fin 7,j=some i ∧ k.val=i.val)

def Chain (i : Fin 7) (j : Option (Fin 7)) : Fin 10→Fin 10→Prop :=
  ext (ext (ext (@Cyclic 7) (JustSite i)) (@OnlyLast 7)) (LastAndSite j)

instance (i : Fin 7) (j : Option (Fin 7)) : DecidableRel (Chain i j) :=
  inferInstanceAs (DecidableRel (ext (ext (ext (@Cyclic 7) (JustSite i)) (@OnlyLast 7)) (LastAndSite j)))

def c10 (i : Fin 7) : Fin 10 := Fin.castLE (by decide) i

def tail (i : Fin 7) (j : Option (Fin 7)) : Fin 9→Fin 10 :=
  if j=some (i+1) then
    ![9,8,7,c10 i,c10 (i-1),c10 (i-2),c10 (i-3),c10 (i-4),c10 (i-5)]
  else
    ![9,8,7,c10 i,c10 (i+1),c10 (i+2),c10 (i+3),c10 (i+4),c10 (i+5)]

theorem tail_certificate : ∀ (i : Fin 7) (j : Option (Fin 7)),
    (j=none ∨ (∃ k : Fin 7,j=some k ∧ Cyclic i k)) →
    (∀ a b : Fin 9,tail i j a=tail i j b→a=b) ∧
    (∀ a b : Fin 9,a<b→(Chain i j (tail i j a) (tail i j b)↔a.val+1=b.val)) := by decide

private theorem cycle_tail_witness
    (H : Hole G 7) (i : Fin 7) (j : Option (Fin 7))
    (permitted : j=none ∨ (∃ k : Fin 7,j=some k ∧ Cyclic i k))
    (z r s : V) (zo : Outside H.c z) (ro : Remote H r) (so : Outside H.c s)
    (sz : s≠z) (rz : G.Adj r z) (sr : G.Adj s r) (szno : ¬G.Adj s z)
    (zi : ∀ k,G.Adj z (H.c k)↔k=i)
    (sj : ∀ k,G.Adj s (H.c k)↔j=some k) :
    ∃ f : Fin 9→V,InducedPath G f := by
  let M : Model G (@Cyclic 7) := ⟨H.c,H.inj,fun a b=>(H.adj a b).symm⟩
  have zAdj (k : Fin 7) : JustSite i k=true ↔ G.Adj z (M.f k) := by
    simpa [JustSite,M] using (zi k).symm
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
  have sAdj (k : Fin 9) : LastAndSite j k=true↔G.Adj s (P.f k) := by
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
        have no : ¬∃ k : Fin 7,j=some k ∧ ((Fin.last 7).castSucc : Fin 9).val=k.val := by
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
  let Q : Model G (Chain i j) := P.extend s sFresh sAdj
  have cert := tail_certificate i j permitted
  exact ⟨Q.f ∘ tail i j,Q.inj.comp (fun a b e=>cert.1 a b e),
    fun a b lt=>(Q.adj ..).symm.trans (cert.2 a b lt)⟩

theorem remote_neighbor_must_share_singleton_gate
    (H : Hole G 7) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    {z r s : V} (zo : Outside H.c z) (ro : Remote H r) (so : Remote H s)
    (i : Fin 7) (zi : ∀ k,G.Adj z (H.c k)↔k=i)
    (rz : G.Adj r z) (rs : G.Adj r s) : G.Adj s z := by
  by_contra no
  have sz : s≠z := fun eq=>so.2 i (eq.symm ▸ (zi i).mpr rfl)
  exact h9 (cycle_tail_witness H i none (Or.inl rfl) z r s zo ro so.1 sz rz rs.symm no zi
    (fun k=>⟨fun e=>(so.2 k e).elim,fun e=>Option.noConfusion e⟩))

theorem remote_at_singleton_gate_has_at_most_one_remote_neighbor
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    {z r s t : V} (zo : Outside H.c z) (ro : Remote H r) (so : Remote H s) (tRemote : Remote H t)
    (i : Fin 7) (zi : ∀ k,G.Adj z (H.c k)↔k=i)
    (rz : G.Adj r z) (rs : G.Adj r s) (rt : G.Adj r t) : s=t :=
  h4 r z s t rz.ne rs (remote_neighbor_must_share_singleton_gate H h9 zo ro so i zi rz rs).symm
    rt (remote_neighbor_must_share_singleton_gate H h9 zo ro tRemote i zi rz rt).symm

theorem sites_of_singleton_gates_at_remote_nonconsecutive
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    {z r s : V} (zo : Outside H.c z) (ro : Remote H r) (so : Outside H.c s)
    {i j : Fin 7} (zi : ∀ k,G.Adj z (H.c k)↔k=i) (sj : ∀ k,G.Adj s (H.c k)↔k=j)
    (zs : z≠s) (rz : G.Adj r z) (rs : G.Adj r s) : i≠j ∧ ¬Cyclic i j := by
  have za := (zi i).mpr rfl
  have sa := (sj j).mpr rfl
  constructor
  · intro eq
    exact zs (h4 r (H.c i) z s (ro.1 i) rz za.symm rs (eq.symm ▸ sa.symm))
  · intro cyclic
    have no : ¬G.Adj s z := by
      intro e
      have ij := (H.adj i j).mpr cyclic
      exact zo j (h4 s (H.c i) z (H.c j) (so i) e za.symm sa ij)
    exact h9 (cycle_tail_witness H i (some j) (Or.inr ⟨j,rfl,cyclic⟩) z r s zo ro so
      zs.symm rz rs.symm no zi (fun k=>(sj k).trans ⟨fun q=>congrArg some q.symm,fun q=>(Option.some.inj q).symm⟩))

private theorem independent_cycle7_card_bound :
    ∀ S : Finset (Fin 7), (∀ i∈S,∀ j∈S,¬Cyclic i j) → S.card≤3 := by decide

theorem remote_singleton_gates_card_le_three
    (H : Hole G 7) (h4 : FourCycleFree G) (h9 : ¬∃ f : Fin 9→V,InducedPath G f)
    (r : V) (rm : Remote H r) (S : Finset V)
    (single : ∀ z∈S, Outside H.c z ∧ G.Adj r z ∧
      ∃ i,∀ k,G.Adj z (H.c k)↔k=i) : S.card≤3 := by
  classical
  obtain ⟨f,hf⟩ := Classical.axiomOfChoice (fun z : (S : Set V)=>(single z.val z.property).2.2)
  let g (z : V) := if m : z∈S then f ⟨z,m⟩ else 0
  have prop (z : V) (zm : z∈S) : ∀ k,G.Adj z (H.c k)↔k=g z := by
    rw [show g z=f ⟨z,zm⟩ from dif_pos zm]
    exact hf ⟨z,zm⟩
  have sep (x : V) (xm : x∈S) (y : V) (ym : y∈S) (ne : x≠y) :
      g x≠g y ∧ ¬Cyclic (g x) (g y) :=
    sites_of_singleton_gates_at_remote_nonconsecutive H h4 h9 (single x xm).1 rm (single y ym).1
      (prop x xm) (prop y ym) ne (single x xm).2.1 (single y ym).2.1
  have inj : Set.InjOn g (S : Set V) := by
    intro x xm y ym eq
    by_contra ne
    exact (sep x xm y ym ne).1 eq
  have count := independent_cycle7_card_bound (S.image g) (by
    intro i im j jm cyc
    obtain ⟨x,xm,rfl⟩ := Finset.mem_image.mp im
    obtain ⟨y,ym,rfl⟩ := Finset.mem_image.mp jm
    by_cases eq : x=y
    · subst y
      have no : ∀ i : Fin 7,¬Cyclic i i := by decide
      exact no _ cyc
    · exact (sep x xm y ym eq).2 cyc)
  rwa [Finset.card_image_of_injOn inj] at count

#print axioms remote_singleton_gates_card_le_three
#print axioms remote_neighbor_must_share_singleton_gate
#print axioms remote_at_singleton_gate_has_at_most_one_remote_neighbor
#print axioms sites_of_singleton_gates_at_remote_nonconsecutive
end Graffiti133NestedSingleGate
