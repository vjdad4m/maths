import HighEarParity33

namespace Graffiti384b.HighEar
open Finset SimpleGraph OneEar EarAnchor EarFrame33 CliquePivot33
open private Repair.isolate from Repair384b
open private EarAnchor.sees_in_clique from CubicAnchor33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- All even simple routes fail at a pivot with no uncredited cubic neighbor.
A shortest even route would allow two pins per color in the retained clique. -/
theorem pivot_odd {e a c x : V} (de : H.degree e=2) (ea : H.Adj e a) (ec : H.Adj e c) (ac : a≠c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (xm : x∈C)
    (safe : ∀ u,H.degree u=3 → u∉R → ¬H.Adj u x) :
    ∀ n,Route (Repair.isolate H x) e a c n → n%2=1 := by
  classical
  let J := Repair.isolate H x
  let K := C.erase x
  have en : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have ke : e∉K := fun m => en (erase_subset _ _ m)
  have sz : K.card=4 := by rw [show K=C.erase x from rfl,card_erase_of_mem xm,cl.2]
  have jk : J.IsClique (K : Set V) := fun i im j jm ne =>
    ⟨cl.1 (mem_erase.mp im).2 (mem_erase.mp jm).2 ne,(mem_erase.mp im).1,(mem_erase.mp jm).1⟩
  intro n p
  apply Classical.byContradiction; intro no
  obtain ⟨m,q,ev,span⟩ := short_contacts jk (by omega) ke ⟨n,by omega,⟨p⟩⟩
  have big : 2≤m := by
    have nz : m≠0 := fun h => ac (q.start.symm.trans (h ▸ q.finish))
    omega
  have away (i : ℕ) (hi : i≤m) : q.atIdx i≠x := by
    by_cases endi : i=m
    · subst i
      have last := q.step (m-1) (by omega)
      rw [show m-1+1=m by omega] at last
      exact last.2.2
    · exact (q.step i (by omega)).2.1
  obtain ⟨A,B,fr,eb,xa,xb,la,lb,_⟩ := cycle_pins H ke (fun h => en (h ▸ xm)) big ev q.atIdx
    (fun i hi => (q.step i hi).1) q.unique q.avoid away (by rwa [q.start]) (by rwa [q.finish]) span
  have hk : H.IsNClique 4 K := ⟨fun i im j jm ne => (jk im jm ne).1,sz⟩
  obtain ⟨u,ur,du,ux⟩ := merge_pins H de pos inj tight hk (not_mem_erase x C)
    (fun y ym => cl.1 xm (mem_erase.mp ym).2 (mem_erase.mp ym).1.symm) fr eb xa xb la lb
  exact safe u du ur ux

/-- Read a path in the opened graph as a simple path avoiding the isolated
pivot and ear. Its first edge cannot be the edge between the endpoints. -/
theorem from_bypass {e a c x : V} (ec : H.Adj e c) (ac : H.Adj a c)
    (ear : H.neighborFinset e={a,c}) (reach : (bypass H e a c x).Reachable a c) :
    ∃ n,∃ p : Route (Repair.isolate H x) e a c n,2≤n ∧ p.atIdx 1≠c := by
  classical
  let J := bypass H e a c x
  obtain ⟨w,path⟩ := reach.exists_isPath
  let f := w.getVert
  have one : 0<w.length := by
    have nz : w.length≠0 := fun h => ac.ne (w.getVert_zero.symm.trans (h ▸ w.getVert_length))
    omega
  have next := w.adj_getVert_succ (i:=0) one
  rw [w.getVert_zero] at next
  have nc : f 1≠c := by
    intro h; exact next.1.2 ⟨by simp,by change f 1∈({e,a,c}:Finset V); simp [h]⟩
  have big : 2≤w.length := by
    have n1 : w.length≠1 := fun h => nc (by change w.getVert 1=c; rw [← h,w.getVert_length])
    omega
  have iso {y : V} (edge : J.Adj e y) : False := by
    have m := (H.mem_neighborFinset _ _).mpr edge.1.1; rw [ear] at m
    exact edge.1.2 ⟨mem_insert_self ..,mem_insert_of_mem m⟩
  let p : Route (Repair.isolate H x) e a c w.length := {
    atIdx := f
    start := w.getVert_zero
    finish := w.getVert_length
    step := fun i hi => ⟨(w.adj_getVert_succ hi).1.1,(w.adj_getVert_succ hi).2⟩
    unique := fun _ hi _ hj h => path.getVert_injOn hi hj h
    avoid := by
      intro i hi fe
      by_cases lt : i<w.length
      · have edge : J.Adj (f i) (f (i+1)) := w.adj_getVert_succ lt
        exact iso (fe ▸ edge)
      · have eq : i=w.length := by omega
        exact ec.ne (fe.symm.trans (eq ▸ w.getVert_length)) }
  exact ⟨_,p,big,nc⟩

/-- If every exterior neighbor of an endpoint lies in an exterior edge,
then deleting a safe clique pivot must destroy that property at some
surviving neighbor or remove one of the endpoints. -/
theorem bare_neighbor {e a c x : V} (de : H.degree e=2) (da : 4≤H.degree a) (dc : 4≤H.degree c)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (both : ¬(a∈C ∧ c∈C))
    (xm : x∈C) (xa : x≠a) (xc : x≠c) (safe : ∀ t,H.degree t=3 → t∉R → ¬H.Adj t x) :
    ∃ y∈exterior H e a c,y≠x ∧ ∀ t∈exterior H e a c,H.Adj y t → t=x := by
  classical
  have ear : H.neighborFinset e={a,c} := (eq_of_subset_of_card_le
    (insert_subset ((H.mem_neighborFinset _ _).mpr ea) (singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr ec)))
    (by rw [card_pair ac.ne,card_neighborFinset_eq_degree,de])).symm
  obtain ⟨n,p,big,nc⟩ := from_bypass H ec ac ear
    (pivot_route H de da dc ea ec ac pos inj tight cl both xm xa xc safe)
  let J := Repair.isolate H x
  let y := p.atIdx 1
  have ay : J.Adj a y := p.start ▸ p.step 0 (by omega)
  have ym : y∈exterior H e a c := mem_sdiff.mpr ⟨(H.mem_neighborFinset _ _).mpr ay.1,
    by simpa using And.intro (p.avoid 1 (by omega)) nc⟩
  refine ⟨y,ym,ay.2.2,?_⟩
  intro t tm yt
  apply Classical.byContradiction; intro tx
  have at' : J.Adj a t := ⟨(H.mem_neighborFinset _ _).mp (mem_sdiff.mp tm).1,xa.symm,tx⟩
  have yt' : J.Adj y t := ⟨yt,ay.2.2,tx⟩
  let K : Finset V := {a,y,t}
  have clique : J.IsClique (K : Set V) := by
    intro i im j jm neq
    change i∈K at im; change j∈K at jm
    rcases (show i=a ∨ i=y ∨ i=t by simpa only [K,mem_insert,mem_singleton] using im) with h|h|h <;>
      rcases (show j=a ∨ j=y ∨ j=t by simpa only [K,mem_insert,mem_singleton] using jm) with g|g|g <;>
      subst i <;> subst j <;> first | exact (neq rfl).elim | exact ay | exact ay.symm | exact at' | exact at'.symm | exact yt' | exact yt'.symm
  have te : t≠e := fun h => (mem_sdiff.mp tm).2 (h ▸ mem_insert_self ..)
  have miss : e∉K := by simp [K,ea.ne,(p.avoid 1 (by omega)).symm,te.symm,y]
  obtain ⟨l,even,⟨z⟩⟩ := AnchorParity.even_of_two_contacts clique
    (show 3≤K.card by simp [K,ay.ne,at'.ne,yt.ne]) miss p (r:=0) (s:=1) (by decide) (by omega)
    (by simp [p.start,K]) (by simp [K,y])
  have odd := pivot_odd H de ea ec ac.ne pos inj tight cl xm safe l z
  omega

end Graffiti384b.HighEar
#print axioms Graffiti384b.HighEar.pivot_odd
#print axioms Graffiti384b.HighEar.bare_neighbor
