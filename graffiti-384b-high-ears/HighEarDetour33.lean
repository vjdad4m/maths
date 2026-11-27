import HighEarLayout33

namespace Graffiti384b.HighEar
open Finset SimpleGraph OneEar EarAnchor CliquePivot33
open private Repair.isolate from Repair384b
open private CubicShore.half_tight from CubicDiamondCut33
open private EarAnchor.sees_in_clique from CubicAnchor33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Using one exterior neighbor as a safe pivot gives an odd route that meets
the clique only at the other exterior neighbor. Insert the pivot back into
the first edge to obtain an even route with both clique colors prescribed. -/
theorem triangle_detour {e a c s t u : V} (de : H.degree e=2) (da : 4≤H.degree a) (dc : 4≤H.degree c)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c) (st : H.Adj s t)
    (D : exterior H e a c={s,t})
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (half : Fintype.card V≤2*gamma H) {C : Finset V} (cl : H.IsNClique 5 C)
    (sc : s∈C) (tc : t∈C) (anc : a∉C) (cnc : c∉C)
    (du : H.degree u=3) (N : H.neighborFinset u=C\{s,t}) (only : ∀ y,H.degree y=3 → y=u) :
    ∃ m,∃ q : Route H e a c m,2≤m ∧ m%2=0 ∧ q.atIdx 1=t ∧ q.atIdx 2=s ∧
      (∀ i≤m,q.atIdx i≠u) ∧ ∀ i≤m,q.atIdx i∈C → q.atIdx i=s ∨ q.atIdx i=t := by
  classical
  let J := Repair.isolate H t
  have safe (v : V) (dv : H.degree v=3) (_ : v∉(∅ : Finset V)) : ¬H.Adj v t := by
    intro edge
    have mem := (H.mem_neighborFinset _ _).mpr (show H.Adj u t from only v dv ▸ edge)
    rw [N] at mem; exact (mem_sdiff.mp mem).2 (mem_insert_of_mem (mem_singleton_self _))
  have xs : t≠a := fun h => anc (h ▸ tc)
  have xc : t≠c := fun h => cnc (h ▸ tc)
  have ear : H.neighborFinset e={a,c} := (eq_of_subset_of_card_le
    (insert_subset ((H.mem_neighborFinset _ _).mpr ea) (singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr ec)))
    (by rw [card_pair ac.ne,card_neighborFinset_eq_degree,de])).symm
  have tight := CubicShore.half_tight H half
  obtain ⟨n,p,big,notC⟩ := from_bypass H ec ac ear
    (pivot_route H de da dc ea ec ac pos inj tight cl (fun pair => anc pair.1) tc xs xc safe)
  have odd := pivot_odd H de ea ec ac.ne pos inj tight cl tc safe n p
  have away (i : ℕ) (hi : i≤n) : p.atIdx i≠t := by
    by_cases lt : i<n
    · exact (p.step i lt).2.1
    · have endi : i=n := by omega
      exact fun h => xc (h.symm.trans (endi ▸ p.finish))
  have firstE : H.Adj a (p.atIdx 1) := (congrArg (fun v => H.Adj v (p.atIdx 1)) p.start).mp (p.step 0 (by omega)).1
  have outside : p.atIdx 1∈exterior H e a c := mem_sdiff.mpr ⟨(H.mem_neighborFinset _ _).mpr firstE,
    by simpa using And.intro (p.avoid 1 (by omega)) notC⟩
  rw [D] at outside
  have first : p.atIdx 1=s := (mem_insert.mp outside).resolve_right (fun m => away 1 (by omega) (mem_singleton.mp m))
  let K := C.erase t
  have ke : e∉K := fun m => by have := EarAnchor.sees_in_clique H cl (erase_subset _ _ m); omega
  have ks : K.card=4 := by rw [show K=C.erase t from rfl,card_erase_of_mem tc,cl.2]
  have jc : J.IsClique (K : Set V) := fun i im j jm ne =>
    ⟨cl.1 (mem_erase.mp im).2 (mem_erase.mp jm).2 ne,(mem_erase.mp im).1,(mem_erase.mp jm).1⟩
  have single (i : ℕ) (hi : i≤n) (im : p.atIdx i∈C) : i=1 := by
    have mk : p.atIdx i∈K := mem_erase.mpr ⟨away i hi,im⟩
    have k1 : p.atIdx 1∈K := first ▸ mem_erase.mpr ⟨st.ne,sc⟩
    apply Classical.byContradiction; intro ne
    have ev : ∃ k,k%2=0 ∧ Nonempty (Route J e a c k) := by
      rcases lt_or_gt_of_ne ne with lt|gt
      · exact AnchorParity.even_of_two_contacts jc (by omega) ke p lt (by omega) mk k1
      · exact AnchorParity.even_of_two_contacts jc (by omega) ke p gt hi k1 mk
    obtain ⟨k,even,⟨r⟩⟩ := ev
    have other := pivot_odd H de ea ec ac.ne pos inj tight cl tc safe k r
    omega
  have ue : u≠e := fun eq => by subst u; omega
  have uC : u∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have ua : u≠a := fun eq => by subst u; omega
  have uc : u≠c := fun eq => by subst u; omega
  have skip (i : ℕ) (hi : i≤n) : p.atIdx i≠u := by
    intro h
    have nz : i≠0 := fun z => ua (h.symm.trans (z ▸ p.start))
    have ne : i≠n := fun z => uc (h.symm.trans ((congrArg p.atIdx z).trans p.finish))
    have lt : i<n := by omega
    have mem {y : V} (edge : H.Adj u y) : y∈C := by
      have m := (H.mem_neighborFinset _ _).mpr edge
      rw [N] at m; exact (mem_sdiff.mp m).1
    have prev := (p.step (i-1) (by omega)).1.symm
    rw [show i-1+1=i by omega,h] at prev
    have nxt := (p.step i lt).1; rw [h] at nxt
    have l := single (i-1) (by omega) (mem prev)
    have r := single (i+1) (by omega) (mem nxt)
    omega
  let r : Route H e a c n := ⟨p.atIdx,p.start,p.finish,fun i hi => (p.step i hi).1,p.unique,p.avoid⟩
  let tail := r.suffix 1 (by omega)
  have te : t≠e := fun eq => by have := EarAnchor.sees_in_clique H cl (show e∈C from eq ▸ tc); omega
  let mid := tail.prepend (show H.Adj t (r.atIdx 1) from first ▸ st.symm) te
    (fun i hi => (away (1+i) (by omega)).symm)
  have at' : H.Adj a t := (H.mem_neighborFinset _ _).mp (mem_sdiff.mp (show t∈exterior H e a c from D ▸ mem_insert_of_mem (mem_singleton_self _))).1
  let q := mid.prepend at' ea.ne.symm (by
    intro i hi; cases i with
    | zero => exact xs.symm
    | succ j =>
      intro h
      have eq := p.unique 0 (by omega) (1+j) (by omega) (p.start.trans h)
      omega)
  refine ⟨_,q,by omega,by omega,rfl,first,?_,?_⟩
  · intro i hi; cases i with
    | zero => exact ua.symm
    | succ j => cases j with
      | zero => exact fun eq => uC (eq ▸ tc)
      | succ k => exact skip (1+k) (by omega)
  · intro i hi im; cases i with
    | zero => exact (anc im).elim
    | succ j => cases j with
      | zero => exact Or.inr rfl
      | succ k =>
        have sd := single (1+k) (by omega) im
        exact Or.inl (show p.atIdx (1+k)=s from (congrArg p.atIdx sd).trans first)

end Graffiti384b.HighEar
#print axioms Graffiti384b.HighEar.triangle_detour
