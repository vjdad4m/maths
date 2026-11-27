import NeighborCount
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
variable {X H : Set V} {z r a b : V}

private theorem remaining_index (i j : Fin 3) (ij : i ≠ j) :
    ∃ k : Fin 3, k ≠ i ∧ k ≠ j ∧ ∀ t : Fin 3, t = i ∨ t = j ∨ t = k := by
  revert i j
  decide

theorem ThreeCliques.splice (C : ThreeCliques G H) (F : SingletonCut G X z r a b)
    (sub : H ⊆ X) (on : ∀ v ∈ H, G.Adj r v) {s t : V}
    (route : Traverses G (insert r H)ᶜ s t) {i j : Fin 3} (ij : i ≠ j)
    {v w : V} (vi : v ∈ C.part i) (wj : w ∈ C.part j) (vs : G.Adj v s) (tw : G.Adj t w) : Traceable G := by
  classical
  obtain ⟨k,ki,kj,full⟩ := remaining_index i j ij
  have inn {l : Fin 3} {u : V} (h : u ∈ C.part l) : u ∈ H := (C.cover u).mpr ⟨l,h⟩
  have off (l : Fin 3) : r ∉ C.part l := fun h => F.offX r (by simp) (sub (inn h))
  have dj {l m : Fin 3} (lm : l ≠ m) : Disjoint (C.part l) (C.part m) :=
    Set.disjoint_left.mpr (fun {p} h q => (C.separate l m lm p h p q).1 rfl)
  obtain ⟨h,hk⟩ := C.nonempty k
  obtain ⟨u,uk,first⟩ := Traverses.start_clique (C.clique k) hk
  obtain ⟨m,mi,second⟩ := Traverses.end_clique (C.clique i) vi
  obtain ⟨n,_,last⟩ := Traverses.start_clique (C.clique j) wj
  have L := first.join (Traverses.single r) (Set.disjoint_singleton_right.mpr (off k)) (on _ (inn uk)).symm
  have A := L.join second (Set.disjoint_union_left.mpr ⟨dj ki,Set.disjoint_singleton_left.mpr (off i)⟩) (on _ (inn mi))
  let S := (C.part k ∪ {r}) ∪ C.part i
  have firstSub : S ⊆ insert r H := by
    rintro p ((k'|r')|i')
    · exact Or.inr (inn k')
    · exact Or.inl r'
    · exact Or.inr (inn i')
  have B := A.join route (disjoint_compl_right.mono_left firstSub) vs
  have dis : Disjoint (S ∪ (insert r H)ᶜ) (C.part j) := Set.disjoint_union_left.mpr
    ⟨Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr ⟨dj kj,Set.disjoint_singleton_left.mpr (off j)⟩,
      dj ij⟩, Set.disjoint_left.mpr (fun {v} vW vj => vW (Or.inr (inn vj)))⟩
  obtain ⟨P,_,_⟩ := B.join last dis tw
  have all : (S ∪ (insert r H)ᶜ) ∪ C.part j = Set.univ := by
    apply Set.eq_univ_of_forall
    intro h
    by_cases eq : h = r
    · exact Or.inl (Or.inl (Or.inl (Or.inr eq)))
    by_cases hh : h ∈ H
    · obtain ⟨l,ml⟩ := (C.cover _).mp hh
      rcases full l with e|e|e
      · exact Or.inl (Or.inl (Or.inr (e ▸ ml)))
      · exact Or.inr (e ▸ ml)
      · exact Or.inl (Or.inl (Or.inl (Or.inl (e ▸ ml))))
    · exact Or.inl (Or.inr (fun h => h.elim eq hh))
  exact traceable_iff_hamiltonian_walk.mpr (pathOn_univ_iff_hamiltonian_walk.mp ⟨all ▸ P⟩)

/-- A nonneighbor of r meeting one of three anticomplete neighbor cliques
is complete to at least one of the other two. -/
theorem ThreeCliques.complete_to_another (C : ThreeCliques G H) (F : SingletonCut G X z r a b)
    (sub : H ⊆ X) (on : ∀ v ∈ H, G.Adj r v) {x : V} (xX : x ∈ X) (rx : ¬ G.Adj r x)
    {i : Fin 3} {u : V} (ui : u ∈ C.part i) (xu : G.Adj x u) :
    ∃ j : Fin 3, j ≠ i ∧ ∀ v ∈ C.part j, G.Adj x v := by
  classical
  by_contra! none
  obtain ⟨j,ji⟩ : ∃ j : Fin 3, j ≠ i := exists_ne i
  obtain ⟨k,ki,kj,_⟩ := remaining_index i j ji.symm
  obtain ⟨v,vj,xv⟩ := none j ji
  obtain ⟨w,wk,xw⟩ := none k ki
  have uh := (C.cover _).mpr ⟨i,ui⟩
  have vh := (C.cover _).mpr ⟨j,vj⟩
  have wh := (C.cover _).mpr ⟨k,wk⟩
  have ru := on _ uh
  have rv := on _ vh
  have rw' := on _ wh
  have uv := C.separate i j ji.symm _ ui _ vj
  have uw := C.separate i k ki.symm _ ui _ wk
  have vw := C.separate j k kj.symm _ vj _ wk
  obtain ⟨f,h0,h1,h2,h3,root⟩ := four_ordering (G := G) (r := r) (x := u) (y := v) (z := w)
    (by simp [ru.ne,rv.ne,rw'.ne,uv.1,uw.1,vw.1]) ru (Or.inl ⟨rv.symm,fun e => uv.2 e.symm⟩)
    (Or.inl ⟨rw'.symm,fun e => uw.2 e.symm,fun e => vw.2 e.symm⟩)
  have side : ∀ l : Fin 4, l ≠ 0 → f l ∈ X := by
    intro l h; fin_cases l
    · exact (h rfl).elim
    · exact h1.symm ▸ sub uh
    · exact h2.symm ▸ sub vh
    · exact h3.symm ▸ sub wh
  have off : ∀ l, x ≠ f l := by
    intro l; fin_cases l
    · exact h0.symm ▸ fun e => F.offX r (by simp) (e ▸ xX)
    · exact h1.symm ▸ xu.ne
    · exact h2.symm ▸ fun e => rx (e.symm ▸ rv)
    · exact h3.symm ▸ fun e => rx (e.symm ▸ rw')
  obtain ⟨l,ne,hx⟩ := (F.quartet_contacts f h0 side root).1 x xX off 1 (h1.symm ▸ xu)
  fin_cases l
  · exact rx (h0 ▸ hx.symm)
  · exact ne rfl
  · exact xv (h2 ▸ hx)
  · exact xw (h3 ▸ hx)

#print axioms ThreeCliques.splice
#print axioms ThreeCliques.complete_to_another
end Graffiti199Depleted.Catalogue.Incomplete
