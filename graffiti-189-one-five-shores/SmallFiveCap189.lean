import CapOreFill189
import FiveCapUniversal189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph Finset Graffiti189Ore
open private degree_increasing from OreClosure189
variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
set_option linter.unusedSectionVars false

theorem traceable_cap_small_five_contacts
    (P : Finset V) (p5 : P.card=5) (large : 7≤Fintype.card V)
    (port : ∀ u∈P,3≤J.degree u) (nonport : ∀ u∉P,5≤J.degree u)
    (small : Fintype.card V≤9 ∨
      (Fintype.card V=10 ∧ ∃ E⊆P,E.card=2 ∧ ∀ u∈E,4≤J.degree u)) :
    Graffiti189Ore.Traceable (cap J (fun u=>u∈P)) := by
  classical
  let K := (univ : Finset V)\P
  have count : K.card+P.card=Fintype.card V :=
    (card_sdiff_add_card_eq_card (subset_univ P)).trans card_univ
  have k2 : 2≤K.card := by omega
  have portEdge (thin : K.card=2) : ∃ x∈P,∃ y∈P,J.Adj x y := by
    obtain ⟨x,xp⟩ := card_pos.mp (show 0<P.card by omega)
    apply Classical.byContradiction
    intro no
    have sub : J.neighborFinset x⊆K := by
      intro y ym
      have xy := (mem_neighborFinset J x y).mp ym
      exact mem_sdiff.mpr ⟨mem_univ _,fun yp=>no ⟨x,xp,y,yp,xy⟩⟩
    have cap := card_le_card sub
    rw [card_neighborFinset_eq_degree] at cap
    have lo := port x xp
    omega
  have build {H : SimpleGraph V} (sub : J≤H)
      (fill : ∀ x∈K,∀ y,x≠y → H.Adj x y) :
      Graffiti189Ore.Traceable (cap H (fun x=>x∈P)) := by
    letI : DecidableRel H.Adj := Classical.decRel _
    apply traceable_cap_five_with_universal_nonports P p5 k2
    · intro u up v uv
      exact fill u (mem_sdiff.mpr ⟨mem_univ _,up⟩) v uv
    intro thin
    obtain ⟨u,up,v,vp,uv⟩ := portEdge thin
    exact ⟨u,up,v,vp,sub uv⟩
  rcases small with small|⟨n10,E,es,e2,eDeg⟩
  · apply traceable_cap_fillAcross P K univ
    · intro x xk y _
      have xp := (mem_sdiff.mp xk).2
      have lo := nonport x xp
      by_cases yp : y∈P
      · have h := port y yp
        simp [xp,yp]
        omega
      have h := nonport y yp
      simp [xp,yp]
      omega
    apply build (fillAcross_mono J K univ)
    intro x xk y xy
    exact .inr ⟨xy,.inl ⟨xk,mem_univ _⟩⟩
  let I := fillAcross J K (K∪E)
  letI : DecidableRel I.Adj := Classical.decRel _
  have ji : J≤I := fillAcross_mono J K _
  apply traceable_cap_fillAcross P K (K∪E)
  · intro x xk y yk
    have xp := (mem_sdiff.mp xk).2
    have lo := nonport x xp
    rcases mem_union.mp yk with yk|ye
    · have yp := (mem_sdiff.mp yk).2
      have h := nonport y yp
      simp [xp,yp]
      omega
    have yp := es ye
    have h := eDeg y ye
    simp [xp,yp]
    omega
  have i6 (x : V) (xK : x∈K) : 6≤I.degree x := by
    have pair : Disjoint (K.erase x) E := by
      apply disjoint_left.mpr
      exact fun z zk ze=>(mem_sdiff.mp (mem_of_mem_erase zk)).2 (es ze)
    have sub : (K.erase x)∪E⊆I.neighborFinset x := by
      intro z h
      apply (mem_neighborFinset I x z).mpr
      rcases mem_union.mp h with zk|ze
      · exact .inr ⟨(mem_erase.mp zk).1.symm,.inl ⟨xK,mem_union_left _ (mem_of_mem_erase zk)⟩⟩
      exact .inr ⟨(fun e=>(mem_sdiff.mp xK).2 (e.symm ▸ es ze)),.inl ⟨xK,mem_union_right _ ze⟩⟩
    have tally := card_le_card sub
    rw [card_union_of_disjoint pair,card_erase_of_mem xK,e2,card_neighborFinset_eq_degree] at tally
    omega
  apply traceable_cap_fillAcross (J:=I) P K univ
  · intro x xk y _
    have xp := (mem_sdiff.mp xk).2
    have lo := i6 x xk
    by_cases yp : y∈P
    · have h := (port y yp).trans (degree_increasing ji y)
      simp [xp,yp]
      omega
    have h := (nonport y yp).trans (degree_increasing ji y)
    simp [xp,yp]
    omega
  apply build (ji.trans (fillAcross_mono I K univ))
  intro x xk y xy
  exact .inr ⟨xy,.inl ⟨xk,mem_univ _⟩⟩

#print axioms traceable_cap_small_five_contacts
end Graffiti189LongestPath.CrossSaturation
