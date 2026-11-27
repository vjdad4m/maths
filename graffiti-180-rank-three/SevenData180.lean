import CutEntry180
import MiddleCertificate180

set_option warningAsError true
set_option compiler.extract_closed false
namespace Minimal180.HigherRank.Seven
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180 Converse180 Assembly180
abbrev V := Fin 7

/-- A five-clique with degree-two vertices on the pairs 01 and 23. All
ten edges of the five-clique remain present. -/
noncomputable def E : List (V×V) := [(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4),(0,5),(1,5),(2,6),(3,6)]
noncomputable def G : SimpleGraph V where
  Adj x y := x≠y ∧ ((x,y)∈E ∨ (y,x)∈E)
  symm _ _ h := ⟨h.1.symm,h.2.symm⟩
  loopless _ h := h.1 rfl
noncomputable instance : DecidableRel G.Adj := fun x y =>
  inferInstanceAs (Decidable (x≠y ∧ ((x,y)∈E ∨ (y,x)∈E)))
noncomputable abbrev A : Finset V := {4,5,6}
noncomputable abbrev P : Finset V := {2,3,4,5}
noncomputable abbrev U : Finset V := {2,3,4,5,6}
noncomputable abbrev K : Finset V := {0,1,2,3,4}
noncomputable def d (r x : V) := (([[0,1,1,1,1,1,2],[1,0,1,1,1,1,2],[1,1,0,1,1,2,1],[1,1,1,0,1,2,1],[1,1,1,1,0,2,2],[1,1,2,2,2,0,3],[2,2,1,1,2,3,0]]:List (List ℕ))[r.val]!)[x.val]!
noncomputable def avoid (c x : V) := (([[19,0,1,1,1,1,2],[1,19,0,1,1,2,1],[1,1,19,0,1,2,1],[1,1,1,19,0,2,2],[1,1,2,2,19,0,3],[2,2,1,1,2,19,0],[0,1,1,1,1,1,19]]:List (List ℕ))[c.val]!)[x.val]!

theorem distances (r : V) : G.Connected ∧ ∀ x,G.dist x r=d r x := by
  apply layers
  · exact (show ∀ i : V,d i i=0 by decide) r
  · intro x y; exact (show ∀ i a b,G.Adj a b → d i a≤d i b+1 by decide) r x y
  · exact (show ∀ i x : V,x≠i → ∃ y,G.Adj x y ∧ d i x=d i y+1 by decide) r

theorem block : NoCut G := by
  apply noCut_of_routes G (fun c => c+1) avoid <;> decide

theorem data : Indep G A ∧ parity G 5 false=P ∧ eligible A P 5=U ∧
    evenCount G 5=4 ∧ maxEven G=4 := by
  have par (r : V) : parity G r false=univ.filter (fun x : V => d r x%2=0) := by
    ext x; simp [mem_parity,(distances r).2]
  have p : parity G 5 false=P := (par 5).trans (by decide)
  have ev : evenCount G 5=4 := by rw [even_equiv,p]; decide
  refine ⟨by unfold Indep; decide,p,by decide,ev,le_antisymm ?_ ?_⟩
  · apply Finset.sup_le
    intro r _
    rw [even_equiv,par]
    exact (show ∀ j : V,(univ.filter (fun x : V => d j x%2=0)).card≤4 by decide) r
  · exact ev ▸ (le_sup (f:=evenCount G) (mem_univ (5:V)))

theorem ranks : independence G=3 ∧ bipartiteNum G=4 := by
  classical
  have small (S : Finset V) (ind : Indep G S) : (S∩K).card≤1 := by
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨aS,aK⟩ := mem_inter.mp ha
    obtain ⟨bS,bK⟩ := mem_inter.mp hb
    by_contra ab
    exact ind a aS b bS ab ((show ∀ x∈K,∀ y∈K,x≠y → G.Adj x y by decide) a aK b bK ab)
  have rest (S : Finset V) : (S\K).card≤2 := by
    have sub : S\K⊆({5,6}:Finset V) := fun x hx =>
      (show ∀ z : V,z∉K → z∈({5,6}:Finset V) by decide) x (mem_sdiff.mp hx).2
    exact (card_le_card sub).trans (by decide)
  have ac : A.card=3 := by decide
  have al := indep_card_le G data.1
  have alpha : independence G≤3 := by
    apply Finset.sup_le
    intro S hs
    have one := small S (mem_filter.mp hs).2
    have two := rest S
    have sum := card_sdiff_add_card_inter S K
    omega
  have col : TwoColor G (insert 0 A) := by
    refine ⟨{0},A,by decide,by decide,?_,data.1⟩
    simp [Indep]
  have four := size_bip G col
  have eq : (insert 0 A).card=4 := by decide
  obtain ⟨S,⟨L,R,_,lr,li,ri⟩,mx⟩ := optB G
  have dis : S∩K=(L∩K)∪(R∩K) := by rw [←lr,union_inter_distrib_right]
  have sum := card_sdiff_add_card_inter S K
  have ub := card_union_le (L∩K) (R∩K)
  rw [←dis] at ub
  have q := rest S
  have l := small L li
  have r := small R ri
  omega

#print axioms distances
#print axioms block
#print axioms data
#print axioms ranks
end Minimal180.HigherRank.Seven
