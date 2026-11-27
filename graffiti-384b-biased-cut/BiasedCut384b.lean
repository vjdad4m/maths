import Proof384b

namespace Graffiti384b.BiasedCut
open Finset SimpleGraph
set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

private def cut (a b : Finset V) : ℕ := ∑ x ∈ a, ∑ y ∈ b, if G.Adj x y then 1 else 0

omit [Fintype V] [DecidableEq V] in
private theorem cut_symm (a b : Finset V) : cut G a b = cut G b a := by
  unfold cut
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro y _
  apply sum_congr rfl
  intro x _
  by_cases h : G.Adj x y
  · simp [h, G.symm h]
  · have hn : ¬G.Adj y x := fun h' => h (G.symm h')
    simp [h, hn]

omit [Fintype V] in
private theorem cut_insert {v : V} {a : Finset V} (hv : v∉a) (b : Finset V) :
    cut G (insert v a) b = nbr G v b+cut G a b := by
  simp [cut,nbr,hv]

/-- Degree-tilted cut potential, as a function of the retained shore. -/
def score (B : Finset V) : ℤ := 3 * (B.card : ℤ) - (cut G B B : ℤ)

def Optimal (B : Finset V) : Prop := ∀ C, score G C ≤ score G B

omit [Fintype V] in
private theorem nbr_insert_self (v : V) (B : Finset V) :
    nbr G v (insert v B) = nbr G v B := by
  unfold nbr
  congr 1
  ext w
  by_cases e : w=v
  · subst w
    simp
  · simp [e]

private theorem score_insert {B : Finset V} {v : V} (hv : v∉B) :
    score G (insert v B) = score G B + 3 - 2 * (nbr G v B : ℤ) := by
  have h : cut G (insert v B) (insert v B) =
      nbr G v B + nbr G v B + cut G B B := by
    rw [cut_insert G hv, nbr_insert_self G, cut_symm G B (insert v B),cut_insert G hv]
    omega
  unfold score
  rw [card_insert_of_not_mem hv,h]
  push_cast
  omega

omit [Fintype V] in
private theorem nbr_erase_self (v : V) (B : Finset V) :
    nbr G v (B.erase v) = nbr G v B := by
  by_cases h : v∈B
  · have e := nbr_insert_self G v (B.erase v)
    rw [insert_erase h] at e
    exact e.symm
  · rw [erase_eq_of_not_mem h]

theorem exists_optimal : ∃ B : Finset V, Optimal G B := by
  obtain ⟨b,_,le⟩ := exists_max_image (univ : Finset (Finset V)) (score G) ⟨∅,mem_univ _⟩
  exact ⟨b,fun C => le C (mem_univ _)⟩

theorem two_dominates {B : Finset V} (opt : Optimal G B) : TwoDominates G B := by
  intro v hv
  have noninc := opt (insert v B)
  rw [score_insert G hv] at noninc
  omega

theorem dissociated {B : Finset V} (opt : Optimal G B) {v : V} (hv : v∈B) :
    nbr G v B≤1 := by
  have e := score_insert G (not_mem_erase v B)
  rw [insert_erase hv,nbr_erase_self G] at e
  have dec := opt (B.erase v)
  omega

private theorem no_neighbors_after_erasing_both {B : Finset V} {x y z : V}
    (xy : G.Adj x y) (xz : G.Adj x z) (yB : y∈B) (zB : z∈B)
    (yz : y≠z) (ex : nbr G x B=2) : nbr G x ((B.erase y).erase z)=0 := by
  have sub : ({y,z} : Finset V)⊆B.filter (G.Adj x) :=
    insert_subset (mem_filter.mpr ⟨yB,xy⟩) (singleton_subset_iff.mpr (mem_filter.mpr ⟨zB,xz⟩))
  have eq := eq_of_subset_of_card_le sub (by rw [card_pair yz]; exact le_of_eq ex)
  unfold nbr
  have empty : ((B.erase y).erase z).filter (G.Adj x) = ∅ := by
    apply filter_eq_empty_iff.mpr
    intro a am adj
    have aB := erase_subset _ _ (erase_subset _ _ am)
    have ha := mem_filter.mpr ⟨aB,adj⟩
    rw [←eq,mem_insert,mem_singleton] at ha
    rcases ha with rfl|rfl
    · exact not_mem_erase _ _ (erase_subset _ _ am)
    · exact not_mem_erase _ _ am
  rw [empty,card_empty]

omit [Fintype V] in
private theorem nbr_erase_nonadj {B : Finset V} {z y : V} (ny : ¬G.Adj z y) :
    nbr G z (B.erase y)=nbr G z B := by
  unfold nbr
  congr 1
  ext a
  simp only [mem_filter,mem_erase]
  constructor
  · exact fun h=>⟨h.1.2,h.2⟩
  · intro h
    exact ⟨⟨fun e=>ny (e ▸ h.2),h.1⟩,h.2⟩

/-- Each exactly-two-supported outside vertex sees an isolated retained
vertex or the endpoints of a single retained edge. -/
theorem exact_support_matching {B : Finset V} (opt : Optimal G B)
    {x y z : V} (xB : x∉B) (yB : y∈B) (zB : z∈B) (yz : y≠z)
    (xy : G.Adj x y) (xz : G.Adj x z) (ex : nbr G x B=2) :
    G.Adj y z ∨ nbr G y B=0 ∨ nbr G z B=0 := by
  by_cases h : G.Adj y z
  · exact Or.inl h
  by_cases hy0 : nbr G y B=0
  · exact Or.inr (Or.inl hy0)
  by_cases hz0 : nbr G z B=0
  · exact Or.inr (Or.inr hz0)
  exfalso
  have dy := dissociated G opt yB
  have dz := dissociated G opt zB
  have ye : nbr G y B=1 := by omega
  have ze : nbr G z B=1 := by omega
  let C := (B.erase y).erase z
  have hy := score_insert G (not_mem_erase y B)
  rw [insert_erase yB,nbr_erase_self G,ye] at hy
  have zp : z ∈ B.erase y := mem_erase.mpr ⟨yz.symm,zB⟩
  have hz := score_insert G (not_mem_erase z (B.erase y))
  rw [insert_erase zp,nbr_erase_self G,nbr_erase_nonadj G (fun a=>h a.symm),ze] at hz
  have xc : x∉C := fun hx=>xB (erase_subset _ _ (erase_subset _ _ hx))
  have hs := score_insert G xc
  have ni := no_neighbors_after_erasing_both G xy xz yB zB yz ex
  change nbr G x C=0 at ni
  rw [ni] at hs
  have mx := opt (insert x C)
  change score G (B.erase y)=score G C + 3 - 2*(1:ℤ) at hz
  omega

#print axioms Graffiti384b.BiasedCut.exists_optimal
#print axioms Graffiti384b.BiasedCut.two_dominates
#print axioms Graffiti384b.BiasedCut.dissociated
#print axioms Graffiti384b.BiasedCut.exact_support_matching





omit [Fintype V] in
private theorem nbr_erase_adj {B : Finset V} {x y : V} (yB : y∈B) (xy : G.Adj x y) :
    nbr G x B = nbr G x (B.erase y)+1 := by
  unfold nbr
  have eq : B.filter (G.Adj x) = insert y ((B.erase y).filter (G.Adj x)) := by
    ext w
    by_cases e : w=y
    · subst w
      simp [yB,xy]
    · simp [e]
  rw [eq,card_insert_of_not_mem (fun h=>(mem_erase.mp (mem_filter.mp h).1).1 rfl)]

/-- A vertex outside B having exactly two B-neighbors can exchange with a
matched retained neighbor without changing the optimum potential. -/
theorem swap_supported {B : Finset V} (opt : Optimal G B) {x y : V}
    (xB : x∉B) (yB : y∈B) (xy : G.Adj x y) (ex : nbr G x B=2) (ym : nbr G y B=1) :
    Optimal G (insert x (B.erase y)) := by
  have h := score_insert G (not_mem_erase y B)
  rw [insert_erase yB,nbr_erase_self G,ym] at h
  have inx : x∉B.erase y := fun hm=>xB (erase_subset _ _ hm)
  have e := score_insert G inx
  have loss := nbr_erase_adj G yB xy
  have one : nbr G x (B.erase y)=1 := by omega
  rw [one] at e
  intro T
  have ht := opt T
  omega

/-- The exactly-two-supported outside vertices sharing a matched retained
neighbor form a clique. The two support sets need not be equal. -/
theorem fragile_fiber_clique {B : Finset V} (opt : Optimal G B) {x z y : V}
    (xB : x∉B) (zB : z∉B) (yB : y∈B) (xz : x≠z)
    (xy : G.Adj x y) (zy : G.Adj z y) (ex : nbr G x B=2) (ez : nbr G z B=2) (ym : nbr G y B=1) :
    G.Adj x z := by
  classical
  by_contra no
  have n : z∉insert x (B.erase y) := by
    intro z'
    rcases mem_insert.mp z' with eq|hm
    · exact xz eq.symm
    · exact zB (erase_subset _ _ hm)
  have h := two_dominates G (swap_supported G opt xB yB xy ex ym) z n
  have e : nbr G z (insert x (B.erase y)) = nbr G z (B.erase y) := by
    unfold nbr
    congr 1
    ext a
    by_cases e : a=x
    · subst a
      have nzx : ¬G.Adj z x := fun h=>no h.symm
      simp [nzx]
    · simp [e]
  rw [e] at h
  have zz := nbr_erase_adj G yB zy
  omega

#print axioms swap_supported
#print axioms fragile_fiber_clique
end Graffiti384b.BiasedCut
