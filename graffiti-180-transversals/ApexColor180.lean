import RootReserve180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def tone (a : Bool) (d : ℕ) : Bool := if d%2=0 then a else !a

theorem tone_succ (a : Bool) (d : ℕ) : tone a (d+1)=!(tone a d) := by
  by_cases h : d%2=0
  · have n : (d+1)%2≠0 := by omega
    simp [tone,h,n]
  · have e : (d+1)%2=0 := by omega
    simp [tone,h,e]

omit [Fintype V] [DecidableEq V] in
theorem near_tone (G : SimpleGraph V) (gc : G.Connected) (r t : V) (c : V→Bool)
    (proper : ∀ x≠t,∀ y≠t,G.Adj x y → c x≠c y) (x : V)
    (xt : x≠t) (near : G.dist x r≤G.dist t r) : c x=tone (c r) (G.dist x r) := by
  induction d : G.dist x r using Nat.strong_induction_on generalizing x with
  | h d ih =>
    by_cases xr : x=r
    · subst x; simp [←d,tone,dist_self]
    · obtain ⟨y,xy,down⟩ := Graffiti169.exists_predecessor G gc r x xr
      have yt : y≠t := by rintro rfl; omega
      have lower := ih (G.dist y r) (by omega) y yt (by omega) rfl
      have diff := proper x xt y yt xy
      rw [←d,down,tone_succ,←lower]
      cases a : c x <;> cases b : c y <;> simp_all

theorem neighbor_repair (G : SimpleGraph V) (t : V) (c : V→Bool) (a : Bool)
    (proper : ∀ x≠t,∀ y≠t,G.Adj x y → c x≠c y) :
    let F := (G.neighborFinset t).filter (fun y => c y≠a)
    TwoColor G (univ\F) := by
  classical
  intro F
  let paint x := if x=t then !a else c x
  apply (color_function ..).mpr
  refine ⟨paint,fun x xm y ym edge => ?_⟩
  have safe (v : V) (vm : v∈univ\F) (tv : G.Adj t v) : c v=a := by
    by_contra ne
    exact (mem_sdiff.mp vm).2 (mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr tv,ne⟩)
  by_cases xt : x=t
  · subst x; have ya := safe y ym edge
    simp [paint,edge.ne.symm,ya]
  by_cases yt : y=t
  · subst y; have xa := safe x xm edge.symm
    simp [paint,xt,xa]
  simpa [paint,xt,yt] using proper x xt y yt edge

/-- When deleting t gives a bipartite graph, all same-layer neighbors of
t have a common color, including when t has several predecessors. -/
theorem apex_vertical (G : SimpleGraph V) (gc : G.Connected) (r t : V) (bi : TwoColor G (univ.erase t))
    (I : Finset V) (ii : Indep G I) (it : t∈I) :
    let H := alternating G (parity G r true)
    ∃ Z,TwoColor G Z ∧ I⊆Z ∧ Fintype.card V≤Z.card+H.degree t := by
  classical
  intro H
  obtain ⟨c,ok⟩ := (color_function ..).mp bi
  have proper (x : V) (xt : x≠t) (y : V) (yt : y≠t) := ok x (mem_erase.mpr ⟨xt,mem_univ _⟩) y (mem_erase.mpr ⟨yt,mem_univ _⟩)
  let a := tone (c r) (G.dist t r)
  let F := (G.neighborFinset t).filter (fun y => c y≠a)
  have sub : F⊆H.neighborFinset t := by
    intro y ym
    obtain ⟨nb,no⟩ := mem_filter.mp ym
    have ed := (G.mem_neighborFinset _ _).mp nb
    have neq : G.dist y r≠G.dist t r := by
      intro eq; exact no (by simpa only [a,eq] using near_tone G gc r t c proper y ed.ne.symm eq.le)
    have l := gc.dist_triangle (u:=y) (v:=t) (w:=r)
    have u := gc.dist_triangle (u:=t) (v:=y) (w:=r)
    rw [dist_eq_one_iff_adj.mpr ed.symm] at l
    rw [dist_eq_one_iff_adj.mpr ed] at u
    apply (H.mem_neighborFinset _ _).mpr
    refine ⟨ed,?_⟩
    simp only [mem_parity,Bool.toNat_true];omega
  have cap := card_le_card sub
  rw [card_neighborFinset_eq_degree] at cap
  have ct := card_sdiff_add_card_eq_card (subset_univ F)
  rw [card_univ] at ct
  refine ⟨univ\F,neighbor_repair G t c a proper,?_,by omega⟩
  intro x xm
  refine mem_sdiff.mpr ⟨mem_univ _,fun m => ?_⟩
  have ed := (G.mem_neighborFinset _ _).mp (mem_filter.mp m).1
  exact ii t it x xm ed.ne ed

#print axioms near_tone
#print axioms neighbor_repair
#print axioms apex_vertical
end Minimal180.Transversals
