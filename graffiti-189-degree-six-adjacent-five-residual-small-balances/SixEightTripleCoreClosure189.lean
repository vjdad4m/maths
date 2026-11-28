import SixEightHighCoreWeightedLow189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private starClose star_mono star_degree_of_marked star_degree_of_unmarked local_degree_mono
  degree_strict_of_new_edge from SixTenOre189
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

private def cliqueFill (G : SimpleGraph V) (M : Finset V) : SimpleGraph V where
  Adj u v := G.Adj u v ∨ (u≠v ∧ u∈M ∧ v∈M)
  symm := fun _ _ h=>h.elim (fun e=>.inl e.symm) (fun e=>.inr ⟨e.1.symm,e.2.2,e.2.1⟩)
  loopless := fun u h=>h.elim (G.loopless u) (fun e=>e.1 rfl)

private instance (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset V) :
    DecidableRel (cliqueFill G M).Adj := fun _ _=>inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

private theorem cliqueFill_mono (G : SimpleGraph V) (M : Finset V) :
    G≤cliqueFill G M := fun _ _ h=>.inl h

private theorem cliqueFill_degree (M : Finset V) {u : V} (um : u∈M) :
    M.card-1≤(cliqueFill G M).degree u := by
  have sub : M.erase u⊆(cliqueFill G M).neighborFinset u := by
    intro v vm
    have ⟨vn,vM⟩ := mem_erase.mp vm
    exact (mem_neighborFinset _ _ _).mpr (.inr ⟨vn.symm,um,vM⟩)
  have h := card_le_card sub
  rwa [card_erase_of_mem um,card_neighborFinset_eq_degree] at h

/-- On eight vertices, a five-vertex high core and minimum degree three
allow a prescribed terminal low vertex as long as the other side offers
one high backup vertex or a missing edge to that terminal. -/
theorem eight_triple_core_closure (n : Fintype.card V=8)
    (C : Finset V) (c5 : C.card=5) (high : ∀ u∈C,5≤G.degree u)
    (low : ∀ u,3≤G.degree u) {a z h : V} (az : a≠z) (zh : z≠h)
    (zc : z∉C) (hc : h∉C) (back : 4≤G.degree h ∨ ¬G.Adj z h) :
    ∃ p : G.Walk a z,p.IsPath ∧ ∀ u,u∈p.support := by
  classical
  let A := insert z C
  let H1 := cliqueFill G A
  let B : Finset V := {z,h}
  let H2 := cliqueFill H1 B
  let E := insert h C
  let H3 := cliqueFill H2 E
  let H4 := starClose H3 C
  have sub1 : G≤H1 := cliqueFill_mono G A
  have sub2 : H1≤H2 := cliqueFill_mono H1 B
  have sub3 : H2≤H3 := cliqueFill_mono H2 E
  have sub4 : H3≤H4 := star_mono H3 C
  have hz5 : 5≤H1.degree z := by
    have w := cliqueFill_degree (G:=G) A (show z∈A from mem_insert_self _ _)
    change _ ≤ H1.degree z at w
    have d : A.card=6 := by change (insert z C).card=6; rw [card_insert_of_not_mem zc,c5]
    omega
  have min1 (u : V) : 3≤H1.degree u := (low u).trans (local_degree_mono sub1 u)
  have h4 : 4≤H2.degree h := by
    rcases back with big|no
    · exact big.trans ((local_degree_mono sub1 h).trans (local_degree_mono sub2 h))
    have no1 : ¬H1.Adj z h := by
      rintro (ez|⟨_,_,hm⟩)
      · exact no ez
      rcases mem_insert.mp hm with q|q
      · exact zh q.symm
      exact hc q
    have yes : H2.Adj z h := .inr ⟨zh,by simp [B],by simp [B]⟩
    have g := degree_strict_of_new_edge sub2 yes.symm (fun e=>no1 e.symm)
    have q := min1 h
    omega
  have min3 (u : V) : 3≤H3.degree u :=
    (min1 u).trans ((local_degree_mono sub2 u).trans (local_degree_mono sub3 u))
  have H36 (u : V) (uc : u∈C) : 6≤H3.degree u := by
    have sub : (insert z (insert h C)).erase u⊆H3.neighborFinset u := by
      intro v vm
      have ⟨vu,vm⟩ := mem_erase.mp vm
      rcases mem_insert.mp vm with e|vm
      · subst v
        have e : H1.Adj u z := .inr ⟨vu.symm,mem_insert_of_mem uc,mem_insert_self _ _⟩
        exact (mem_neighborFinset _ _ _).mpr (sub3 (sub2 e))
      exact (mem_neighborFinset _ _ _).mpr (.inr ⟨vu.symm,mem_insert_of_mem uc,vm⟩)
    have i := card_le_card sub
    rw [card_erase_of_mem (mem_insert_of_mem (mem_insert_of_mem uc)),
      card_insert_of_not_mem (by simp [zh,zc]),card_insert_of_not_mem hc,c5,card_neighborFinset_eq_degree] at i
    exact i
  have final5 (u : V) : 5≤H4.degree u := by
    change 5≤(starClose H3 C).degree u
    by_cases uc : u∈C
    · have hi := star_degree_of_marked (G:=H3) C uc
      rw [n] at hi
      omega
    exact c5 ▸ star_degree_of_unmarked (G:=H3) C uc
  obtain ⟨p,pp,ps⟩ := hamilton_connected_of_ore (G:=H4)
    (fun u v _ _=>by rw [n]; have x:=final5 u; have y:=final5 v; omega) az
  have close4 (u v : V) (yes : H4.Adj u v) (no : ¬H3.Adj u v) :
      Fintype.card V+1≤H3.degree u+H3.degree v+(if u=z ∨ v=z then 1 else 0) := by
    rw [n]
    rcases yes with e|⟨_,uC|vC⟩
    · exact (no e).elim
    · have x := H36 u uC; have y := min3 v; omega
    · have x := min3 u; have y := H36 v vC; omega
  obtain ⟨p,pp,ps⟩ := weighted_terminal_ore_closure sub4 close4 p pp ps
  have close3 (u v : V) (yes : H3.Adj u v) (no : ¬H2.Adj u v) :
      Fintype.card V+1≤H2.degree u+H2.degree v+(if u=z ∨ v=z then 1 else 0) := by
    rw [n]
    rcases yes with e|⟨uv,ue,ve⟩
    · exact (no e).elim
    have d (t : V) (tc : t∈C) : 5≤H2.degree t :=
      (high t tc).trans ((local_degree_mono sub1 t).trans (local_degree_mono sub2 t))
    rcases mem_insert.mp ue with rfl|uC
    · have vC := (mem_insert.mp ve).resolve_left uv.symm
      have p := d v vC
      omega
    rcases mem_insert.mp ve with rfl|vC
    · have p := d u uC
      omega
    have p := d u uC; have q := d v vC; omega
  obtain ⟨p,pp,ps⟩ := weighted_terminal_ore_closure sub3 close3 p pp ps
  have close2 (u v : V) (yes : H2.Adj u v) (no : ¬H1.Adj u v) :
      Fintype.card V+1≤H1.degree u+H1.degree v+(if u=z ∨ v=z then 1 else 0) := by
    rw [n]
    rcases yes with e|⟨uv,ue,ve⟩
    · exact (no e).elim
    simp only [B,mem_insert,mem_singleton] at ue ve
    rcases ue with eu|eu
    · subst u
      have vh := ve.resolve_left uv.symm
      rw [if_pos (.inl rfl)]
      have v3 := min1 v
      omega
    subst u
    have vz := ve.resolve_right uv.symm
    subst v
    rw [if_pos (.inr rfl)]
    have h3 := min1 h
    omega
  obtain ⟨p,pp,ps⟩ := weighted_terminal_ore_closure sub2 close2 p pp ps
  have close1 (u v : V) (yes : H1.Adj u v) (no : ¬G.Adj u v) :
      Fintype.card V+1≤G.degree u+G.degree v+(if u=z ∨ v=z then 1 else 0) := by
    rw [n]
    rcases yes with e|⟨uv,ue,ve⟩
    · exact (no e).elim
    rcases mem_insert.mp ue with e|uC
    · subst u
      have x := low z; have y := high v ((mem_insert.mp ve).resolve_left uv.symm)
      rw [if_pos (.inl rfl)]
      omega
    rcases mem_insert.mp ve with e|vC
    · subst v
      have x := high u uC; have y := low z
      rw [if_pos (.inr rfl)]
      omega
    have x := high u uC; have y := high v vC; omega
  exact weighted_terminal_ore_closure sub1 close1 p pp ps

#print axioms eight_triple_core_closure
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
