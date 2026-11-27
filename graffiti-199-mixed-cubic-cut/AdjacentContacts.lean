import UniversalBridgeRoute

namespace Graffiti199Depleted.Catalogue.CubicMixedCut

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [Fintype V] (F : CubicMixedCut G)

omit [Fintype V] in
def swap : CubicMixedCut G :=
  { F with
      b := F.c
      c := F.b
      bB := F.cB
      cB := F.bB
      bc := F.bc.symm
      neighbors := fun x => (F.neighbors x).trans (by tauto) }

omit [Fintype V] in
theorem swap_inner : F.swap.inner = F.inner := by
  ext x
  simp only [swap,inner,Set.mem_setOf_eq]
  tauto

omit [Fintype V] in
theorem swap_leftOnly : F.swap.leftOnly = F.rightOnly := by
  ext x
  change (x ∈ F.swap.inner ∧ G.Adj F.c x ∧ ¬ G.Adj F.b x) ↔ x ∈ F.rightOnly
  rw [F.swap_inner]
  rfl

omit [Fintype V] in
theorem swap_left : F.swap.leftBlock = F.rightBlock := by
  change {F.c} ∪ F.swap.leftOnly = _
  rw [F.swap_leftOnly]
  rfl

omit [Fintype V] in
theorem swap_hub : F.swap.hub = F.hub := by
  ext x
  change (x ∈ F.swap.inner ∧ G.Adj F.c x ∧ G.Adj F.b x) ↔ x ∈ F.hub
  rw [F.swap_inner]
  change _ ↔ x ∈ F.inner ∧ G.Adj F.b x ∧ G.Adj F.c x
  tauto

theorem boundary_of_leftOnly (budget : treeNumber G ≤ 5) {x y : V}
    (xl : x ∈ F.leftOnly) (yOff : y ∉ F.leftOnly) (xy : G.Adj x y) :
    y = F.b ∨ y = F.p ∨ y = F.q ∨ y ∈ F.hub := by
  rcases F.other_contacts_of_B_edge xl.1.1 xy with yB|rr|pp|qq
  · have yAll : y ∈ (F.leftBlock ∪ F.rightBlock) ∪ F.hub := (F.blocks_cover budget).symm ▸ yB
    rcases yAll with ((yb|l)|r)|h
    · exact Or.inl yb
    · exact (yOff l).elim
    · exact (xl.1.2.1 ((F.bridge_only budget (Or.inr xl) r xy).1)).elim
    · exact Or.inr (Or.inr (Or.inr h))
  · exact (F.off_r_of_inner xl.1 (rr ▸ xy).symm).elim
  · exact Or.inr (Or.inl pp)
  · exact Or.inr (Or.inr (Or.inl qq))

/-- With a unique hub, some outer port contacts every nonempty exclusive wing. -/
theorem some_port_into_leftOnly (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    {h : V} (hHub : h ∈ F.hub) (single : F.hub ⊆ {h}) (nonempty : F.leftOnly.Nonempty) :
    ∃ x ∈ F.leftOnly, G.Adj F.p x ∨ G.Adj F.q x := by
  classical
  by_cases pTouch : ∃ x ∈ F.leftOnly, G.Adj F.p x
  · obtain ⟨x,hi,px⟩ := pTouch
    exact ⟨x,hi,Or.inl px⟩
  let Sep : Finset V := {F.b,F.q,h}
  have off (d : V) (dSep : d ∈ Sep) : d ∉ F.leftOnly := by
    intro dl
    rcases (show d = F.b ∨ d = F.q ∨ d = h by simpa [Sep] using dSep) with e|e|e
    · exact dl.1.2.1 e
    · exact F.offB F.q (by simp) (e ▸ dl.1.1)
    · exact Set.disjoint_left.mp F.hubApart (Or.inl (Or.inr dl))
        (e.symm ▸ hHub)
  have bound : ShoreBoundary G Sep F.leftOnly := by
    intro x xl y yOff edge
    rcases F.boundary_of_leftOnly budget xl yOff edge with e|e|e|yH
    · simp [Sep,e]
    · exact (pTouch ⟨x,xl,(e ▸ edge).symm⟩).elim
    · simp [Sep,e]
    · have e : y = h := single yH
      simp [Sep,e]
  obtain ⟨x,hl,qx⟩ := contact_of_shore conn (card_triple_le ..) off bound nonempty
    (show F.q ∈ Sep from by simp [Sep])
  exact ⟨x,hl,Or.inr qx⟩

variable [DecidableRel G.Adj]

/-- Without a common hub, either port can reach a suitable first
vertex in the left clique. -/
theorem left_contact_without_hub (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (noHub : ∀ h, h ∉ F.hub) (bHigh : 4 ≤ G.degree F.b) {s : V}
    (port : s = F.p ∨ s = F.q) :
    ∃ x ∈ F.leftBlock, (x ≠ F.b ∨ F.leftBlock = {F.b}) ∧ G.Adj s x := by
  classical
  by_cases has : F.leftOnly.Nonempty
  · let Sep : Finset V := {F.b,F.p,F.q}
    have off (d : V) (dSep : d ∈ Sep) : d ∉ F.leftOnly := by
      intro dl
      rcases (show d = F.b ∨ d = F.p ∨ d = F.q by simpa [Sep] using dSep) with e|e|e
      · exact dl.1.2.1 e
      · exact F.offB _ (by simp [e]) dl.1.1
      · exact F.offB _ (by simp [e]) dl.1.1
    have bound : ShoreBoundary G Sep F.leftOnly := by
      intro x xl y yOff edge
      rcases F.boundary_of_leftOnly budget xl yOff edge with e|e|e|h
      · simp [Sep,e]
      · simp [Sep,e]
      · simp [Sep,e]
      · exact (noHub _ h).elim
    have sSep : s ∈ Sep := by rcases port with rfl|rfl <;> simp [Sep]
    obtain ⟨x,hl,sx⟩ := contact_of_shore conn (card_triple_le ..) off bound has sSep
    exact ⟨x,Or.inr hl,Or.inl hl.1.2.1,sx⟩
  · have left : F.leftBlock = {F.b} := by
      ext x
      exact ⟨fun h => h.resolve_right (fun xl => has ⟨x,xl⟩),Or.inl⟩
    have within (x : V) (xB : x ∈ F.B) (e : G.Adj F.b x) : x = F.c := by
      have all : x ∈ (F.leftBlock ∪ F.rightBlock) ∪ F.hub := (F.blocks_cover budget).symm ▸ xB
      rcases all with (l|r)|h
      · have eq : x ∈ ({F.b} : Set V) := left ▸ l
        exact (e.ne.symm eq).elim
      · exact (F.bridge_only budget (Or.inl rfl) r e).2
      · exact (noHub _ h).elim
    have all (x : V) (e : G.Adj F.b x) : x = F.c ∨ x = F.r ∨ x = F.p ∨ x = F.q := by
      rcases F.other_contacts_of_B_edge F.bB e with b|out
      · exact Or.inl (within x b e)
      · exact Or.inr out
    have sb : G.Adj s F.b := by
      by_contra! no
      rcases port with rfl|rfl
      · have lo := degree_le_three_of_three_names (G := G) (v := F.b)
          (x := F.c) (y := F.r) (z := F.q) (by
            intro x e
            rcases all x e with c|r|p|q
            · exact Or.inl c
            · exact Or.inr (Or.inl r)
            · exact (no (p ▸ e).symm).elim
            · exact Or.inr (Or.inr q))
        omega
      · have lo := degree_le_three_of_three_names (G := G) (v := F.b)
          (x := F.c) (y := F.r) (z := F.p) (by
            intro x e
            rcases all x e with c|r|p|q
            · exact Or.inl c
            · exact Or.inr (Or.inl r)
            · exact Or.inr (Or.inr p)
            · exact (no (q ▸ e).symm).elim)
        omega
    exact ⟨F.b,Or.inl rfl,Or.inr left,sb⟩

end Graffiti199Depleted.Catalogue.CubicMixedCut
