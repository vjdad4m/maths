import MixedSplice

namespace Graffiti199Depleted.Catalogue.CubicMixedCut

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] [Fintype V] (F : CubicMixedCut G)

theorem universal_inner_of_nonadjacent (budget : treeNumber G ≤ 5)
    (bcOff : ¬ G.Adj F.b F.c) {x y : V} (hx : x ∈ F.inner) (hy : y ∈ F.B) (ne : x ≠ y) :
    G.Adj x y := by
  rcases F.split_B hy with rfl|rfl|inner
  · exact (F.both_contacts_of_nonadjacent budget bcOff hx).1.symm
  · exact (F.both_contacts_of_nonadjacent budget bcOff hx).2.symm
  · exact F.inner_adjacent_of_common_contact budget F.rb F.bB hx inner ne
      (F.both_contacts_of_nonadjacent budget bcOff hx).1
      (F.both_contacts_of_nonadjacent budget bcOff inner).1

omit [Fintype V] in
private theorem inner_nonempty_of_nonadjacent (bcOff : ¬ G.Adj F.b F.c) :
    F.inner.Nonempty := by
  obtain ⟨w⟩ := F.connB.preconnected ⟨F.b,F.bB⟩ ⟨F.c,F.cB⟩
  have ne : (⟨F.b,F.bB⟩ : F.B) ≠ ⟨F.c,F.cB⟩ :=
    fun e => F.bc (congrArg (fun a : F.B => a.val) e)
  have e : G.Adj F.b w.snd.val := w.adj_snd (Walk.not_nil_of_ne (p := w) ne)
  exact ⟨w.snd.val,w.snd.property,e.ne.symm,fun h => bcOff (h ▸ e)⟩

/-- A reserve vertex of the clique interior supplies the only missing
connector in the nonadjacent-neighbor case. -/
theorem route_of_one_missing_edge (budget : treeNumber G ≤ 5) (bcOff : ¬ G.Adj F.b F.c)
    {u x y : V} (hu : u ∈ F.inner) (hx : x ∈ F.B) (hy : y ∈ F.B)
    (ux : u ≠ x) (uy : u ≠ y) (xy : x ≠ y) : Traverses G F.B x y := by
  have make {L : List V} {v w : V} (two : 2 ≤ L.length) (nd : L.Nodup)
      (ch : L.Chain' G.Adj) (first : L.head? = some v) (last : L.getLast? = some w)
      (mem : ∀ t ∈ L, t ∈ F.B) (bL : F.b ∈ L) (cL : F.c ∈ L) : Traverses G F.B v w := by
    apply traverses_of_universal_extension two nd ch first last mem
    intro n nB nL t tB nt
    rcases F.split_B nB with rfl|rfl|inner
    · exact (nL bL).elim
    · exact (nL cL).elim
    · exact F.universal_inner_of_nonadjacent budget bcOff inner tB nt
  have ub := (F.both_contacts_of_nonadjacent budget bcOff hu).1
  have uc := (F.both_contacts_of_nonadjacent budget bcOff hu).2
  have pair : Traverses G F.B F.b F.c := by
    apply make (L := [F.b,u,F.c]) (by simp)
    · simp [hu.2.1.symm,hu.2.2,F.bc]
    · simp [List.chain'_cons,ub,uc.symm,List.chain'_singleton]
    · rfl
    · rfl
    · intro v hv
      rcases (show v = F.b ∨ v = u ∨ v = F.c by simpa using hv) with rfl|rfl|rfl
      · exact F.bB
      · exact hu.1
      · exact F.cB
    · simp
    · simp
  have start {v : V} (vi : v ∈ F.inner) (uv : u ≠ v) :
      Traverses G F.B F.b v ∧ Traverses G F.B F.c v := by
    have vb := (F.both_contacts_of_nonadjacent budget bcOff vi).1
    have vc := (F.both_contacts_of_nonadjacent budget bcOff vi).2
    constructor
    · apply make (L := [F.b,u,F.c,v]) (by simp)
      · simp [hu.2.1.symm,hu.2.2,F.bc,vi.2.1.symm,vi.2.2.symm,uv]
      · simp [List.chain'_cons,ub,uc.symm,vc,List.chain'_singleton]
      · rfl
      · rfl
      · intro w hm
        rcases (show w = F.b ∨ w = u ∨ w = F.c ∨ w = v by simpa using hm) with rfl|rfl|rfl|rfl
        · exact F.bB
        · exact hu.1
        · exact F.cB
        · exact vi.1
      · simp
      · simp
    · apply make (L := [F.c,u,F.b,v]) (by simp)
      · simp [hu.2.1,hu.2.2.symm,F.bc.symm,vi.2.1.symm,vi.2.2.symm,uv]
      · simp [List.chain'_cons,uc,ub.symm,vb,List.chain'_singleton]
      · rfl
      · rfl
      · intro w hm
        rcases (show w = F.c ∨ w = u ∨ w = F.b ∨ w = v by simpa using hm) with rfl|rfl|rfl|rfl
        · exact F.cB
        · exact hu.1
        · exact F.bB
        · exact vi.1
      · simp
      · simp
  rcases F.split_B hx with rfl|rfl|xi <;> rcases F.split_B hy with rfl|rfl|yi
  · exact (xy rfl).elim
  · exact pair
  · exact (start yi uy).1
  · exact pair.reverse
  · exact (xy rfl).elim
  · exact (start yi uy).2
  · exact (start xi ux).1.reverse
  · exact (start xi ux).2.reverse
  · have xb := (F.both_contacts_of_nonadjacent budget bcOff xi).1
    have yc := (F.both_contacts_of_nonadjacent budget bcOff yi).2
    apply make (L := [x,F.b,u,F.c,y]) (by simp)
    · simp [xi.2.1,xi.2.2,hu.2.1.symm,hu.2.2,F.bc,yi.2.1.symm,yi.2.2.symm,ux.symm,uy,xy]
    · simp [List.chain'_cons,xb.symm,ub,uc.symm,yc,List.chain'_singleton]
    · rfl
    · rfl
    · intro w hm
      rcases (show w = x ∨ w = F.b ∨ w = u ∨ w = F.c ∨ w = y by simpa using hm) with
        rfl|rfl|rfl|rfl|rfl
      · exact xi.1
      · exact F.bB
      · exact hu.1
      · exact F.cB
      · exact yi.1
    · simp
    · simp

omit [Fintype V] in
private theorem neighbor_options_of_missing_edge (bcOff : ¬ G.Adj F.b F.c) {s v : V}
    (side : s = F.b ∨ s = F.c) (edge : G.Adj s v) :
    v ∈ F.inner ∨ v = F.r ∨ v = F.p ∨ v = F.q := by
  have sB := side.elim (fun eq => eq.symm ▸ F.bB) (fun eq => eq.symm ▸ F.cB)
  rcases F.other_contacts_of_B_edge sB edge with vB|small
  · rcases F.split_B vB with rfl|rfl|inner
    · rcases side with rfl|rfl
      · exact (G.loopless _ edge).elim
      · exact (bcOff edge.symm).elim
    · rcases side with rfl|rfl
      · exact (bcOff edge).elim
      · exact (G.loopless _ edge).elim
    · exact Or.inl inner
  · exact Or.inr small

variable [DecidableRel G.Adj]

/-- In the nonadjacent-neighbor case, choose two distinct port contacts
while reserving an interior vertex. When the interior has order one or
two, the degree-four bounds give the required port edges at the two
exceptional vertices. -/
theorem reserve_inner (conn : ConnectivityAtLeast G 3) (bcOff : ¬ G.Adj F.b F.c)
    (highB : 4 ≤ G.degree F.b) (highC : 4 ≤ G.degree F.c) :
    ∃ x ∈ F.B, ∃ y ∈ F.B, ∃ u ∈ F.inner, x ≠ y ∧ u ≠ x ∧ u ≠ y ∧
      G.Adj F.p x ∧ G.Adj F.q y := by
  classical
  obtain ⟨x,xB,y,yB,xy,px,qy⟩ := F.distinct_contacts_to_B conn
  by_cases spare : ∃ u ∈ F.inner, u ≠ x ∧ u ≠ y
  · obtain ⟨u,hu,ux,uy⟩ := spare
    exact ⟨x,xB,y,yB,u,hu,xy,ux,uy,px,qy⟩
  have count (v : V) (hv : v ∈ F.inner) : v = x ∨ v = y := by
    by_cases xEq : v = x
    · exact Or.inl xEq
    · exact Or.inr (Classical.byContradiction (fun yOff => spare ⟨v,hv,xEq,yOff⟩))
  have both_small (u : V) (hu : u ∈ F.inner) (single : ∀ v ∈ F.inner, v = u) :
      ∃ x ∈ F.B, ∃ y ∈ F.B, ∃ w ∈ F.inner, x ≠ y ∧ w ≠ x ∧ w ≠ y ∧
        G.Adj F.p x ∧ G.Adj F.q y := by
    have pb : G.Adj F.p F.b := by
      by_contra no
      have bound := degree_le_three_of_three_names (G := G) (v := F.b) (x := u) (y := F.r) (z := F.q)
        (by
          intro v bv
          rcases F.neighbor_options_of_missing_edge bcOff (Or.inl rfl) bv with vI|rv|pv|qv
          · exact Or.inl (single _ vI)
          · exact Or.inr (Or.inl rv)
          · exact (no (pv ▸ bv).symm).elim
          · exact Or.inr (Or.inr qv))
      omega
    have qc : G.Adj F.q F.c := by
      by_contra no
      have bound := degree_le_three_of_three_names (G := G) (v := F.c) (x := u) (y := F.r) (z := F.p)
        (by
          intro v cv
          rcases F.neighbor_options_of_missing_edge bcOff (Or.inr rfl) cv with vI|rv|pv|qv
          · exact Or.inl (single _ vI)
          · exact Or.inr (Or.inl rv)
          · exact Or.inr (Or.inr pv)
          · exact (no (qv ▸ cv).symm).elim)
      omega
    exact ⟨F.b,F.bB,F.c,F.cB,u,hu,F.bc,hu.2.1,hu.2.2,pb,qc⟩
  by_cases hx : x ∈ F.inner
  · by_cases hy : y ∈ F.inner
    · have touch : G.Adj F.p F.b ∨ G.Adj F.q F.b := by
        by_contra missing
        have bound := degree_le_three_of_three_names (G := G) (v := F.b) (x := x) (y := y) (z := F.r)
          (by
            intro v e
            rcases F.neighbor_options_of_missing_edge bcOff (Or.inl rfl) e with vI|rv|pv|qv
            · exact (count _ vI).imp id Or.inl
            · exact Or.inr (Or.inr rv)
            · exact (missing (Or.inl (pv ▸ e).symm)).elim
            · exact (missing (Or.inr (qv ▸ e).symm)).elim)
        omega
      rcases touch with pb|qb
      · exact ⟨F.b,F.bB,y,yB,x,hx,hy.2.1.symm,hx.2.1,xy,pb,qy⟩
      · exact ⟨x,xB,F.b,F.bB,y,hy,hx.2.1,xy.symm,hy.2.1,px,qb⟩
    · exact both_small x hx (fun v h => (count v h).resolve_right (fun e => hy (e ▸ h)))
  · by_cases hy : y ∈ F.inner
    · exact both_small y hy (fun v h => (count v h).resolve_left (fun e => hx (e ▸ h)))
    · obtain ⟨v,hv⟩ := F.inner_nonempty_of_nonadjacent bcOff
      exact ((count v hv).elim (fun e => hx (e ▸ hv)) (fun e => hy (e ▸ hv))).elim

/-- The nonadjacent pair on the nonclique side of the mixed cubic cut
is excluded altogether in the independent-cubic branch. -/
theorem traceable_of_nonadjacent_ports (conn : ConnectivityAtLeast G 3) (budget : treeNumber G ≤ 5)
    (bcOff : ¬ G.Adj F.b F.c) (highB : 4 ≤ G.degree F.b) (highC : 4 ≤ G.degree F.c) : Traceable G := by
  obtain ⟨x,hx,y,hy,u,hu,xy,ux,uy,px,qy⟩ := F.reserve_inner conn bcOff highB highC
  exact F.finish_of_B_path conn (F.route_of_one_missing_edge budget bcOff hu hx hy ux uy xy) px qy

#print axioms traceable_of_nonadjacent_ports

end Graffiti199Depleted.Catalogue.CubicMixedCut
