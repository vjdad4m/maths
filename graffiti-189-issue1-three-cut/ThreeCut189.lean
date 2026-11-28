import Base189
namespace Issue189
set_option maxHeartbeats 12000000
set_option maxRecDepth 100000
def d (u v : V) : Nat := if u = v then 0 else if bag u = bag v then 1 else len (bag u) (bag v)
def hop (u v : V) := if d u v ≤ 1 then v else step (bag u) (bag v)
theorem descend : ∀ u v : V, u ≠ v → G.Adj u (hop u v) ∧
    d (hop u v) v + 1 = d u v := by decide
theorem walk_of_d (u v : V) : ∃ p : G.Walk u v, p.length = d u v := by
  by_cases e : u = v
  · subst v; exact ⟨.nil,by simp [d]⟩
  · obtain ⟨he, hl⟩ := descend u v e
    obtain ⟨p,hp⟩ := walk_of_d (hop u v) v
    exact ⟨p.cons he, by simpa [hp] using hl⟩
termination_by d u v
decreasing_by omega
theorem connected : G.Connected := ⟨fun u v => ⟨(walk_of_d u v).choose⟩⟩
theorem base_lipschitz : ∀ i j k : I, touch i j → len i k ≤ len j k + 1 := by decide
theorem base_off_diag : ∀ i j : I, i ≠ j → 1 ≤ len i j := by decide
theorem ext_lipschitz {u w : V} (h : G.Adj u w) (v : V) : d u v ≤ d w v + 1 := by
  rcases (show adj u w from h) with ⟨hne, hj⟩
  by_cases eu : u = v
  · simp [d,eu]
  by_cases ew : w = v
  · subst v; rcases hj with hj | hj
    · simp [d,eu,hj]
    · change len (bag u) (bag w) = 1 at hj
      simp [d,eu,hj]
  by_cases bu : bag u = bag v
  · simp [d, eu, bu]
  by_cases bw : bag w = bag v
  · rcases hj with e|e
    · exact False.elim (bu (e.trans bw))
    · simp [d,eu,ew,bu,bw]; rw [←bw]; exact Nat.le_trans (Nat.le_of_eq e) (by decide : 1 ≤ 1 + 1)
  rcases hj with e|e
  · simp [d,eu,ew,bu,bw,e]
  · simpa [d,eu,ew,bu,bw] using base_lipschitz _ _ _ e
theorem d_le_walk {u v : V} (p : G.Walk u v) : d u v ≤ p.length := by
  induction p with
  | nil => simp [d]
  | cons h _ ih => exact (ext_lipschitz h _).trans (Nat.add_le_add_right ih 1)
theorem dist_eq (u v : V) : G.dist u v = d u v := by
  obtain ⟨p,hp⟩ := walk_of_d u v
  obtain ⟨q,hq⟩ := connected.exists_walk_length_eq_dist u v
  exact le_antisymm (hp ▸ G.dist_le p) (hq ▸ d_le_walk q)
def degC (u : V) := (Finset.univ.filter (G.Adj u)).card
theorem degree_eq (u : V) : G.degree u = degC u := by
  rw [← G.card_neighborFinset_eq_degree, G.neighborFinset_eq_filter]; rfl
def evC (u : V) := (Finset.univ.filter (fun v => Even (d u v))).card
noncomputable def ev (u : V) := (Finset.univ.filter (fun v => Even (G.dist u v))).card
theorem even_eq (u : V) : ev u = evC u := by simp only [ev,evC,dist_eq]
/-- Lower bound for every vertex together with two distinct attaining it pins
both the smallest and the second-smallest degree to 15. -/
theorem hypotheses : (∀ u : V, 15 ≤ G.degree u ∧ ev u ≤ 16) ∧
    G.degree 21 = 15 ∧ G.degree 22 = 15 ∧ ev 0 = 16 := by
  simp only [degree_eq,even_eq]
  decide
#print axioms hypotheses
end Issue189
