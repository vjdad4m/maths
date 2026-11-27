import Deficiency
import Boundary

namespace RainbowCover1553
open SimpleGraph Finset HallRainbow1121 BullCover1125
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- A singleton labeling gives one different marked neighbor for each color. -/
theorem rainbow_demand {k : ℕ} {f : V → Fin (k+1)} (hf : Rainbow G f) :
    ∀ v ∉ univ.filter (fun u => f u ≠ 0),
      k ≤ ((univ.filter (fun u => f u ≠ 0)).filter (G.Adj v)).card := by
  intro v hv
  have zero : f v = 0 := by simpa using hv
  have witness (i : Fin k) := hf v zero i.succ (Fin.succ_ne_zero i)
  choose pick edge color using witness
  have inj : Function.Injective pick := fun i j eq =>
    Fin.succ_injective _ ((color i).symm.trans ((congrArg f eq).trans (color j)))
  suffices h : (univ : Finset (Fin k)).card ≤ ((univ.filter (fun u => f u ≠ 0)).filter (G.Adj v)).card by simpa using h
  apply card_le_card_of_injOn pick ?_ inj.injOn
  intro i _
  exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,(color i).symm ▸ Fin.succ_ne_zero i⟩,edge i⟩

theorem rainbow_edge_bound (iso : IsolateFree G) {k : ℕ} (hk : 0 < k) :
    edgeCoverNumber G ≤ rainbowNumber G k + degreeExcess G k / k := by
  let label : Fin (k+1) := ⟨1,Nat.succ_lt_succ hk⟩
  have nz : label ≠ 0 := fun h => Nat.one_ne_zero (congrArg Fin.val h)
  let sizes := {n | ∃ f : V → Fin (k+1), weight f=n ∧ Rainbow G f}
  have feasible : sizes.Nonempty :=
    ⟨_,fun _ => label,rfl,fun _ hv => False.elim (nz hv)⟩
  obtain ⟨f,cost,hf⟩ := Nat.sInf_mem feasible
  change weight f = rainbowNumber G k at cost
  let S := univ.filter (fun u => f u ≠ 0)
  have bound := cover_of_k_dominating G iso S hk (rainbow_demand G hf)
  have shift : crossExcess G S k / k ≤ degreeExcess G k / k := Nat.div_le_div_right (cross_le_degree_excess G S k)
  change S.card = rainbowNumber G k at cost
  rw [← cost]
  exact bound.trans (Nat.add_le_add_left shift _)

theorem row1553 (_order : 2 ≤ Fintype.card V) (subcubic : ∀ u, G.degree u ≤ 3)
    {r : ℕ} (numeric : edgeCoverValue G = some r) : r ≤ rainbowNumber G 3 := by
  classical
  by_cases iso : IsolateFree G
  · have eq : edgeCoverNumber G = r := by simpa [edgeCoverValue,iso] using numeric
    have budget : degreeExcess G 3 = 0 := by
      unfold degreeExcess
      exact sum_eq_zero (fun u _ => Nat.sub_eq_zero_of_le (subcubic u))
    simpa [eq,budget] using rainbow_edge_bound G iso (k:=3) (by decide)
  · simp [edgeCoverValue,iso] at numeric

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- Assign each vertex to a covering edge incident with it. Its color class
has at most two vertices, which are adjacent whenever they differ. -/
theorem clique_cover_le_edge_cover (iso : IsolateFree G) :
    vertexCliqueCover G ≤ edgeCoverNumber G := by
  classical
  obtain ⟨C,good⟩ := (coverable_iff G).mpr iso
  obtain ⟨P,sz,covers⟩ := Nat.sInf_mem (s:={n | ∃ P : Finset G.edgeSet, P.card=n ∧ Covers G P})
    ⟨_,C,rfl,good⟩
  change P.card = edgeCoverNumber G at sz
  choose edge member incident using covers
  let owner (x : V) : ↥P := ⟨edge x,member x⟩
  have proper {x y : V} (adj : Gᶜ.Adj x y) : owner x ≠ owner y := by
    intro eq
    have same : edge x = edge y := congrArg Subtype.val eq
    obtain ⟨ne,no⟩ := (G.compl_adj _ _).mp adj
    have order := (Sym2.mem_and_mem_iff ne).mp ⟨incident x,same ▸ incident y⟩
    exact no (show s(x,y) ∈ G.edgeSet from order ▸ (edge x).property)
  let col : Gᶜ.Coloring ↥P := Coloring.mk owner proper
  apply Nat.sInf_le
  simpa [sz] using col.colorable

local instance (k m : ℕ) : DecidableRel (biclique k m).Adj := fun a b => by
  change Decidable (a.isLeft ∧ b.isRight ∨ a.isRight ∧ b.isLeft)
  infer_instance

theorem biclique_excess {k m : ℕ} : degreeExcess (biclique k m) k = k*(m-k) := by
  unfold degreeExcess
  rw [Fintype.sum_sum_type]
  simp [(biclique_degrees k m).1,(biclique_degrees k m).2]

/-- The additive correction, including its coefficient, is attained for all
positive k and m ≥ k. The excess may therefore be arbitrarily large. -/
theorem sharp_family {k m : ℕ} (hk : 0 < k) (h : k ≤ m) :
    edgeCoverValue (biclique k m) = some m ∧ rainbowNumber (biclique k m) k = k ∧
    degreeExcess (biclique k m) k / k = m-k := by
  have iso : IsolateFree (biclique k m) := by
    rintro (a|b)
    · exact ⟨Sum.inr ⟨0,lt_of_lt_of_le hk h⟩,by simp [biclique,completeBipartiteGraph]⟩
    · exact ⟨Sum.inl ⟨0,hk⟩,by simp [biclique,completeBipartiteGraph]⟩
  have color := biclique_rainbow k m
  have q : degreeExcess (biclique k m) k / k = m-k := by
    rw [biclique_excess,Nat.mul_div_cancel_left _ hk]
  have lo := clique_cover_le_edge_cover (biclique k m) iso
  rw [biclique_cover h] at lo
  have hi := rainbow_edge_bound (biclique k m) iso hk
  rw [color,q] at hi
  have cover : edgeCoverNumber (biclique k m) = m := by omega
  exact ⟨by simp [edgeCoverValue,iso,cover],color,q⟩

theorem sharp_row : 2 ≤ Fintype.card (Fin 3 ⊕ Fin 3) ∧
    (∀ u, (biclique 3 3).degree u ≤ 3) ∧ edgeCoverValue (biclique 3 3) = some 3 ∧
    rainbowNumber (biclique 3 3) 3 = 3 := by
  obtain ⟨cover,rainbow,_⟩ := sharp_family (k:=3) (m:=3) (by decide) (by decide)
  exact ⟨by decide,Sum.forall.mpr ⟨fun a => ((biclique_degrees 3 3).1 a).le,
    fun b => ((biclique_degrees 3 3).2 b).le⟩,cover,rainbow⟩

#print axioms sharp_row
#print axioms deficiency
#print axioms cover_of_k_dominating
#print axioms rainbow_edge_bound
#print axioms row1553
#print axioms clique_cover_le_edge_cover
#print axioms biclique_excess
#print axioms sharp_family
end RainbowCover1553
