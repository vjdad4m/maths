import Factor
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace RegularCliques1957
open SimpleGraph Finset Graffiti326 AutoGraphForge378 HallRainbow1121 TriangleMatching1078

abbrev Index (n : ℕ) := Fin (n+1)
abbrev Core (n : ℕ) := Option (Index n)
abbrev Slot (n : ℕ) := Core n ⊕ Index n
abbrev Vertex (n : ℕ) := Bool × Slot n

/-- Core slots on opposite sides have a private matching. Satellite slots
see every core on the opposite side. -/
def compatible {n} : Slot n → Slot n → Prop
  | .inl i, .inl j => i = j
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr _, .inr _ => False

def graph (n : ℕ) : SimpleGraph (Vertex n) where
  Adj x y := x.1 ≠ y.1 ∧ compatible x.2 y.2
  symm := by
    rintro ⟨b,i⟩ ⟨c,j⟩ ⟨h,e⟩
    exact ⟨h.symm,by cases i <;> cases j <;> simp_all [compatible]⟩
  loopless := fun _ e => e.1 rfl

instance (n) : DecidableRel (graph n).Adj := by
  rintro ⟨b,i⟩ ⟨c,j⟩
  cases i <;> cases j <;> dsimp [graph,compatible] <;> infer_instance

theorem regular (n) : (graph n).IsRegularOfDegree (n+2) := by
  rintro ⟨b,i|j⟩
  · let leaf : Index n ↪ Vertex n := ⟨fun t => (!b,.inr t), fun _ _ e => Sum.inr.inj (Prod.mk.inj e).2⟩
    have neighbors : (graph n).neighborFinset (b,.inl i) =
        insert (!b,.inl i) (univ.map leaf) := by
      ext y
      rcases y with ⟨c,j|t⟩ <;> cases b <;> cases c <;>
        simp [mem_neighborFinset,graph,compatible,leaf,eq_comm]
    change ((graph n).neighborFinset (b,.inl i)).card = n+2
    rw [neighbors,card_insert_of_not_mem (by simp [leaf]),card_map,card_univ,Fintype.card_fin]
  · let core : Core n ↪ Vertex n := ⟨fun t => (!b,.inl t), fun _ _ e => Sum.inl.inj (Prod.mk.inj e).2⟩
    have neighbors : (graph n).neighborFinset (b,.inr j) = univ.map core := by
      ext y
      rcases y with ⟨c,t|k⟩ <;> cases b <;> cases c <;>
        simp [mem_neighborFinset,graph,compatible,core]
    change ((graph n).neighborFinset (b,.inr j)).card = n+2
    rw [neighbors,card_map,card_univ,Fintype.card_option,Fintype.card_fin]

theorem connected (n) : (graph n).Connected := by
  let hub (b : Bool) : Vertex n := (b,.inl none)
  have bridge : (graph n).Adj (hub false) (hub true) := ⟨Bool.false_ne_true,rfl⟩
  have hubs (b : Bool) : (graph n).Reachable (hub false) (hub b) := by
    cases b
    · exact Reachable.rfl
    · exact bridge.reachable
  have core (b : Bool) (i : Core n) : (graph n).Reachable (hub b) (b,.inl i) := by
    have a : (graph n).Adj (hub b) (!b,.inr (0 : Index n)) := ⟨by cases b <;> simp [hub],trivial⟩
    have z : (graph n).Adj (!b,.inr (0 : Index n)) (b,.inl i) := ⟨by cases b <;> simp [hub],trivial⟩
    exact a.reachable.trans z.reachable
  have reach (x : Vertex n) : (graph n).Reachable (hub false) x := by
    rcases x with ⟨b,i|j⟩
    · exact (hubs b).trans (core b i)
    · have e : (graph n).Adj (hub (!b)) (b,.inr j) := ⟨by cases b <;> simp [hub],trivial⟩
      exact (hubs (!b)).trans e.reachable
  exact ⟨fun x y => (reach x).symm.trans (reach y)⟩

theorem triangle_free (n) : TriangleFree (graph n) := by
  have bits : ∀ a b c : Bool, a ≠ b → b ≠ c → c ≠ a → False := by decide
  exact fun a b c h j k => bits _ _ _ h.1 j.1 k.1

theorem order (n) : Fintype.card (Vertex n) = 4*n+6 := by
  simp [Vertex,Slot,Core,Index,Fintype.card_sum,Fintype.card_prod]; omega

theorem private_matching (n) : HasMaximalMatching (graph n) (n+2) := by
  let e : Fin (n+2) ≃ Core n := finSuccEquiv (n := n+1)
  let f : Fin (n+2) × Bool ↪ Vertex n :=
    ⟨fun z => (z.2,.inl (e z.1)), by
      rintro ⟨i,b⟩ ⟨j,c⟩ he
      obtain ⟨bc,ij⟩ := Prod.mk.inj he
      exact Prod.ext (e.injective (Sum.inl.inj ij)) bc⟩
  have used (b : Bool) (j : Core n) : (b,.inl j) ∈ support f := by
    apply (Graffiti326.mem_support f).mpr
    exact ⟨e.symm j,b,by simp [f]⟩
  refine ⟨f,fun _ => ⟨Bool.false_ne_true,rfl⟩,?_⟩
  rintro ⟨b,i|j⟩ hu ⟨c,k|t⟩ hv edge
  · exact hu (used b i)
  · exact hu (used b i)
  · exact hv (used c k)
  · exact edge.2

theorem edge_exact (n) : lineDomination (graph n) = n+2 ∧
    minMaximalMatching (graph n) = n+2 := by
  have size := order n
  obtain ⟨h,_⟩ := row1078 (graph n) (by omega) ⟨_,regular n⟩ (triangle_free n)
  rw [average_regular _ (regular n)] at h
  have lower : n+2 ≤ lineDomination (graph n) := by exact_mod_cast h
  have middle := lineDomination_le_matching (graph n)
  have upper : minMaximalMatching (graph n) ≤ n+2 := Nat.sInf_le (private_matching n)
  omega

/-- An explicit perfect matching: swap each indexed core with its satellite
across sides and join the two unindexed cores. -/
def partner {n} : Slot n → Slot n
  | .inl none => .inl none
  | .inl (some j) => .inr j
  | .inr j => .inl (some j)

theorem clique_exact (n) : vertexCliqueCover (graph n) = 2*n+3 := by
  have size : Fintype.card (Slot n) = 2*n+3 := by
    simp [Slot,Core,Index,Fintype.card_sum]; omega
  have pair (j : Slot n) : compatible j (partner j) := by
    rcases j with (_ | k) | k <;> trivial
  have inv (j : Slot n) : partner (partner j) = j := by
    rcases j with (_ | k) | k <;> rfl
  let color : Vertex n → Slot n := fun v => if v.1 then partner v.2 else v.2
  have proper {v w : Vertex n} (adj : (graph n)ᶜ.Adj v w) : color v ≠ color w := by
    obtain ⟨ne,no⟩ := ((graph n).compl_adj _ _).mp adj
    rcases v with ⟨b,i⟩
    rcases w with ⟨c,j⟩
    cases b <;> cases c <;> simp only [color,Bool.false_eq_true,if_false,if_true]
    · exact fun h => ne (Prod.ext rfl h)
    · intro h
      exact no ⟨Bool.false_ne_true,h ▸ (graph n).symm (show (graph n).Adj (true,j) (false,partner j) from ⟨Bool.false_ne_true.symm,pair j⟩) |>.2⟩
    · intro h
      exact no ⟨Bool.false_ne_true.symm,h ▸ pair i⟩
    · exact fun h => ne (Prod.ext rfl ((inv i).symm.trans ((congrArg partner h).trans (inv j))))
  let col : (graph n)ᶜ.Coloring (Slot n) := Coloring.mk color proper
  have upper : vertexCliqueCover (graph n) ≤ Fintype.card (Slot n) := Nat.sInf_le col.colorable
  obtain ⟨opt⟩ := Nat.sInf_mem (s:={k | (graph n)ᶜ.Colorable k}) ⟨_,(graph n)ᶜ.colorable_of_fintype⟩
  let entries (j : Slot n) := opt (false,j)
  have inj : Function.Injective entries := by
    intro i j h
    apply Classical.byContradiction
    intro diff
    exact opt.valid (((graph n).compl_adj _ _).mpr
      ⟨fun e => diff (Prod.mk.inj e).2,fun e => e.1 rfl⟩) h
  have lower := Fintype.card_le_of_injective entries inj
  change Fintype.card (Slot n) ≤ Fintype.card (Fin (vertexCliqueCover (graph n))) at lower
  rw [Fintype.card_fin] at lower
  omega

end RegularCliques1957
