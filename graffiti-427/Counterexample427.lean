import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Finite.Card
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! Counterexample to the November 2026 corrected cut-vertex statement of WOW II #427. -/

namespace Graffiti427
open Finset SimpleGraph

section Definitions
variable {V : Type*}

noncomputable def componentCount (G : SimpleGraph V) : ℕ :=
  Nat.card G.ConnectedComponent

def deleteVertex (G : SimpleGraph V) (v : V) : SimpleGraph {w : V // w ≠ v} :=
  G.induce {w | w ≠ v}

/-- Catalogue definition 106, comparing the two component counts. -/
def IsCutVertex (G : SimpleGraph V) (v : V) : Prop :=
  componentCount G < componentCount (deleteVertex G v)

theorem finiteComponents [Finite V] (G : SimpleGraph V) : Finite G.ConnectedComponent :=
  Finite.of_surjective G.connectedComponentMk fun c => c.exists_rep

theorem componentCount_eq_one {G : SimpleGraph V} (h : G.Connected) :
    componentCount G = 1 := by
  classical
  letI : Unique G.ConnectedComponent :=
    { default := G.connectedComponentMk (Classical.choice h.nonempty)
      uniq := fun x => by
        obtain ⟨v,rfl⟩ := x.exists_rep
        exact ConnectedComponent.sound (h v _) }
  unfold componentCount
  exact Nat.card_unique

variable [Fintype V] (G : SimpleGraph V)

noncomputable def cutVertices : Finset V :=
  @Finset.filter V (IsCutVertex G) (fun _ => Classical.propDecidable _) univ

theorem mem_cutVertices {v : V} : v ∈ cutVertices G ↔ IsCutVertex G v := by
  unfold cutVertices
  exact (@Finset.mem_filter V _ (fun _ => Classical.propDecidable _) univ v).trans
    ⟨And.right,fun h => ⟨mem_univ v,h⟩⟩

/-- Catalogue definition 7. Only independence constrains already selected vertices. -/
def IndependentDominates (D : Finset V) : Prop :=
  G.IsIndepSet (D : Set V) ∧ ∀ v, v ∈ D ∨ ∃ w ∈ D, G.Adj v w

noncomputable def independentDominationNumber : ℕ :=
  sInf {k : ℕ | ∃ D, IndependentDominates G D ∧ D.card = k}

variable [DecidableEq V] [DecidableRel G.Adj]

def pendants : Finset V := univ.filter (fun v => G.degree v = 1)

def openNeighborhood (S : Finset V) : Finset V := univ.filter (fun v => ∃ w ∈ S, G.Adj v w)

/-- An unordered edge is counted once when its endpoints are in opposite parts. -/
def cutEdges (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (fun e => ∃ u ∈ S, ∃ v ∉ S, e = s(u,v))

def remainderEdges : ℕ :=
  (G.induce ((univ \ openNeighborhood G (pendants G) : Finset V) : Set V)).edgeFinset.card

noncomputable def floorTerm : ℤ :=
  Int.floor ((2 / 3 : ℚ) * (remainderEdges G : ℚ))

noncomputable def catalogueRhs : ℤ :=
  ((cutEdges G (cutVertices G)).card : ℤ) + floorTerm G

end Definitions

abbrev Vertex := Fin 24
abbrev Branch := Fin 4
abbrev Part := Branch × Fin 3

private def group (v : Vertex) : ℕ := v.val / 6
private def role (v : Vertex) : ℕ := v.val % 6

/-- Each branch has vertices s,x,y,t,a,b in that order. The s vertices form a clique. -/
def branchVertex (i : Branch) (r : Fin 6) : Vertex := ⟨6 * i.val + r.val,by omega⟩

private def branchEdges : Finset (ℕ × ℕ) := {(0,1),(1,2),(2,3),(0,4),(3,5)}

def witnessAdj (u v : Vertex) : Prop :=
  (role u = 0 ∧ role v = 0 ∧ u ≠ v) ∨
    (group u = group v ∧
      ((role u,role v) ∈ branchEdges ∨ (role v,role u) ∈ branchEdges))

instance (u v : Vertex) : Decidable (witnessAdj u v) := by
  unfold witnessAdj
  infer_instance

private theorem witness_symm : ∀ u v : Vertex, witnessAdj u v → witnessAdj v u := by decide

private theorem witness_loopless : ∀ v : Vertex, ¬ witnessAdj v v := by decide

def witness : SimpleGraph Vertex where
  Adj := witnessAdj
  symm := witness_symm
  loopless := witness_loopless

instance : DecidableRel witness.Adj := fun u v =>
  inferInstanceAs (Decidable (witnessAdj u v))

private def parent (v : Vertex) : Vertex :=
  ![0,0,1,2,0,3,0,6,7,8,6,9,0,12,13,14,12,15,0,18,19,20,18,21] v

private theorem parent_adj : ∀ v : Vertex, v ≠ 0 → witness.Adj v (parent v) := by decide
private theorem parent_lt : ∀ v : Vertex, v ≠ 0 → (parent v).val < v.val := by decide
private theorem parent_nonleaf : ∀ v : Vertex, role (parent v) < 4 := by decide

private theorem connected_of_parent {W : Type*} (G : SimpleGraph W) (r : W) (p : W → W)
    (f : W → ℕ) (ha : ∀ v, v ≠ r → G.Adj v (p v))
    (hlt : ∀ v, v ≠ r → f (p v) < f v) : G.Connected := by
  have reach : ∀ n : ℕ, ∀ v : W, f v = n → G.Reachable r v := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro v hv
      by_cases hr : v = r
      · subst v
        exact Reachable.refl _
      · exact (ih (f (p v)) (hv ▸ hlt v hr) (p v) rfl).trans (ha v hr).symm.reachable
  exact (connected_iff_exists_forall_reachable G).mpr ⟨r,fun v => reach _ v rfl⟩

theorem witness_connected : witness.Connected :=
  connected_of_parent witness 0 parent Fin.val parent_adj parent_lt

private theorem leaf_deletion_connected (z : Vertex) (hz : ¬ role z < 4) :
    (deleteVertex witness z).Connected := by
  have hroot : (0 : Vertex) ≠ z := fun h => hz (h ▸ (by decide : role 0 < 4))
  let root : {w : Vertex // w ≠ z} := ⟨0,hroot⟩
  let next (v : {w : Vertex // w ≠ z}) : {w : Vertex // w ≠ z} :=
    ⟨parent v,fun h => hz (h ▸ parent_nonleaf v)⟩
  apply connected_of_parent (deleteVertex witness z) root next (fun v => v.val.val)
  · intro v hv
    exact parent_adj v (fun h => hv (Subtype.ext h))
  · intro v hv
    exact parent_lt v (fun h => hv (Subtype.ext h))

/-- For each deleted nonleaf, this marks one branch piece separated by the deletion. -/
private def side (z v : Vertex) : Bool :=
  decide (group z = group v ∧
    ((role z = 0 ∧ role v = 4) ∨
     (role z = 1 ∧ (role v = 2 ∨ role v = 3 ∨ role v = 5)) ∨
     (role z = 2 ∧ (role v = 3 ∨ role v = 5)) ∨
     (role z = 3 ∧ role v = 5)))

set_option maxHeartbeats 9000000 in
private theorem side_edge :
    ∀ z u v : Vertex, role z < 4 → u ≠ z → v ≠ z → witness.Adj u v →
      side z u = side z v := by decide

private theorem side_walk {z : Vertex} (hz : role z < 4)
    {u v : {w : Vertex // w ≠ z}} (p : (deleteVertex witness z).Walk u v) :
    side z u = side z v := by
  induction p with
  | nil => rfl
  | @cons a b c hab p ih =>
    exact (side_edge z a b hz a.property b.property hab).trans ih

private theorem side_witnesses :
    ∀ z : Vertex, role z < 4 → ∃ u v : Vertex,
      u ≠ z ∧ v ≠ z ∧ side z u ≠ side z v := by decide

theorem isCutVertex_iff (z : Vertex) : IsCutVertex witness z ↔ role z < 4 := by
  rw [IsCutVertex, componentCount_eq_one witness_connected]
  constructor
  · intro h
    by_contra hz
    rw [componentCount_eq_one (leaf_deletion_connected z hz)] at h
    exact (Nat.lt_irrefl 1) h
  · intro hz
    obtain ⟨u,v,hu,hv,hside⟩ := side_witnesses z hz
    let H := deleteVertex witness z
    haveI : Finite H.ConnectedComponent := finiteComponents H
    have hcomp : H.connectedComponentMk ⟨u,hu⟩ ≠ H.connectedComponentMk ⟨v,hv⟩ := by
      intro h
      obtain ⟨p⟩ := ConnectedComponent.exact h
      exact hside (side_walk hz p)
    exact (Finite.one_lt_card_iff_nontrivial).mpr ⟨⟨_,_,hcomp⟩⟩

def knownCuts : Finset Vertex := univ.filter (fun v => role v < 4)

theorem cutVertices_eq : cutVertices witness = knownCuts := by
  ext v
  simp [knownCuts,mem_cutVertices,isCutVertex_iff]

theorem cutVertices_card : (cutVertices witness).card = 16 := by
  rw [cutVertices_eq]
  decide

def knownPendants : Finset Vertex := {4,5,10,11,16,17,22,23}

set_option maxHeartbeats 5000000 in
theorem pendants_eq : pendants witness = knownPendants := by decide

def knownSupports : Finset Vertex := {0,3,6,9,12,15,18,21}

theorem pendantNeighborhood_eq : openNeighborhood witness (pendants witness) = knownSupports := by
  rw [pendants_eq]
  decide

set_option maxHeartbeats 5000000 in
theorem cutEdges_card : (cutEdges witness (cutVertices witness)).card = 8 := by
  rw [cutVertices_eq]
  decide

set_option maxHeartbeats 5000000 in
theorem remainderEdges_eq : remainderEdges witness = 4 := by
  rw [remainderEdges,pendantNeighborhood_eq]
  decide

theorem floorTerm_eq : floorTerm witness = 2 := by
  rw [floorTerm,remainderEdges_eq]
  apply Int.floor_eq_iff.mpr
  constructor <;> norm_num

theorem rhs_eq : catalogueRhs witness = 10 := by
  rw [catalogueRhs,cutEdges_card,floorTerm_eq]
  decide

private def block (p : Part) : Finset Vertex :=
  if p.2 = 0 then {branchVertex p.1 0,branchVertex p.1 4}
  else if p.2 = 1 then {branchVertex p.1 1,branchVertex p.1 2}
  else {branchVertex p.1 3,branchVertex p.1 5}

private theorem block_disjoint : ∀ p q : Part, p ≠ q → Disjoint (block p) (block q) := by decide

private theorem clique_adj : ∀ i j : Branch, i ≠ j →
    witness.Adj (branchVertex i 0) (branchVertex j 0) := by decide

private theorem leafA_block : ∀ i : Branch, ∀ w : Vertex,
    (w = branchVertex i 4 ∨ witness.Adj (branchVertex i 4) w) → w ∈ block (i,0) := by decide

private theorem leafB_block : ∀ i : Branch, ∀ w : Vertex,
    (w = branchVertex i 5 ∨ witness.Adj (branchVertex i 5) w) → w ∈ block (i,2) := by decide

private theorem path_block : ∀ i : Branch, ∀ w : Vertex,
    (w = branchVertex i 1 ∨ witness.Adj (branchVertex i 1) w) →
      w = branchVertex i 0 ∨ w ∈ block (i,1) := by decide

private theorem card_le_of_blocks_hit (A : Finset Part) (D : Finset Vertex)
    (h : ∀ p ∈ A, ∃ w ∈ D, w ∈ block p) : A.card ≤ D.card := by
  have h' (p : A) : ∃ w : D, w.val ∈ block p.val := by
    obtain ⟨w,hw,hb⟩ := h p p.property
    exact ⟨⟨w,hw⟩,hb⟩
  choose f hf using h'
  have hinj : Function.Injective f := by
    intro p q he
    by_contra hn
    have hpq : p.val ≠ q.val := fun hval => hn (Subtype.ext hval)
    exact disjoint_left.mp (block_disjoint p q hpq) (hf p) (he ▸ hf q)
  simpa using Fintype.card_le_of_injective f hinj

private theorem lower_bound (D : Finset Vertex) (hD : IndependentDominates witness D) :
    11 ≤ D.card := by
  let use (p : Part) : Prop := p.2 ≠ 1 ∨ branchVertex p.1 0 ∉ D
  let A : Finset Part := univ.filter use
  let B : Finset Part := univ.filter (fun p => ¬use p)
  have he : A.card + B.card = 12 := by
    have h := filter_card_add_filter_neg_card_eq_card (s := (univ : Finset Part)) use
    change A.card + B.card = _ at h
    rw [card_univ] at h
    exact h.trans (by decide)
  have only_one : B.card ≤ 1 := by
    apply card_le_one.mpr
    intro p hp q hq
    have hp' : p.2 = 1 ∧ branchVertex p.1 0 ∈ D := by simpa [B,use] using hp
    have hq' : q.2 = 1 ∧ branchVertex q.1 0 ∈ D := by simpa [B,use] using hq
    apply Prod.ext _ (hp'.1.trans hq'.1.symm)
    by_contra hn
    have ha := clique_adj p.1 q.1 hn
    exact (hD.1 hp'.2 hq'.2 ha.ne) ha
  have hdom (v : Vertex) : ∃ w ∈ D, w = v ∨ witness.Adj v w := by
    obtain hv | ⟨w,hw,ha⟩ := hD.2 v
    · exact ⟨v,hv,Or.inl rfl⟩
    · exact ⟨w,hw,Or.inr ha⟩
  have hh : ∀ p ∈ A, ∃ w ∈ D, w ∈ block p := by
    rintro ⟨i,j⟩ hj
    have hroles : j = 0 ∨ j = 1 ∨ j = 2 := by
      have h := j.isLt
      omega
    obtain rfl | rfl | rfl := hroles
    · obtain ⟨w,hw,ha⟩ := hdom (branchVertex i 4)
      exact ⟨w,hw,leafA_block i w ha⟩
    · have hs : branchVertex i 0 ∉ D := by simpa [A,use] using hj
      obtain ⟨w,hw,ha⟩ := hdom (branchVertex i 1)
      exact ⟨w,hw,(path_block i w ha).resolve_left (fun h => hs (h ▸ hw))⟩
    · obtain ⟨w,hw,ha⟩ := hdom (branchVertex i 5)
      exact ⟨w,hw,leafB_block i w ha⟩
  have hc := card_le_of_blocks_hit A D hh
  omega

def selected : Finset Vertex := {0,3,7,9,10,13,15,16,19,21,22}

set_option maxHeartbeats 5000000 in
theorem selected_independentDominates : IndependentDominates witness selected := by
  unfold IndependentDominates
  decide

theorem independentDomination_eq : independentDominationNumber witness = 11 := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨selected,selected_independentDominates,by decide⟩
  · have hn : {k : ℕ | ∃ D, IndependentDominates witness D ∧ D.card = k}.Nonempty :=
      ⟨11,selected,selected_independentDominates,by decide⟩
    obtain ⟨D,hD,hcard⟩ := Nat.sInf_mem hn
    change 11 ≤ sInf _
    rw [← hcard]
    exact lower_bound D hD

theorem counterexample427 :
    witness.Connected ∧ 3 < Fintype.card Vertex ∧
      catalogueRhs witness < (independentDominationNumber witness : ℤ) := by
  refine ⟨witness_connected,by decide,?_⟩
  rw [rhs_eq,independentDomination_eq]
  decide

theorem conjecture427_false :
    ¬ ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      G.Connected → 3 < Fintype.card V →
        (independentDominationNumber G : ℤ) ≤ catalogueRhs G := by
  intro h
  exact (not_le_of_gt counterexample427.2.2) (h Vertex witness witness_connected (by decide))

#print axioms cutVertices_eq
#print axioms pendants_eq
#print axioms cutEdges_card
#print axioms remainderEdges_eq
#print axioms floorTerm_eq
#print axioms independentDomination_eq
#print axioms conjecture427_false

end Graffiti427
