import PortColor180

set_option warningAsError true
namespace Minimal180.RootEar
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 OddBlock CutGain DescentOne
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {r : V} {odd : Bool} {A : Finset V} (h : FailedTwo G r odd A)
include h

/-- Every shortest-path predecessor of a singly marked vertex is singly
marked, all the way back to the root. -/
theorem predecessor_closed {i q : V} :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    i∈D → G.Adj i q → G.dist i r=G.dist q r+1 → q∈D := by
  classical
  intro P D id iq step
  let d (v : V) := G.dist v r
  have nz : i≠r := by intro eq; rw [eq,dist_self] at step; omega
  let p (v : V) := if v=i then q else if vr : v=r then r else
    (Graffiti169.exists_predecessor G h.connected r v vr).choose
  have down (v : V) (vr : v≠r) : G.Adj v (p v) ∧ d v=d (p v)+1 := by
    by_cases vi : v=i
    · subst v; simpa [p,d] using And.intro iq step
    · simpa [p,d,vi,vr] using (Graffiti169.exists_predecessor G h.connected r v vr).choose_spec
  obtain ⟨M,mg,tree,cross,take,star⟩ := predecessor_tree G h.connected r odd p down
  obtain ⟨s,t,rs,rt,st⟩ := block_neighbors G h.connected h.order h.block r
  have internal : r∉leaves M := fun z => st (leaf_unique M z (star _ rs) (star _ rt))
  have count := (h.rigid M tree mg internal cross).2
  change (M.edgeFinset∩D.sym2).card+1=D.card at count
  rw [chosen_parent_count M tree r D p d (fun v vr => (down v vr).2) take] at count
  have rd : r∈D := h.root_disagreement
  have erase := card_erase_add_one rd
  have eq := eq_of_subset_of_card_le (filter_subset (fun v => p v∈D) (D.erase r)) (by omega)
  have kept : i∈(D.erase r).filter (fun v => p v∈D) := by rw [eq]; exact mem_erase.mpr ⟨nz,id⟩
  have inside := mem_filter.mp kept
  simpa [p] using inside.2

/-- At every positive distance the disagreement width is nonincreasing;
in particular it is bounded by the number of marked-disagreement neighbors
of the root, which is at most two. -/
theorem width :
    let P := parity G r odd
    let D := (A∪P)\(A∩P)
    let layer (k : ℕ) := D.filter (fun v => G.dist v r=k)
    (∀ k, (layer (k+2)).card≤(layer (k+1)).card) ∧
      (∀ k, (layer (k+1)).card≤(layer 1).card) ∧ (layer 1).card≤2 := by
  classical
  intro P D layer
  let p (v : V) := if vr : v=r then r else (Graffiti169.exists_predecessor G h.connected r v vr).choose
  have down (v : V) (vr : v≠r) : G.Adj v (p v) ∧ G.dist v r=G.dist (p v) r+1 := by
    simpa [p,vr] using (Graffiti169.exists_predecessor G h.connected r v vr).choose_spec
  have desc (k : ℕ) : (layer (k+2)).card≤(layer (k+1)).card := by
    have nz {v : V} (m : v∈layer (k+2)) : v≠r := by
      intro eq; have d := (mem_filter.mp m).2; rw [eq,dist_self] at d; omega
    have maps {v : V} (m : v∈layer (k+2)) : p v∈layer (k+1) := by
      obtain ⟨vd,degree⟩ := mem_filter.mp m
      have ⟨edge,step⟩ := down v (nz m)
      exact mem_filter.mpr ⟨predecessor_closed h vd edge step,by omega⟩
    have inj : Set.InjOn p (↑(layer (k+2)) : Set V) := by
      intro i im j jm eq
      obtain ⟨a,di⟩ := down i (nz im)
      obtain ⟨b,dj⟩ := down j (nz jm)
      have ⟨pd,dp⟩ := mem_filter.mp (maps im)
      have pr : p i≠r := by intro re; rw [re,dist_self] at dp; omega
      exact h.outward (mem_sdiff.mp pd).1 pr a.symm (eq ▸ b.symm) di (by simpa only [eq] using dj)
    exact (card_image_of_injOn inj) ▸ (card_le_card (show (layer (k+2)).image p⊆layer (k+1) from
      by intro z m; obtain ⟨v,vm,rfl⟩ := mem_image.mp m; exact maps vm))
  refine ⟨desc,?_,?_⟩
  · intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih => exact (desc k).trans ih
  · have inc : layer 1⊆G.neighborFinset r := by
      intro v m
      exact (G.mem_neighborFinset ..).mpr (dist_eq_one_iff_adj.mp (mem_filter.mp m).2).symm
    simpa only [card_neighborFinset_eq_degree,h.root_degree] using card_le_card inc

#print axioms predecessor_closed
#print axioms width
end Minimal180.RootEar
