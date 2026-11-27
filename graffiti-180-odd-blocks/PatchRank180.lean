import CyclicRank180

set_option warningAsError true
namespace Minimal180.OddBlock
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Only the two listed vertices may contact the exterior of the patch. -/
def Ports (G : SimpleGraph V) (S : Finset V) (x w : V) : Prop :=
  ∀ i∈S, ∀ j∉S, G.Adj i j → i=x ∨ i=w

omit [Fintype V] in
private theorem glue {G : SimpleGraph V} {S B : Finset V} {x w : V}
    (ports : Ports G S x w) (xs : x∈S) (ws : w∈S) (xw : G.Adj x w)
    {c f : V→Bool} (pc : ProperOn G S c)
    (outer : ∀ i∈B, ∀ j∈B, ¬(i∈S ∧ j∈S) → G.Adj i j → f i≠f j)
    (agree : x∈B → w∈B → f x≠f w) : TwoColor G B := by
  classical
  let t := if x∈B then x else w
  let d (v : V) := if c t=f t then c v else !(c v)
  have pd : ProperOn G S d := by
    intro i hi j hj e
    by_cases eq : c t=f t <;> simp [d,eq,pc i hi j hj e]
  have dt : d t=f t := by dsimp [d]; cases c t <;> cases f t <;> decide
  have locks (v : V) (hv : v∈B) (hv' : v=x ∨ v=w) : d v=f v := by
    rcases hv' with rfl|rfl
    · simpa [t,hv] using dt
    · by_cases xb : x∈B
      · have equ : d x=f x := by simpa [t,xb] using dt
        have ne := pd x xs v ws xw
        have ne' := agree xb hv
        rw [equ] at ne
        revert ne ne'
        cases f x <;> cases d v <;> cases f v <;> decide
      · simpa [t,xb] using dt
  apply (color_function G B).mpr
  refine ⟨fun v => if v∈S then d v else f v,?_⟩
  intro i ib j jb e
  by_cases is : i∈S <;> by_cases js : j∈S
  · simpa only [if_pos is,if_pos js] using pd i is j js e
  · simp only [if_pos is,if_neg js,locks i ib (ports i is j js e)]
    exact outer i ib j jb (fun h => js h.2) e
  · simp only [if_neg is,if_pos js,locks j jb (ports j js i is e.symm)]
    exact outer i ib j jb (fun h => is h.1) e
  · simpa only [if_neg is,if_neg js] using outer i ib j jb (fun h => is h.1) e

/-- In a bipartite patch with two adjacent ports, deleting internal edges
preserves bipartite order whenever the two ports still have an internal path. -/
theorem patch_rank (G H : SimpleGraph V) (S : Finset V) (x w : V)
    (xs : x∈S) (ws : w∈S) (xw : G.Adj x w) (ports : Ports G S x w)
    (bip : TwoColor G S) (sub : H≤G)
    (outer : ∀ i j, G.Adj i j → ¬(i∈S ∧ j∈S) → H.Adj i j)
    (route : (side H S).Reachable ⟨x,xs⟩ ⟨w,ws⟩) : bipartiteNum H=bipartiteNum G := by
  classical
  obtain ⟨c,pc⟩ := (color_function G S).mp bip
  obtain ⟨B,col,top⟩ := optB H
  obtain ⟨f,pf⟩ := (color_function H B).mp col
  apply le_antisymm _ (rank_antitone G sub)
  rw [←top]
  have out (i : V) (ib : i∈B) (j : V) (jb : j∈B) (off : ¬(i∈S ∧ j∈S)) (e : G.Adj i j) :
      f i≠f j := pf i ib j jb (outer i j e off)
  by_cases ok : x∈B → w∈B → f x≠f w
  · exact size_bip G (glue ports xs ws xw pc out ok)
  push_neg at ok
  obtain ⟨xb,wb,same⟩ := ok
  have missing : ¬S⊆B := by
    intro allS
    have propagate {i j : ↥S} (p : (side H S).Walk i j) :
        (c i=f i ↔ c j=f j) := by
      induction p with
      | nil => rfl
      | @cons a b d e _ ih =>
        have k := pc a a.property b b.property (sub (show H.Adj a b from e))
        have k' := pf a (allS a.property) b (allS b.property) e
        apply Iff.trans _ ih
        revert k k'
        cases c a <;> cases f a <;> cases c b <;> cases f b <;> decide
    have eq : c x=f x ↔ c w=f w := propagate route.some
    have ne := pc x xs w ws xw
    rw [same] at eq
    revert eq ne
    cases c x <;> cases c w <;> cases f w <;> decide
  obtain ⟨z,zs,zb⟩ := Finset.not_subset.mp missing
  let B' := insert z (B.erase x)
  have zx : z≠x := fun e => zb (e ▸ xb)
  have zw : z≠w := fun e => zb (e ▸ wb)
  have nx : x∉B' := by simp [B',zx.symm]
  have old {a : V} (aB : a∈B') (az : a≠z) : a∈B :=
    mem_of_mem_erase ((mem_insert.mp aB).resolve_left az)
  have exterior (i : V) (ib : i∈B') (j : V) (jb : j∈B') (off : ¬(i∈S ∧ j∈S)) (e : G.Adj i j) :
      f i≠f j := by
    have nz {a b : V} (edge : G.Adj a b) (apart : ¬(a∈S ∧ b∈S)) : a≠z := by
      rintro rfl
      exact (ports a zs b (fun h => apart ⟨zs,h⟩) edge).elim zx zw
    exact out i (old ib (nz e off)) j (old jb (nz e.symm (fun h => off h.symm))) off e
  have bound := size_bip G (glue ports xs ws xw pc exterior (fun h => (nx h).elim))
  have ze : z∉B.erase x := fun h => zb (mem_of_mem_erase h)
  change (insert z (B.erase x)).card≤_ at bound
  rw [card_insert_of_not_mem ze,card_erase_add_one xb] at bound
  exact bound

#print axioms patch_rank
end Minimal180.OddBlock
