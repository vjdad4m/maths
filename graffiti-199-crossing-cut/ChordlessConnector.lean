import CutTorso
import Mathlib.Combinatorics.SimpleGraph.Metric

namespace Graffiti199Depleted.Catalogue

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

private theorem walk_take_length {a b : V} (p : G.Walk a b) (n : ℕ) :
    (p.take n).length ≤ n := by
  induction p generalizing n with
  | nil => simp [Walk.take]
  | cons h p ih =>
    cases n with
    | zero => simp [Walk.take]
    | succ n => exact Nat.succ_le_succ (ih n)

private theorem walk_drop_length {a b : V} (p : G.Walk a b) (n : ℕ) :
    (p.drop n).length ≤ p.length - n := by
  induction p generalizing n with
  | nil => simp [Walk.drop]
  | cons h p ih =>
    cases n with
    | zero => simp [Walk.drop]
    | succ n => simpa [Walk.drop, Walk.length_cons, Nat.succ_sub_succ_eq_sub] using ih n

private theorem geodesic_gap {a b : V} (p : G.Walk a b) (hp : p.length = G.dist a b)
    {i j : ℕ} (gap : i+1 < j) (hj : j ≤ p.length) :
    ¬ G.Adj (p.getVert i) (p.getVert j) := by
  intro e
  let q := (p.take i).append ((p.drop j).cons e)
  have len := G.dist_le q
  rw [← hp] at len
  change p.length ≤ ((p.take i).append ((p.drop j).cons e)).length at len
  rw [Walk.length_append,Walk.length_cons] at len
  have left := walk_take_length p i
  have right := walk_drop_length p j
  omega

theorem geodesic_adj_iff {a b : V} (p : G.Walk a b) (hp : p.length = G.dist a b)
    {i j : ℕ} (hi : i ≤ p.length) (hj : j ≤ p.length) :
    G.Adj (p.getVert i) (p.getVert j) ↔ i+1=j ∨ j+1=i := by
  constructor
  · intro adj
    rcases lt_trichotomy i j with lt|eq|lt
    · exact Or.inl (by by_contra h; exact geodesic_gap p hp (by omega) hj adj)
    · subst j
      exact (G.loopless _ adj).elim
    · exact Or.inr (by by_contra h; exact geodesic_gap p hp (by omega) hi adj.symm)
  · rintro (rfl|rfl)
    · exact p.adj_getVert_succ (by omega)
    · exact (p.adj_getVert_succ (by omega)).symm

structure ChordlessConnector (G : SimpleGraph V) (B : Set V) (u v : V) where
  last : ℕ
  inside : Fin (last+1) ↪ V
  kept : ∀ i, inside i ∈ B
  chain : ∀ i j, G.Adj (inside i) (inside j) ↔ i.val+1=j.val ∨ j.val+1=i.val
  from_u : ∀ i, G.Adj u (inside i) ↔ i.val=0
  from_v : ∀ i, G.Adj v (inside i) ↔ i.val=last

/-- The geodesic in the opposite shore together with the two specified
ports has new interior vertices and no chords. -/
theorem exists_chordless_connector {B : Set V} {u v : V}
    (hB : (G.induce B).Preconnected) (uv : u ≠ v)
    (nonedge : ¬ G.Adj u v) (hu : ∃ x ∈ B, G.Adj u x) (hv : ∃ y ∈ B, G.Adj v y) :
    Nonempty (ChordlessConnector G B u v) := by
  classical
  let S : Set V := B ∪ {u,v}
  let H := G.induce S
  let u' : S := ⟨u,Or.inr (by simp)⟩
  let v' : S := ⟨v,Or.inr (by simp)⟩
  obtain ⟨x,xB,ux⟩ := hu
  obtain ⟨y,yB,vy⟩ := hv
  let x' : S := ⟨x,Or.inl xB⟩
  let y' : S := ⟨y,Or.inl yB⟩
  have center : H.Reachable x' y' :=
    reachable_of_preconnected_induce (fun _ h => Or.inl h) hB xB yB
  have reach : H.Reachable u' v' :=
    (show H.Adj u' x' from ux).reachable.trans (center.trans (show H.Adj y' v' from vy.symm).reachable)
  obtain ⟨p,plen⟩ := reach.exists_walk_length_eq_dist
  have path := p.isPath_of_length_eq_dist plen
  have long : 1 < p.length := by
    rw [plen]
    exact reach.one_lt_dist_of_ne_of_not_adj (fun eq => uv (congrArg Subtype.val eq)) nonedge
  let m := p.length-2
  let c : Fin (m+1) → V := fun i => (p.getVert (i.val+1)).val
  have bound (i : Fin (m+1)) : i.val+1 < p.length := by
    have h := i.isLt
    dsimp [m] at h
    omega
  have comes (i : Fin (m+1)) : c i ∈ B := by
    rcases (p.getVert (i.val+1)).property with h|h
    · exact h
    · have e : c i = u ∨ c i = v := by simpa using h
      rcases e with e|e
      · have q := (path.getVert_eq_start_iff (bound i).le).mp (Subtype.ext e)
        omega
      · have q := (path.getVert_eq_end_iff (bound i).le).mp (Subtype.ext e)
        have lt := bound i
        omega
  have cInj : Function.Injective c := by
    intro i j e
    have s : p.getVert (i.val+1) = p.getVert (j.val+1) := Subtype.ext e
    have index := path.getVert_injOn (show i.val+1 ≤ p.length from (bound i).le)
      (show j.val+1 ≤ p.length from (bound j).le) s
    exact Fin.ext (by omega)
  refine ⟨⟨m,⟨c,cInj⟩,comes,?_,?_,?_⟩⟩
  · intro i j
    change H.Adj (p.getVert (i.val+1)) (p.getVert (j.val+1)) ↔ _
    rw [geodesic_adj_iff p plen (bound i).le (bound j).le]
    omega
  · intro i
    change H.Adj u' (p.getVert (i.val+1)) ↔ _
    have step := geodesic_adj_iff p plen (Nat.zero_le _) (bound i).le
    rw [p.getVert_zero] at step
    exact step.trans (by omega)
  · intro i
    change H.Adj v' (p.getVert (i.val+1)) ↔ _
    have step := geodesic_adj_iff p plen (le_refl p.length) (bound i).le
    rw [p.getVert_length] at step
    exact step.trans (by dsimp [m]; have h := bound i; omega)

#print axioms exists_chordless_connector

end Graffiti199Depleted.Catalogue
