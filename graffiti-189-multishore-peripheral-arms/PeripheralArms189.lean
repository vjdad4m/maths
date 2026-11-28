import MultiShoreCutBound189
open Finset SimpleGraph Graffiti189LongestPath
open private Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
set_option maxHeartbeats 10000000
namespace Graffiti189LongestPath.MultiShoreCutBound
variable {V α : Type*} [Fintype V] [DecidableEq V] [Fintype α]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Peripheral arms after deleting k−1 vertices satisfy the same shape bound
as minimum-cut shores, even when their articulation attachments differ and
an unrestricted central region remains. -/
theorem degree_le_of_peripheral_arms
    (hc : G.Connected) (k d : Nat) (hk : 3≤k)
    (conn : ∀ D : Finset V,D.card<k → (G.induce ((↑D:Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → d≤G.degree u ∨ d≤G.degree v)
    (cap : ∀ v,(DistanceTwo G v).card≤d) (T : Finset V) (M : α→Finset V) (p : α→V)
    (tc : T.card+1=k) (pair : Pairwise (fun i j => Disjoint (M i) (M j)))
    (mt : ∀ i,Disjoint (M i) T) (pOut : ∀ i j,p i∉M j)
    (each : ∀ i,∀ a∈M i,∀ b∉M i,G.Adj a b → b∈insert (p i) T)
    (sz : ∀ i,1<(M i).card) (q2 : 2≤Fintype.card α) :
    let q := (Fintype.card α:ℤ)
    ((q-1)^2-q)*(d:ℤ)+q*(q-1)≤q*(q-1)*(k:ℤ) := by
  classical
  have other (i : α) : ∃ j : α, i≠j := by
    by_contra! h
    have aux : (univ : Finset α) ⊆ {i} := fun j _ => mem_singleton.mpr (h j).symm
    have c := card_le_card aux
    simp at c
    omega
  have no (i j : α) (ij : i≠j) (u : V) (ui : u∈M i) (v : V) (vj : v∈M j) :
      ¬G.Adj u v := by
    intro uv
    have m := each i u ui v (fun vi => disjoint_left.mp (pair ij) vi vj) uv
    rcases mem_insert.mp m with e|e
    · exact pOut i j (e ▸ vj)
    · exact disjoint_left.mp (mt j) vj e
  have neM (i : α) : (M i).Nonempty := card_pos.mp (by have := sz i; omega)
  have reach (i : α) (s : V) (ss : s∈T) : ∃ u∈M i,G.Adj s u := by
    by_contra bad
    obtain ⟨x,xi⟩ := neM i
    obtain ⟨j,ij⟩ := other i
    obtain ⟨y,yj⟩ := neM j
    let B := (insert (p i) T).erase s
    have cl (u : V) (ui : u∈M i) (v : V) (vi : v∉M i) (uv : G.Adj u v) :
        v∈B := mem_erase.mpr ⟨fun e => bad ⟨u,ui,e ▸ uv.symm⟩,each i u ui v vi uv⟩
    have out (j : α) (v : V) (vj : v∈M j) : v∉B := by
      intro h
      exact (mem_insert.mp (mem_erase.mp h).2).elim
        (fun e => pOut i j (e ▸ vj)) (disjoint_left.mp (mt j) vj)
    have ksmall := Graffiti189LongestPath.boundary_card_of_connectivity k conn xi
      (fun h => disjoint_left.mp (pair ij) h yj) (out j y yj)
      (disjoint_left.mpr (fun v vi => out i v vi)) cl
    have h := card_erase_add_one (mem_insert_of_mem ss : s∈insert (p i) T)
    have t := card_insert_le (p i) T
    change k≤((insert (p i) T).erase s).card at ksmall
    omega
  have result : ∃ s∈T,∀ i,∃ u∈M i,G.Adj s u ∧ d≤G.degree u := by
    by_cases someLow : ∃ i,∃ x∈M i,G.degree x<d
    · obtain ⟨i,x,xi,xl⟩ := someLow
      have high (u : V) (ux : u≠x) := (deg u x ux).resolve_right (Nat.not_le_of_lt xl)
      have reachHigh : ∃ s∈T,∃ u∈M i,G.Adj s u ∧ d≤G.degree u := by
        apply Classical.byContradiction
        intro none
        have er := card_erase_add_one xi
        obtain ⟨u,ui⟩ := card_pos.mp (show 0<((M i).erase x).card from by have := sz i; omega)
        obtain ⟨j,ij⟩ := other i
        obtain ⟨v,vj⟩ := neM j
        have vr : v∉M i := fun h => disjoint_left.mp (pair ij) h vj
        let B : Finset V := {x,p i}
        have cl (a : V) (ar : a∈(M i).erase x) (b : V) (br : b∉(M i).erase x) (ab : G.Adj a b) :
            b∈B := by
          obtain ⟨ax,ai⟩ := mem_erase.mp ar
          by_cases bi : b∈M i
          · have bx : b=x := Classical.byContradiction (fun h => br (mem_erase.mpr ⟨h,bi⟩))
            exact mem_insert.mpr (Or.inl bx)
          · rcases mem_insert.mp (each i a ai b bi ab) with h|bt
            · exact mem_insert.mpr (Or.inr (mem_singleton.mpr h))
            · exact (none ⟨b,bt,a,ai,ab.symm,high a ax⟩).elim
        have out : v∉B := fun h => (mem_insert.mp h).elim
          (fun vx => vr (vx.symm ▸ xi)) (fun vp => pOut i j ((mem_singleton.mp vp) ▸ vj))
        have dis : Disjoint ((M i).erase x) B := disjoint_left.mpr (fun z zr zb =>
          (mem_insert.mp zb).elim (mem_erase.mp zr).1 (fun h => pOut i i ((mem_singleton.mp h) ▸ (mem_erase.mp zr).2)))
        have small := Graffiti189LongestPath.boundary_card_of_connectivity k conn ui
          (fun h => vr (mem_erase.mp h).2) out dis cl
        have le : B.card≤2 := (card_insert_le x {p i}).trans (by simp)
        omega
      obtain ⟨s,ss,hs⟩ := reachHigh
      refine ⟨s,ss,?_⟩
      intro j
      by_cases h : i=j
      · exact h ▸ hs
      · obtain ⟨u,uj,su⟩ := reach j s ss
        exact ⟨u,uj,su,high u (fun e => disjoint_left.mp (pair h) xi (e ▸ uj))⟩
    · obtain ⟨s,ss⟩ := card_pos.mp (show 0<T.card from by omega)
      refine ⟨s,ss,?_⟩
      intro i
      obtain ⟨u,ui,su⟩ := reach i s ss
      exact ⟨u,ui,su,Nat.le_of_not_gt (fun hl => someLow ⟨i,u,ui,hl⟩)⟩
  obtain ⟨s,ss,rs⟩ := result
  apply multishore_budget hc d cap k M pair no s
    (fun i si => disjoint_left.mp (mt i) si ss) _ q2
  intro i
  obtain ⟨u,ui,su,ud⟩ := rs i
  refine ⟨u,ui,su,ud,?_⟩
  have sub : G.neighborFinset u\M i ⊆ insert (p i) T := fun v hv => by
    obtain ⟨uv,vo⟩ := mem_sdiff.mp hv
    exact each i u ui v vo ((G.mem_neighborFinset _ _).mp uv)
  exact (card_le_card sub).trans ((card_insert_le _ _).trans_eq tc)

#print axioms degree_le_of_peripheral_arms
end Graffiti189LongestPath.MultiShoreCutBound
