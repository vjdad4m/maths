import RootReserve180
import ParentFiber180

set_option warningAsError true
namespace Minimal180.Transversals
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Direct the full alternating star at t toward one chosen predecessor.
On the symmetric difference, the parent is still a shortest-path predecessor.
When the root is singly marked, a child outside that difference exits
its part strictly below t. -/
theorem apex_star (G : SimpleGraph V) (gc : G.Connected) (r t : V) (p : Bool) (A : Finset V)
    (ai : Indep G A) (tr : t≠r) (at' : t∈A) (pt : t∈parity G r p) :
    let P := parity G r p
    let X := A∪P
    let D := X\(A∩P)
    let H := alternating G P
    let d := fun x => G.dist x r
    let C := D.filter (fun x => d x<d t)
    ∃ (T : SimpleGraph V) (q : V→V) (rank : V→ℕ),T≤H ∧ T.IsTree ∧
      (∀ x≠r,rank (q x)<rank x) ∧ (∀ x≠r,T.Adj x (q x)) ∧
      T.degree t=H.degree t ∧ (∀ x∈D,x≠r → d x=d (q x)+1) ∧
      (r∈C → ∃ x,x≠r ∧ x∉D ∧ q x∈C) := by
  classical
  intro P X D H d C
  let par x := if h : x=r then r else (Graffiti169.exists_predecessor G gc r x h).choose
  have spec (x : V) (xr : x≠r) : G.Adj x (par x) ∧ d x=d (par x)+1 := by
    simpa [par,xr,d] using (Graffiti169.exists_predecessor G gc r x xr).choose_spec
  let b := par t
  have tb := spec t tr
  change G.Adj t b ∧ d t=d b+1 at tb
  have vert (x : V) (xr : x≠r) : H.Adj x (par x) := by
    obtain ⟨edge,dist⟩ := spec x xr
    refine ⟨edge,?_⟩
    simp only [P,mem_parity];change (d x%2=p.toNat ↔ ¬d (par x)%2=p.toNat)
    cases p <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega
  have non (v : V) (tv : H.Adj t v) : v∉X := by
    intro m
    rcases mem_union.mp m with av|pv
    · exact ai t at' v av tv.1.ne tv.1
    · exact tv.2.mp pt pv
  have low (x : V) (tx : H.Adj t x) : d t≤d x+1 := by
    have h := gc.dist_triangle (u:=t) (v:=x) (w:=r)
    rw [dist_eq_one_iff_adj.mpr tx.1] at h
    change G.dist t r≤G.dist x r+1;omega
  let q x := if H.Adj t x ∧ x≠b then t else par x
  let rank x := 4*d x+(if x=t then 0 else if x=b then 2 else 5)
  have step (x : V) (xr : x≠r) : H.Adj x (q x) ∧ rank (q x)<rank x := by
    by_cases repl : H.Adj t x ∧ x≠b
    · have xt := repl.1.ne.symm
      have l := low x repl.1
      simp only [q,if_pos repl,rank,xt,repl.2,if_false,if_true]
      exact ⟨repl.1.symm,by omega⟩
    · rw [show q x=par x from if_neg repl]
      refine ⟨vert x xr,?_⟩
      by_cases xt : x=t
      · subst x; change rank b<rank t
        simp [rank,tb.1.ne.symm];omega
      · have ds := (spec x xr).2
        simp only [rank];split_ifs <;> omega
  obtain ⟨T,tree,edges⟩ := virtual_tree r q rank (fun x xr => (step x xr).2)
  obtain ⟨K,sub,kt,keep⟩ := keep_target H T (alternating_parity G gc r p).1 tree
  have take (x : V) (xr : x≠r) : K.Adj x (q x) := keep ⟨(step x xr).1,edges x xr⟩
  have qt : q t=b := by simp [q,b]
  have full (x : V) (tx : H.Adj t x) : K.Adj t x := by
    by_cases xb : x=b
    · rw [xb,←qt];exact take t tr
    · have xr : x≠r := by
        intro eq
        have one : d t=1 := dist_eq_one_iff_adj.mpr (show G.Adj t r from eq ▸ tx.1)
        have br : b=r := gc.dist_eq_zero_iff.mp (show d b=0 by omega)
        exact xb (eq.trans br.symm)
      exact (show K.Adj x t by simpa [q,tx,xb] using take x xr).symm
  have deg : K.degree t=H.degree t := by
    have eq : K.neighborFinset t=H.neighborFinset t := by
      ext x;simp only [mem_neighborFinset];exact ⟨fun e => sub e,full x⟩
    simpa only [card_neighborFinset_eq_degree] using congrArg card eq
  refine ⟨K,q,rank,sub,kt,fun x xr => (step x xr).2,take,deg,?_,?_⟩
  · intro x xd xr
    have nx : ¬H.Adj t x := fun h => non x h (mem_sdiff.mp xd).1
    simpa [q,nx] using (spec x xr).2
  · intro rc
    have rd := (mem_filter.mp rc).1
    have outside : b∉D := fun m => non b (vert t tr) (mem_sdiff.mp m).1
    have path (v : V) (vd : v∉D) (close : d v<d b ∨ v=b) :
        ∃ x,x≠r ∧ x∉D ∧ q x∈C := by
      induction k : d v using Nat.strong_induction_on generalizing v with
      | h k ih =>
        have vr : v≠r := fun eq => vd (eq ▸ rd)
        have lower := (spec v vr).2
        have within : d v≤d b := close.elim Nat.le_of_lt (fun eq => eq ▸ Nat.le_refl _)
        have move : q v=par v := by
          apply if_neg
          rintro ⟨edge,nb⟩
          have shorter := close.resolve_right nb
          have hi := low v edge;omega
        by_cases pd : par v∈D
        · exact ⟨v,vr,vd,mem_filter.mpr ⟨move ▸ pd,by rw [move];omega⟩⟩
        · exact ih (d (par v)) (by omega) (par v) pd (Or.inl (by omega)) rfl
    exact path b outside (Or.inr rfl)

#print axioms apex_star
end Minimal180.Transversals
