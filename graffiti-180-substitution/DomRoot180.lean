import DominatingEdge180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The full rooted inequality holds in either parity at an endpoint
of a dominating edge. The order, independence number, and deficit are
otherwise unrestricted. -/
theorem dom_edge_rooted (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    {r y : V} (h : DomEdge G r y) (p : Bool) : localBound G r (parity G r p) := by
  classical
  cases p
  case true => exact dom_odd G gc hn h
  case false =>
    by_cases un : Universal G r
    · exact universal_root G gc hn r un false
    let P := parity G r false
    have rp : r∈P := by simp [P,dist_self]
    have yp : y∉P := by simp [P,dist_eq_one_iff_adj.mpr h.1.symm]
    have high : 3≤bipartiteNum G := by
      by_contra! low; exact un (rank_small_complete G gc hn low r)
    intro A ai
    let Z := A∩P
    have zi : Indep G Z := fun x hx y hy => ai x (mem_inter.mp hx).1 y (mem_inter.mp hy).1
    have only {x : V} (xp : x∈P) : ¬G.Adj x r := by
      intro xr
      simp [P,dist_eq_one_iff_adj.mpr xr] at xp
    by_cases ra : r∈A
    · have ya : y∉A := fun ya => ai _ ra _ ya h.1.ne h.1
      by_cases comp : ∀ u∉A,∀ v∉A,u≠v → G.Adj u v
      · have top : Universal G y := by
          intro v vy
          by_cases va : v∈A
          · by_cases eq : v=r
            · exact eq ▸ h.1
            · exact (h.2 v eq vy).resolve_left (ai v va r ra eq)
          · exact comp v va y ya vy
        apply universal_pay G top A P (Or.inr (Or.inl (mem_inter.mpr ⟨ra,rp⟩)))
        have b := one_credit G zi (u:=y) (by simp [Z,ya])
        simp [ya,yp]; change (A∩P).card+1≤_ at b; omega
      · push_neg at comp
        obtain ⟨u,ua,v,va,ne,non⟩ := comp
        have b := pair_credit G zi ne non (by simp [Z,ua]) (by simp [Z,va])
        apply pair_pay G h A P
        simp [ra,ya,yp]; change (A∩P).card+2≤_ at b; omega
    · by_cases ya : y∈A
      · have empty : A∩P=∅ := by
          apply eq_empty_iff_forall_not_mem.mpr
          intro x hx
          obtain ⟨xa,xp⟩ := mem_inter.mp hx
          have xr : x≠r := fun eq => ra (eq ▸ xa)
          have xy : x≠y := fun eq => yp (eq ▸ xp)
          exact (h.2 x xr xy).elim (only xp) (ai x xa y ya xy)
        apply pair_pay G h A P
        simp [empty,rp,ya]; omega
      · have rz : r∉Z := fun z => ra (mem_inter.mp z).1
        have ins : Indep G (insert r Z) := by
          intro a ha b hb ne edge
          rcases mem_insert.mp ha with ar|az <;> rcases mem_insert.mp hb with br|bz
          · exact ne (ar.trans br.symm)
          · exact only (mem_inter.mp bz).2 (ar ▸ edge.symm)
          · exact only (mem_inter.mp az).2 (br ▸ edge)
          · exact zi a az b bz ne edge
        have b := one_credit G ins (u:=y) (by simp [Z,ya,h.1.ne.symm])
        rw [card_insert_of_not_mem rz] at b
        apply pair_pay G h A P
        simp [rp,ya,yp]; change (A∩P).card+1+1≤_ at b; omega

#print axioms dom_edge_rooted
end Minimal180.Substitution
