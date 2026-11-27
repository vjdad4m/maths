import P5CliqueMultiPortBudget133
import P5CliqueMinimumPortExchange133

namespace Graffiti133P5CliqueArms
open SimpleGraph Finset Graffiti133Camby Graffiti133
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Two erasable singleton ports in a minimum core suppress full visibility
away from their own clients. The entire ambient mean bound needs no P9 premise. -/
theorem minimum_core_four_ports_two_singleton_ambient_mean_four
    (h4 : FourCycleFree G) (D E P : Finset V) (dm : MinimalSize G D)
    (sub : E⊆D) (ec : (G.induce (E : Set V)).Connected)
    (ed : ∀ x∈D,x∈E ∨ ∃ y∈E,G.Adj x y)
    (pc : P.card=4) (pd : P⊆D)
    (h7 : NoPath (G.induce (D : Set V)) 7)
    (tag : V→V) (route : ∀ q∉D,tag q∈P ∧ ∀ x∈D,(G.Adj q x↔x=tag q))
    (u v : V) (uo : u∉D) (vo : v∉D)
    (uE : tag u∉E) (vE : tag v∉E) (uv : tag u≠tag v)
    (uniqU : ∀ q∉D,tag q=tag u→q=u)
    (uniqV : ∀ q∉D,tag q=tag v→q=v) :
    (∑ x : V,localIndependence G x)≤4*Fintype.card V := by
  classical
  let Q := (Finset.univ : Finset V)\D
  let vis (q : V) := (insert q (Q.filter (G.Adj q))).image tag
  let H := Q.filter (fun q=>3<(vis q).card)
  have qo (q : V) (qm : q∈Q) : q∉D := (Finset.mem_sdiff.mp qm).2
  have pick (q : V) (qo : q∉D) : tag q∈D ∧ G.Adj q (tag q) := by
    have hp := pd (route q qo).1
    exact ⟨hp,((route q qo).2 _ hp).mpr rfl⟩
  have vsub (q : V) (qm : q∈Q) : vis q⊆P := by
    intro x xm
    obtain ⟨y,ym,rfl⟩ := Finset.mem_image.mp xm
    rcases Finset.mem_insert.mp ym with e|adj
    · exact (route y (e.symm ▸ qo q qm)).1
    · exact (route y (qo y (Finset.mem_filter.mp adj).1)).1
  have cont (q : V) (qc : q∈Q) (hi : 3<(vis q).card) : q∈({u,v}:Finset V) := by
    by_contra outside
    have qu : q≠u := fun e=>outside (Finset.mem_insert.mpr (Or.inl e))
    have qv : q≠v := fun e=>outside (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr e)))
    have all : vis q=P := Finset.eq_of_subset_of_card_le (vsub q qc) (by omega)
    have look (w : V) (wo : w∉D) (qw : q≠w)
        (uniq : ∀ x∉D,tag x=tag w→x=w) : G.Adj q w := by
      have tar : tag w∈vis q := all.symm ▸ (route w wo).1
      obtain ⟨x,xm,e⟩ := Finset.mem_image.mp tar
      rcases Finset.mem_insert.mp xm with xq|xQ
      · exact (qw (uniq q (qo q qc) (xq ▸ e))).elim
      · have eq := uniq x (qo x (Finset.mem_filter.mp xQ).1) e
        exact eq ▸ (Finset.mem_filter.mp xQ).2
    have zu := look u uo qu uniqU
    have zv := look v vo qv uniqV
    exact uv (minimum_core_at_most_one_visible_singleton_middle_port D E dm sub ec ed tag pick
      q u v (qo q qc) uo vo uE vE zu zv uniqU uniqV)
  have cap : H.card≤2 := by
    have hs : H⊆({u,v}:Finset V) := fun q qm=>cont q (Finset.mem_filter.mp qm).1 (Finset.mem_filter.mp qm).2
    have z := Finset.card_le_card hs
    have ne : u≠v := fun e=>uv (congrArg tag e)
    simpa [ne] using z
  have sum : (∑ q∈Q,(vis q).card)≤3*Q.card+2 := by
    have point (q : V) (qm : q∈Q) : (vis q).card≤3+(if q∈H then 1 else 0) := by
      by_cases hi : 3<(vis q).card
      · have m : q∈H := Finset.mem_filter.mpr ⟨qm,hi⟩
        rw [if_pos m]
        exact (Finset.card_le_card (vsub q qm)).trans (by omega)
      · have h : q∉H := fun e=>hi (Finset.mem_filter.mp e).2
        rw [if_neg h]
        omega
    have ss := Finset.sum_le_sum point
    rw [Finset.sum_add_distrib] at ss
    have hsum : (∑ q∈Q,(if q∈H then 1 else 0 : Nat))=H.card := by
      rw [←Finset.card_filter]
      congr 1
      ext q
      simp only [Finset.mem_filter,H]
      tauto
    have cs : (∑ _q∈Q,(3:Nat))=3*Q.card := by simp [Nat.mul_comm]
    rw [hsum,cs] at ss
    exact ss.trans (Nat.add_le_add_left cap _)
  have extra : (∑ q∈Q,((D.filter (G.Adj q)).card-1))=0 := by
    apply Finset.sum_eq_zero
    intro q qm
    have eq : D.filter (G.Adj q)={tag q} := by
      ext x
      constructor
      · intro m
        obtain ⟨xd,ad⟩ := Finset.mem_filter.mp m
        exact Finset.mem_singleton.mpr (((route q (qo q qm)).2 x xd).mp ad)
      · intro m
        obtain rfl := Finset.mem_singleton.mp m
        exact Finset.mem_filter.mpr (pick q (qo q qm))
    simp [eq]
  apply multi_attachment_weighted_slack_P7free_ambient_mean_four h4 D tag pick dm.1.1 h7
  change (∑ q∈Q,(vis q).card)+2*(∑ q∈Q,((D.filter (G.Adj q)).card-1))≤3*Q.card+D.card
  have pp := Finset.card_le_card pd
  omega

#print axioms minimum_core_four_ports_two_singleton_ambient_mean_four
end Graffiti133P5CliqueArms
