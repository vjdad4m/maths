import Restrained

namespace Restrained534
open SimpleGraph Finset CographRadius
variable {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem degree_two {v a b : V} (va : G.Adj v a) (vb : G.Adj v b) (ne : a ≠ b) :
    2 ≤ G.degree v :=
  one_lt_card_iff.mpr ⟨a,b,(G.mem_neighborFinset _ _).mpr va,(G.mem_neighborFinset _ _).mpr vb,ne⟩

theorem cone_leafless [Nontrivial V] {u : V} (hu : Universal G u) :
    leavesAt G u = ∅ ↔ ∀ v, 2 ≤ G.degree v := by
  classical
  constructor
  · intro empty
    have second (v : V) (ne : v ≠ u) : ∃ w, G.Adj v w ∧ w ≠ u := by
      by_contra! only
      have h := (mem_leaves G).mpr ⟨ne,only⟩
      simp [empty] at h
    intro v
    by_cases h : v = u
    · subst v
      obtain ⟨a,au⟩ := exists_ne u
      obtain ⟨b,ab,bu⟩ := second a au
      exact degree_two G (hu a au.symm) (hu b bu.symm) ab.ne
    · obtain ⟨b,vb,bu⟩ := second v h
      exact degree_two G (hu v (Ne.symm h)).symm vb bu.symm
  · intro deg
    apply eq_empty_of_forall_not_mem
    intro v hv
    obtain ⟨w,hw,ne⟩ := exists_mem_ne (s := G.neighborFinset v)
      (show 1 < (G.neighborFinset v).card from deg v) u
    exact ne (((mem_leaves G).mp hv).2 w ((G.mem_neighborFinset _ _).mp hw))

private theorem nonuniversal_degree (join : ProperJoin G)
    (no : ¬ ∃ u, Universal G u) (v : V) : 2 ≤ G.degree v := by
  classical
  have orient : ∃ (A : V → Prop) (b : V), A v ∧ ¬ A b ∧
      ∀ x y, A x → ¬ A y → G.Adj x y := by
    obtain ⟨A,a,b,ha,hb,cross⟩ := join
    by_cases av : A v
    · exact ⟨A,b,av,hb,cross⟩
    · exact ⟨fun x => ¬ A x,a,av,not_not.mpr ha,
        fun x y hx hy => (cross y x (not_not.mp hy) hx).symm⟩
  obtain ⟨A,b,av,nb,cross⟩ := orient
  have missing : ∃ w, b ≠ w ∧ ¬ G.Adj b w := by
    by_contra! all
    exact no ⟨b,all⟩
  obtain ⟨w,bw,miss⟩ := missing
  have nw : ¬ A w := fun aw => miss (cross w b aw nb).symm
  exact degree_two G (cross v b av nb) (cross v w av nw) bw

/-- Exact criterion on any join of two nonempty finite graphs. -/
theorem join_criterion [Nontrivial V] (join : ProperJoin G) :
    restrainedNumber G ≤ independentDomination G ↔ ∀ v, 2 ≤ G.degree v := by
  classical
  by_cases univVertex : ∃ u, Universal G u
  · obtain ⟨u,hu⟩ := univVertex
    rw [cone_formula G hu,independent_universal G hu,← cone_leafless G hu,← card_eq_zero]
    omega
  · rw [nonuniversal_join G join univVertex]
    obtain ⟨D,sz,_,dom⟩ := attained G
    have lo := two_le_of_no_universal G univVertex dom
    exact ⟨fun _ => nonuniversal_degree G join univVertex,fun _ => sz ▸ lo⟩

/-- Exact extension of the proposed inequality to all connected nontrivial cographs. -/
theorem criterion [Nontrivial V] (conn : G.Connected) (cog : Cograph G) :
    restrainedNumber G ≤ independentDomination G ↔ ∀ v, 2 ≤ G.degree v :=
  join_criterion G (cograph_join G conn cog)

/-- AutoGraphForge normalized physical row 534, record 38975fcb. -/
theorem row534 (order : 2 ≤ Fintype.card V) (cog : Cograph G) (conn : G.Connected)
    (even : ∀ v, Even (G.degree v)) : restrainedNumber G ≤ independentDomination G := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp order
  apply (criterion G conn cog).mpr
  intro v
  have pos : 0 < G.degree v := by
    apply (G.degree_pos_iff_exists_adj v).mpr
    obtain ⟨w,diff⟩ := exists_ne v
    obtain ⟨walk⟩ := conn.preconnected v w
    cases walk with
    | nil => exact (diff rfl).elim
    | cons edge _ => exact ⟨_,edge⟩
  obtain ⟨k,hk⟩ := even v
  omega

#print axioms cone_formula
#print axioms independent_universal
#print axioms nonuniversal_cograph
#print axioms join_criterion
#print axioms criterion
#print axioms row534
end Restrained534
