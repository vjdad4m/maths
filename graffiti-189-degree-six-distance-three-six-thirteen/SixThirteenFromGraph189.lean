import SixTwelveFromGraph189
import SixThirteenSat189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset ArticulationPair
open private Shore shore_disjoint shore_off shore_closed shore_connected from AdjacentCutFiveActual189
open private Cmp DeletionConnected from SixCutFar189
open private no_common_far shore_inside_five from SixDistanceThreeShort189
open private neighbor_subset_of_dark from SixTenRegular189
open private degree_two_from_one_deletion from AdjacentCutFiveTwinThreeGeom189
open private d2 from CrossSaturation189
open Graffiti189LongestPath.SixThirteenSat (Profile Model color seen external floor)
set_option linter.unusedSectionVars false
set_option maxHeartbeats 20000000
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {a b : V} {C D : Cmp G a b}

abbrev WingThirteenVertex := Fin 13

theorem hidden_block_has_shore_exit (D : Cmp G a b) (f : V→Fin 8)
    (h : ∃ u∈Shore D,f u=7) (h' : ∃ v∈Shore D,f v≠7) :
    ∃ u∈Shore D,∃ v∈Shore D,f u=7 ∧ f v≠7 ∧ G.Adj u v := by
  obtain ⟨x,xd,xh⟩ := h
  obtain ⟨y,yd,yh⟩ := h'
  let U : Set V := ↑(Shore D)
  obtain ⟨p⟩ := (shore_connected D).preconnected (⟨x,xd⟩ : U) (⟨y,yd⟩ : U)
  apply Classical.byContradiction
  intro no
  have run {z w : U} (q : (G.induce U).Walk z w) : f z.val=7 → f w.val=7 := by
    induction q with
    | nil => exact id
    | @cons t u w tu q ih =>
      intro ht
      apply ih
      apply Classical.byContradiction
      intro hu
      exact no ⟨t.val,t.property,u.val,u.property,ht,hu,tu⟩
  exact yh (run p xh)

noncomputable def wingThirteenGraph (G : SimpleGraph V) (S : Finset V) (lab : WingThirteenVertex ≃ (↑S : Set V)) :
    SimpleGraph WingThirteenVertex := G.comap (fun i=>(lab i).val)

instance (S : Finset V) (lab : WingThirteenVertex ≃ (↑S : Set V)) :
    DecidableRel (wingThirteenGraph G S lab).Adj :=
  fun i j=>inferInstanceAs (Decidable (G.Adj (lab i).val (lab j).val))

theorem wing_thirteen_degree_eq (lab : WingThirteenVertex ≃ (↑(Shore D) : Set V)) (i : WingThirteenVertex) :
    (wingThirteenGraph G (Shore D) lab).degree i=(inside G (Shore D) (lab i).val).card := by
  classical
  let H := wingThirteenGraph G (Shore D) lab
  let e : WingThirteenVertex ↪ V := lab.toEmbedding.trans ⟨Subtype.val,Subtype.val_injective⟩
  have k : (H.neighborFinset i).map e = inside G (Shore D) (lab i).val := by
    ext v
    constructor
    · intro mm
      obtain ⟨j,jm,eq⟩ := mem_map.mp mm
      change (lab j).val=v at eq
      subst v
      exact mem_filter.mpr ⟨(lab j).property,(H.mem_neighborFinset _ _).mp jm⟩
    · intro mm
      obtain ⟨vs,adj⟩ := mem_filter.mp mm
      let j := lab.symm ⟨v,vs⟩
      have je : lab j=(⟨v,vs⟩ : ↑(↑(Shore D):Set V)) := lab.apply_symm_apply _
      have aj : H.Adj i j := by change G.Adj (lab i).val (lab j).val; rwa [je]
      exact mem_map.mpr ⟨j,(H.mem_neighborFinset _ _).mpr aj,congrArg Subtype.val je⟩
  have h := congrArg Finset.card k
  rw [card_map,H.card_neighborFinset_eq_degree] at h
  exact h

theorem thirteen_model_of_label (hc : G.Connected) (far : 3≤G.dist a b) (ab : a≠b)
    (conn : DeletionConnected G) (even : ∀ x,(EvenFrom G x).card≤7)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v)
    (cd : C≠D) (six : (Shore C).card=6)
    (P : Profile) (lab : WingThirteenVertex ≃ (↑(Shore D) : Set V))
    (ha : P.p=(cutPorts G (Shore C) a).card) (hb : P.q=(cutPorts G (Shore C) b).card)
    (hr : ∀ i,sixClass G a b (lab i).val=P.role i)
    (hl : ∀ i,P.low≠some i → 6≤G.degree (lab i).val) :
    Model P (wingThirteenGraph G (Shore D) lab) (fun i j=>G.dist (lab i).val (lab j).val=2) := by
  classical
  let w (i : WingThirteenVertex) := (lab i).val
  have spec (i : WingThirteenVertex) : sixClassSpec G a b (w i) (P.role i) := by
    have no : ¬(G.Adj a (w i)∧G.Adj b (w i)) := no_common_far far
    exact (class_spec no _).mp (hr i)
  have sha (i : WingThirteenVertex) : w i∈Shore D := (lab i).property
  have na (i : WingThirteenVertex) : w i≠a := by
    intro e
    have s := sha i
    rw [e] at s
    exact (shore_off D).1 s
  have nb (i : WingThirteenVertex) : w i≠b := by
    intro e
    have s := sha i
    rw [e] at s
    exact (shore_off D).2 s
  have winj : Function.Injective w := fun _ _ e=>lab.injective (Subtype.ext e)
  have term (i : WingThirteenVertex) := role_terminal_spec far (spec i)
  constructor
  · intro i j h
    rwa [dist_comm]
  · intro i j ad
    exact six_role_of_edge hc far (na i) (nb i) (na j) (nb j) ad (spec i) (spec j)
  · intro i z vis
    have one : ∃ v∈Shore D,G.Adj (if z then b else a) v ∧ G.Adj (w i) v := by
      cases z
      · exact visible_has_local_mark hc far (sha i) (.inl rfl) ((term i).2.2.1.mp vis)
      · exact visible_has_local_mark hc far (sha i) (.inr rfl) ((term i).2.2.2.mp vis)
    obtain ⟨u,ud,ru,iu⟩ := one
    let j := lab.symm ⟨u,ud⟩
    have je : w j=u := congrArg Subtype.val (lab.apply_symm_apply ⟨u,ud⟩)
    refine ⟨j,?_,?_⟩
    · cases z
      · exact (term j).1.mpr (by rwa [je])
      · exact (term j).2.1.mpr (by rwa [je])
    · change G.Adj (w i) (w j)
      rwa [je]
  · intro i j k ne ik kj no
    exact (mem_filter.mp (d2 hc (fun eq=>ne (winj eq)) no ik kj)).2
  · intro i j z ne ic jc no
    cases z
    · exact (mem_filter.mp (d2 hc (fun eq=>ne (winj eq)) no ((term i).1.mp ic).symm ((term j).1.mp jc))).2
    · exact (mem_filter.mp (d2 hc (fun eq=>ne (winj eq)) no ((term i).2.1.mp ic).symm ((term j).2.1.mp jc))).2
  · intro i
    rw [wing_thirteen_degree_eq]
    change floor P i≤(inside G (Shore D) (w i)).card
    by_cases k : P.low=some i
    · by_cases ip : (P.role i).val<4
      · simpa [floor,k,ip] using shore_inside_one_of_two_connected far conn (sha i)
      · have mn := dark_role_not_adj_when_ge4 (Nat.le_of_not_gt ip) (spec i)
        have l := degree_two_from_one_deletion conn (na i) (fun h=>mn.1 h.symm)
        have sub := card_le_card (neighbor_subset_of_dark D (sha i) mn.1 mn.2)
        rw [G.card_neighborFinset_eq_degree] at sub
        simpa [floor,k,ip] using l.trans sub
    · by_cases ip : (P.role i).val<4
      · simpa [floor,k,ip] using shore_inside_five far D (sha i) (hl i k)
      · obtain ⟨na,nb⟩ := dark_role_not_adj_when_ge4 (Nat.le_of_not_gt ip) (spec i)
        simpa [floor,k,ip] using dark_inside_six (sha i) na nb (hl i k)
  · intro m n
    obtain ⟨i,hi⟩ := m
    obtain ⟨j,hj⟩ := n
    have ih : sixClass G a b (w i)=7 := (hr i).trans hi
    have jh : sixClass G a b (w j)≠7 := fun h=>hj ((hr j).symm.trans h)
    obtain ⟨x,xd,y,yd,xh,yh,xy⟩ := hidden_block_has_shore_exit D (sixClass G a b) ⟨w i,sha i,ih⟩ ⟨w j,sha j,jh⟩
    let k := lab.symm ⟨x,xd⟩
    let l := lab.symm ⟨y,yd⟩
    have ke : w k=x := congrArg Subtype.val (lab.apply_symm_apply ⟨x,xd⟩)
    have le : w l=y := congrArg Subtype.val (lab.apply_symm_apply ⟨y,yd⟩)
    have kr := hr k
    have lr := hr l
    change sixClass G a b (w k)=P.role k at kr
    change sixClass G a b (w l)=P.role l at lr
    rw [ke] at kr
    rw [le] at lr
    refine ⟨k,l,kr.symm.trans xh,fun e=>yh (lr.trans e),?_⟩
    change G.Adj (w k) (w l)
    rwa [ke,le]
  · intro i s caps
    let e : WingThirteenVertex ↪ V := ⟨w,winj⟩
    have loc : s.map e⊆Shore D := by
      intro x hx
      obtain ⟨j,js,eq⟩ := mem_map.mp hx
      exact eq ▸ sha j
    have tw : s.map e⊆DistanceTwo G (w i) := by
      intro x hx
      obtain ⟨j,js,eq⟩ := mem_map.mp hx
      exact mem_filter.mpr ⟨mem_univ _,eq ▸ caps j js⟩
    by_cases d : (P.role i).val<7
    · have l := k6_profile_budget hc far ab conn even degree cd six (sha i) d (spec i) _ loc tw
      rw [card_map] at l
      have ex : external P i = (match (P.role i).val with
        | 0=>(cutPorts G (Shore C) a).card
        | 1=>(cutPorts G (Shore C) a).card+1
        | 2=>(cutPorts G (Shore C) b).card
        | 3=>(cutPorts G (Shore C) b).card+1
        | 4=>(cutPorts G (Shore C) b).card+1+(6-((cutPorts G (Shore C) a).card+(cutPorts G (Shore C) b).card))
        | 5=>(cutPorts G (Shore C) a).card+1+(6-((cutPorts G (Shore C) a).card+(cutPorts G (Shore C) b).card))
        | _=>2+(6-((cutPorts G (Shore C) a).card+(cutPorts G (Shore C) b).card))) := by
        generalize hh : P.role i = r at d ⊢
        unfold external
        rw [hh]
        fin_cases r <;> first | exact ((by decide : ¬((7:Fin 8).val<7)) d).elim | simp [ha,hb]
      rwa [ex]
    · have v : (P.role i).val=7 := by have k := (P.role i).isLt; omega
      have cap := (card_le_card tw).trans (distanceTwo_le_of_even 6 (w i) (even (w i)))
      rw [card_map] at cap
      simpa [external,v] using cap

#print axioms thirteen_model_of_label
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
