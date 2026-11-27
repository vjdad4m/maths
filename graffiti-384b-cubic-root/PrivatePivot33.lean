import PrivateShores33

namespace Graffiti384b.RootCut
open Finset SimpleGraph HighEar OneEar EarAnchor CliquePivot33
open private Repair.isolate from Repair384b
open private EarAnchor.mask from AnchorCut33
open private TrianglePrune.reach_closed from TrianglePrune384b
open private EarAnchor.sees_in_clique from CubicAnchor33
open private CliquePivot33.isolated_degree from CliquePivot33
open private HighEar.nonEar from HighEarBypass33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

def Safe (R : Finset V) (x : V) := ∀ u,H.degree u=3 → u∉R → ¬H.Adj u x

private theorem regular {R : Finset V} {e x : V} (de : H.degree e=2)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H)) (safe : Safe H R x)
    {v : V} (ve : v≠e) (vx : v≠x) :
    3≤(Repair.isolate H x).degree v+2*(if v∈R then 1 else 0) := by
  have deg := HighEar.nonEar H de ve pos inj
  rw [CliquePivot33.isolated_degree H vx]
  by_cases edge : H.Adj v x
  · rw [card_erase_of_mem ((H.mem_neighborFinset _ _).mpr edge),card_neighborFinset_eq_degree]
    by_cases vr : v∈R
    · simp [vr]; omega
    · have ne : H.degree v≠3 := fun d => safe v d vr edge
      simp [vr]; omega
  · rw [erase_eq_of_not_mem (fun m => edge ((H.mem_neighborFinset _ _).mp m)),card_neighborFinset_eq_degree]; omega

/-- Put the two private regions and the retained four-clique into a partial
cut. No edge used by an interior vertex of either region is lost. -/
theorem region_cut {e a c x : V} (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (safe : Safe H R x) (cl : H.IsNClique 5 C) (xc : x∈C)
    (apart : ¬(a∈C ∧ c∈C)) {S T : Finset V} (dis : Disjoint S T) (as' : a∈S) (ct : c∈T)
    (en : e∉S∪T) (xn : x∉S∪T) (sa : ∃ y∈S,H.Adj a y) (tc : ∃ y∈T,H.Adj c y)
    (ls : ∀ y∈S,y≠a → ∀ z,H.Adj y z → z≠x → z∈S)
    (lt : ∀ y∈T,y≠c → ∀ z,H.Adj y z → z≠x → z∈T) : ¬Tight H R := by
  classical
  let K := C.erase x
  let W := insert e ((S∪T)∪K)
  let J := (EarAnchor.mask H S ⊔ EarAnchor.mask H T) ⊔ EarAnchor.mask H K
  have descr {y z : V} : J.Adj y z ↔ ((y∈S ∧ z∈S ∧ H.Adj y z) ∨ (y∈T ∧ z∈T ∧ H.Adj y z)) ∨ (y∈K ∧ z∈K ∧ H.Adj y z) := Iff.rfl
  have enC : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have ks : K.card=4 := by rw [show K=C.erase x from rfl,card_erase_of_mem xc,cl.2]
  have jk : J.IsNClique 4 K := ⟨fun i im j jm ne => descr.mpr (Or.inr ⟨im,jm,cl.1 (mem_erase.mp im).2 (mem_erase.mp jm).2 ne⟩),ks⟩
  have ki : K⊆C := erase_subset ..
  have ke : e∉K := fun m => enC (ki m)
  have kx : x∉K := not_mem_erase x C
  have dyk : Disjoint S K ∨ Disjoint T K := by
    apply Classical.byContradiction; intro deny
    have no := not_or.mp deny
    obtain ⟨z,zs,zk⟩ := not_disjoint_iff.mp no.1
    obtain ⟨w,wt,wk⟩ := not_disjoint_iff.mp no.2
    have zw : z≠w := fun h => disjoint_left.mp dis (h ▸ zs) wt
    have edge := cl.1 (ki zk) (ki wk) zw
    have za : z=a := by
      by_contra diff
      exact disjoint_left.mp dis (ls z zs diff w edge (mem_erase.mp wk).1) wt
    have wc : w=c := by
      by_contra diff
      exact disjoint_left.mp dis zs (lt w wt diff z edge.symm (mem_erase.mp zk).1)
    exact apart ⟨za ▸ ki zk,wc ▸ ki wk⟩
  have apartJ : ¬J.Reachable a c := by
    intro re
    rcases dyk with sk|tk
    · apply disjoint_left.mp dis _ ct
      apply TrianglePrune.reach_closed J S _ as' re
      intro y ym z edge
      rcases descr.mp edge with (s|t)|k
      · exact s.2.1
      · exact (disjoint_left.mp dis ym t.1).elim
      · exact (disjoint_left.mp sk ym k.1).elim
    · apply disjoint_left.mp dis as' _
      apply TrianglePrune.reach_closed J T _ ct re.symm
      intro y ym z edge
      rcases descr.mp edge with (s|t)|k
      · exact (disjoint_left.mp dis s.1 ym).elim
      · exact t.2.1
      · exact (disjoint_left.mp tk ym k.1).elim
  have sW : S⊆W := subset_union_left.trans (subset_union_left.trans (subset_insert ..))
  have tW : T⊆W := subset_union_right.trans (subset_union_left.trans (subset_insert ..))
  have kW : K⊆W := subset_union_right.trans (subset_insert ..)
  have isolated {v : V} (off : v∉S∪T) (nk : v∉K) (y : V) : ¬J.Adj v y := by
    intro edge
    rcases descr.mp edge with (s|t)|k
    · exact off (mem_union_left _ s.1)
    · exact off (mem_union_right _ t.1)
    · exact nk k.1
  have enough {y z : V} (edge : J.Adj y z) : 0<J.degree y := by
    rw [← card_neighborFinset_eq_degree]; exact card_pos.mpr ⟨z,(J.mem_neighborFinset _ _).mpr edge⟩
  obtain ⟨v,vs,av⟩ := sa; obtain ⟨u,ut,cu⟩ := tc
  apply patch_switch H J ea ec ac.ne (fun eq => enC (eq ▸ xc)) (fun h => xn (h ▸ mem_union_left _ as'))
    (fun h => xn (h ▸ mem_union_right _ ct)) (fun _ _ ed => by rcases descr.mp ed with (s|t)|k <;> first | exact s.2.2 | exact t.2.2 | exact k.2.2)
    (isolated en ke) (isolated xn kx) apartJ jk ke kx (fun y ym => cl.1 xc (ki ym) (mem_erase.mp ym).1.symm)
    (enough (descr.mpr (Or.inl (Or.inl ⟨as',vs,av⟩)))) (enough (descr.mpr (Or.inl (Or.inr ⟨ct,ut,cu⟩))))
    (mem_insert_self e _) (sW as') (tW ct) kW
  · intro y _ z edge
    rcases descr.mp edge with (s|t)|k
    · exact sW s.2.1
    · exact tW t.2.1
    · exact kW k.2.1
  · intro y yx yw
    have ye : y≠e := by intro eq; subst y; exact yw (mem_insert_self ..)
    exact regular H de pos inj safe ye yx
  · intro y yw ye ya yc yx
    by_cases yk : y∈K
    · have d := EarAnchor.sees_in_clique J jk yk; omega
    have st : y∈S∪T := (mem_union.mp ((mem_insert.mp yw).resolve_left ye)).resolve_right yk
    have sub : (Repair.isolate H x).neighborFinset y⊆J.neighborFinset y := by
      intro z zm
      have rel := ((Repair.isolate H x).mem_neighborFinset _ _).mp zm
      apply (J.mem_neighborFinset _ _).mpr; apply descr.mpr; apply Or.inl
      exact (mem_union.mp st).elim (fun ys => Or.inl ⟨ys,ls y ys ya z rel.1 rel.2.2,rel.1⟩)
        (fun yt => Or.inr ⟨yt,lt y yt yc z rel.1 rel.2.2,rel.1⟩)
    have h := card_le_card sub
    rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at h
    have d := regular H de pos inj safe ye yx
    omega

/-- For each safe clique pivot, one of the two endpoints loses every
exterior triangle when the pivot is deleted. -/
theorem cannot_survive {e a c x : V} (de : H.degree e=2) (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (safe : Safe H R x)
    (xm : x∈C) (xa : x≠a) (xc : x≠c) (apart : ¬(a∈C ∧ c∈C))
    {p q u v : V} (pm : p∈interior e a c x) (qm : q∈interior e a c x)
    (um : u∈interior e a c x) (vm : v∈interior e a c x)
    (ap : H.Adj a p) (aq : H.Adj a q) (pq : H.Adj p q)
    (cu : H.Adj c u) (cv : H.Adj c v) (uv : H.Adj u v) : False := by
  have ear : H.neighborFinset e={a,c} := (eq_of_subset_of_card_le
    (insert_subset ((H.mem_neighborFinset _ _).mpr ea) (singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr ec)))
    (by rw [card_pair ac.ne,card_neighborFinset_eq_degree,de])).symm
  have odd := pivot_odd H de ea ec ac.ne pos inj tight cl xm safe
  obtain ⟨S,T,d,am,cm,en,xn,st,ts,left,right⟩ := shores H ea ec ac ear xa.symm xc.symm pm qm um vm ap aq pq cu cv uv odd
  exact region_cut H de ea ec ac pos inj safe cl xm apart d am cm en xn st ts left right tight

end Graffiti384b.RootCut
#print axioms Graffiti384b.RootCut.region_cut
#print axioms Graffiti384b.RootCut.cannot_survive
