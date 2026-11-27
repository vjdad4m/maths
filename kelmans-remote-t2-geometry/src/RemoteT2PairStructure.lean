import RemoteT2PairCounts
import RemoteT2Scope

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteT2PairStructure
open SquareCap (SmallTrivial boundary)
open RemoteT2PairCounts (outside_cut_balance OutsideTwo innerCut)
open RemoteT2Scope (Remote cyclic_four_pair_no_common)
noncomputable section
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
def OutsideSome (c : V→Bool) (x y : V) (b : Bool) : Prop :=
  ∃ z : V,z≠x∧z≠y∧c z=b

def surviving (x y z : V) : Finset V := ((G.neighborFinset z).erase x).erase y

theorem surviving_card_lb {x y z : V}
    (cub : G.degree z=3) (none : ¬(G.Adj z x∧G.Adj z y)) :
    2≤(surviving G x y z).card := by
  unfold surviving
  by_cases first : G.Adj z x
  · have ny : y∉G.neighborFinset z := fun h=>none ⟨first,(mem_neighborFinset _ _ _).mp h⟩
    have ny' : y∉(G.neighborFinset z).erase x := fun h=>ny (mem_erase.mp h).2
    rw [erase_eq_of_not_mem ny',card_erase_of_mem ((mem_neighborFinset _ _ _).mpr first),
      card_neighborFinset_eq_degree,cub]
  · have nx : x∉G.neighborFinset z := fun h=>first ((mem_neighborFinset _ _ _).mp h)
    rw [erase_eq_of_not_mem nx]
    by_cases second : G.Adj z y
    · rw [card_erase_of_mem ((mem_neighborFinset _ _ _).mpr second),
        card_neighborFinset_eq_degree,cub]
    · have ny : y∉G.neighborFinset z := fun h=>second ((mem_neighborFinset _ _ _).mp h)
      rw [erase_eq_of_not_mem ny,card_neighborFinset_eq_degree,cub]
      decide

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem in_boundary {c : V→Bool} {u v : V} :
    (u,v)∈boundary G c ↔ c u=true∧c v=false∧G.Adj u v := by
  classical
  simp [boundary]

private theorem single_shore_cut {x y : V} (c : V→Bool) (b : Bool)
    (cub : ∀ z,G.degree z=3) (common : ∀ z,¬(G.Adj x z∧G.Adj y z))
    (some : OutsideSome c x y b) (notTwo : ¬OutsideTwo c x y b) :
    2≤(innerCut G c x y).card := by
  obtain ⟨z,zx,zy,zc⟩ := some
  have unique (u : V) (ux : u≠x) (uy : u≠y) (uc : c u=b) : u=z := by
    by_contra no
    exact notTwo ⟨z,u,zx,zy,ux,uy,Ne.symm no,zc,uc⟩
  let f (u : V) : V×V := if b then (z,u) else (u,z)
  have inj : Function.Injective f := by
    intro a d e
    cases b
    · exact congrArg Prod.fst e
    · exact congrArg Prod.snd e
  have image : (surviving G x y z).image f ⊆ innerCut G c x y := by
    intro q hq
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hq
    obtain ⟨uy,ux,adj⟩ : u≠y∧u≠x∧G.Adj z u := by
      simpa [surviving,mem_neighborFinset] using hu
    have un : c u≠b := fun e=>adj.ne (unique u ux uy e).symm
    cases b
    · have ct : c u=true := by cases e : c u <;> simp_all
      exact mem_filter.mpr ⟨(in_boundary G).mpr ⟨ct,zc,adj.symm⟩,ux,uy,zx,zy⟩
    · have cf : c u=false := by cases e : c u <;> simp_all
      exact mem_filter.mpr ⟨(in_boundary G).mpr ⟨zc,cf,adj⟩,zx,zy,ux,uy⟩
  have m := card_le_card image
  rw [card_image_of_injective _ inj] at m
  exact (surviving_card_lb G (cub z) (fun ⟨a,d⟩=>common z ⟨a.symm,d.symm⟩)).trans m

/-- Every proper cut left after deleting an adjacent pair has at least
two edges. Here cuts are counted on the surviving vertices, so this
includes singleton shores. -/
theorem no_cut_below_two (small : SmallTrivial G) (big : 5≤Fintype.card V)
    (cub : ∀ z,G.degree z=3) {x y : V} (xy : G.Adj x y) (c : V→Bool)
    (pos : OutsideSome c x y true) (neg : OutsideSome c x y false) :
    2≤(innerCut G c x y).card := by
  have common := cyclic_four_pair_no_common small big cub xy
  by_cases p : OutsideTwo c x y true
  · by_cases q : OutsideTwo c x y false
    · exact (outside_cut_balance G small c xy (cub x) (cub y) p q).1
    · exact single_shore_cut G c false cub common neg q
  · exact single_shore_cut G c true cub common pos p

/-- An additional edge omission leaves every proper surviving cut
nonempty, so the deleted-pair graph remains connected after the
omission. This does not require the remote restriction. -/
theorem cut_after_omission_nonempty (small : SmallTrivial G) (big : 5≤Fintype.card V)
    (cub : ∀ z,G.degree z=3) {x y : V} (xy : G.Adj x y) (c : V→Bool)
    (pos : OutsideSome c x y true) (neg : OutsideSome c x y false) (a b : V) :
    ∃ e∈innerCut G c x y,e≠(a,b)∧e≠(b,a) := by
  by_contra! fail
  obtain ⟨e,he,t,ht,eT⟩ := one_lt_card.mp
    (no_cut_below_two G small big cub xy c pos neg)
  have pick (q : V×V) (hq : q∈innerCut G c x y) : q=(a,b)∨q=(b,a) := by
    by_cases h : q=(a,b)
    · exact Or.inl h
    · exact Or.inr (fail q hq h)
  rcases pick e he with e'|e' <;> rcases pick t ht with t'|t'
  · exact eT (e'.trans t'.symm)
  · have k := (in_boundary G).mp (mem_filter.mp he).1
    have l := (in_boundary G).mp (mem_filter.mp ht).1
    rw [e'] at k
    rw [t'] at l
    exact Bool.noConfusion (k.1.symm.trans l.2.1)
  · have k := (in_boundary G).mp (mem_filter.mp he).1
    have l := (in_boundary G).mp (mem_filter.mp ht).1
    rw [e'] at k
    rw [t'] at l
    exact Bool.noConfusion (l.1.symm.trans k.2.1)
  · exact eT (e'.trans t'.symm)

def survivingOmit (x y a b z : V) : Finset V :=
  (surviving G x y z).filter (fun w=>¬((z=a∧w=b)∨(z=b∧w=a)))

private theorem full_surviving {x y z : V} (hx : ¬G.Adj z x) (hy : ¬G.Adj z y) :
    surviving G x y z=G.neighborFinset z := by
  unfold surviving
  have mx : x∉G.neighborFinset z := fun h=>hx ((mem_neighborFinset _ _ _).mp h)
  have my : y∉G.neighborFinset z := fun h=>hy ((mem_neighborFinset _ _ _).mp h)
  have nx : (G.neighborFinset z).erase x=G.neighborFinset z := erase_eq_of_not_mem mx
  rw [nx,erase_eq_of_not_mem my]

private theorem leaf_is_omitted_endpoint (cub : G.degree z=3)
    (none : ¬(G.Adj z x∧G.Adj z y)) (h : (survivingOmit G x y a b z).card≤1) :
    z=a∨z=b := by
  by_contra! bad
  have e : survivingOmit G x y a b z=surviving G x y z := by
    ext u
    simp [survivingOmit,bad.1,bad.2]
  have m := surviving_card_lb G cub none
  rw [e] at h
  omega

private theorem endpoint_two_without_pair (cub : G.degree z=3) (hx : ¬G.Adj z x)
    (hy : ¬G.Adj z y) (ne : a≠b) :
    2≤(survivingOmit G x y a b z).card := by
  by_cases za : z=a
  · have odds : survivingOmit G x y a b z=(G.neighborFinset z).erase b := by
      rw [survivingOmit,full_surviving G hx hy]
      ext u
      simp [za,ne,and_comm]
    rw [odds]
    by_cases bmem : b∈G.neighborFinset z
    · rw [card_erase_of_mem bmem,card_neighborFinset_eq_degree,cub]
    · rw [erase_eq_of_not_mem bmem,card_neighborFinset_eq_degree,cub]; decide
  · by_cases zb : z=b
    · have odds : survivingOmit G x y a b z=(G.neighborFinset z).erase a := by
        rw [survivingOmit,full_surviving G hx hy]
        ext u
        simp [zb,ne.symm,and_comm]
      rw [odds]
      by_cases amem : a∈G.neighborFinset z
      · rw [card_erase_of_mem amem,card_neighborFinset_eq_degree,cub]
      · rw [erase_eq_of_not_mem amem,card_neighborFinset_eq_degree,cub]; decide
    · have odds : survivingOmit G x y a b z=G.neighborFinset z := by
        ext u
        simp [survivingOmit,full_surviving G hx hy,za,zb]
      rw [odds,card_neighborFinset_eq_degree,cub]; decide

/-- In the remote case, at most one surviving vertex has degree at
most one. It must be an endpoint of the omitted edge that sees y. -/
theorem remote_at_most_one_leaf (small : SmallTrivial G) (big : 5≤Fintype.card V)
    (cub : ∀ z,G.degree z=3) {x y a b : V} (xy : G.Adj x y) (ab : G.Adj a b)
    (remote : Remote G x a b) :
    ∀ s t : V, (survivingOmit G x y a b s).card≤1 →
      (survivingOmit G x y a b t).card≤1 → s=t := by
  have common := cyclic_four_pair_no_common small big cub xy
  have commonAB := cyclic_four_pair_no_common small big cub ab
  have ports (z : V) (h : (survivingOmit G x y a b z).card≤1) :
      (z=a∨z=b) ∧ G.Adj z y := by
    have ends := leaf_is_omitted_endpoint G (cub z)
      (fun ⟨p,q⟩=>common z ⟨p.symm,q.symm⟩) h
    have noX : ¬G.Adj z x := by
      rcases ends with rfl|rfl
      · exact fun e=>remote.2.2.1 e.symm
      · exact fun e=>remote.2.2.2 e.symm
    refine ⟨ends,?_⟩
    by_contra ny
    have deg := endpoint_two_without_pair G (cub z) noX ny ab.ne
    omega
  intro s t hs ht
  obtain ⟨sp,sy⟩ := ports s hs
  obtain ⟨tp,ty⟩ := ports t ht
  rcases sp with rfl|rfl <;> rcases tp with rfl|rfl
  · rfl
  · exact (commonAB y ⟨sy,ty⟩).elim
  · exact (commonAB y ⟨ty,sy⟩).elim
  · rfl

#print axioms no_cut_below_two
#print axioms cut_after_omission_nonempty
#print axioms remote_at_most_one_leaf
end
end KelmansCactus.AtomicBridge.RemoteT2PairStructure
