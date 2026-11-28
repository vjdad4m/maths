import TriangleReturns
namespace Graffiti384b.TriangleFrame
open Finset SimpleGraph PrivatePatch SixFront FiveChoice
open private Repair.edge_info from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
variable {P Q D : Finset V} {A : V→Finset V}

/-- A terminal reservation would have just its original triangle at each of its two free vertices. -/
theorem Frame.thin_at_terminal (F : Frame G P Q D A) (T : Terminal G P Q)
    {a x m : V} (ad : a∈D) (pair : A a={x,m})
    (ax : G.Adj a x) (am : G.Adj a m) (xm : G.Adj x m) : trianglesAt G x≤1 := by
  classical
  by_contra! many
  change 1<(link G x).card at many
  obtain ⟨p,pm,other⟩ := exists_ne_of_one_lt_card many ({a,m}:Finset V)
  obtain ⟨sub,size,cl⟩ := Repair.edge_info G pm
  obtain ⟨u,v,uv,shape⟩ := card_eq_two.mp size
  have up : u∈p := shape ▸ mem_insert_self ..
  have vp : v∈p := shape ▸ mem_insert_of_mem (mem_singleton_self _)
  have xu := (G.mem_neighborFinset ..).mp (sub up)
  have xv := (G.mem_neighborFinset ..).mp (sub vp)
  have edge := cl u up v vp uv
  have mark {z w : V} (zw : G.Adj z w) (xw : G.Adj x w) (dist : ({z,w}:Finset V)≠{a,m}) :
      z≠a ∧ z≠m := by
    constructor
    · rintro rfl
      have wm : w≠m := fun eq => dist (by rw [eq])
      exact F.no_return G T ad pair ax am xm xw zw.ne.symm wm (Or.inl zw)
    · rintro rfl
      have wa : w≠a := fun eq => dist (by rw [eq,pair_comm])
      exact F.no_return G T ad pair ax am xm xw wa zw.ne.symm (Or.inr zw)
  have ne : ({u,v}:Finset V)≠{a,m} := fun eq => other (shape.trans eq)
  have mu := mark edge xv ne
  have mv := mark edge.symm xu (by rwa [pair_comm v u])
  have outside : ∀z∈({u,v}:Finset V),z∉(P∪Q)∪D.biUnion A := by
    intro z h; rcases mem_insert.mp h with rfl|h
    · exact F.exterior G T ad pair ax am xm xu mu.1 mu.2
    · obtain rfl := mem_singleton.mp h; exact F.exterior G T ad pair ax am xm xv mv.1 mv.2
  have shifted := F.shift G ad pair ax am xm xu xv edge outside
  exact T _ _ _ _ (subset_insert ..) (subset_insert ..)
    ⟨x,mem_union_left _ (mem_insert_self ..),disjoint_left.mp (F.free a ad) (pair ▸ mem_insert_self ..)⟩ shifted

/-- There is no triangle with two unpinned vertices each occurring in only this triangle. -/
def NoThinPair (P Q : Finset V) : Prop :=
  ∀a x m : V,x∉P∪Q → m∉P∪Q → G.Adj a x → G.Adj a m → G.Adj x m →
    2≤trianglesAt G x ∨ 2≤trianglesAt G m

/-- In a finite graph without a free thin pair, any number of deficient pins
with disjoint free triangle pairs can simultaneously be given two opposite neighbors.
The conclusion preserves every initial pin on its prescribed shore. -/
theorem simultaneous_extension (P Q D : Finset V) (A : V→Finset V)
    (F : Frame G P Q D A) (no : NoThinPair G P Q) : Extension G P Q := by
  classical
  suffices go : ∀k : ℕ,∀ (P Q D : Finset V) (A : V→Finset V),
      (P∪Q)ᶜ.card=k → Frame G P Q D A → NoThinPair G P Q → Extension G P Q by
    exact go _ P Q D A rfl F no
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro P Q D A ck F no
    by_contra bad
    have T : Terminal G P Q := by
      intro L R S B pl qr fresh next
      obtain ⟨v,vm,vn⟩ := fresh
      have inc := union_subset_union pl qr
      have strict : (P∪Q).card<(L∪R).card :=
        card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨inc,fun eq => vn (eq ▸ vm)⟩)
      have fl := card_add_card_compl (P∪Q)
      have fr := card_add_card_compl (L∪R)
      have lifted : NoThinPair G L R :=
        fun a x m xo mo => no a x m (fun u => xo (inc u)) (fun u => mo (inc u))
      obtain ⟨L',R',ll,rr,protect⟩ := ih _ (by omega : (L∪R)ᶜ.card<k) L R S B rfl next lifted
      exact bad ⟨L',R',pl.trans ll,qr.trans rr,protect⟩
    by_cases empty : D=∅
    · exact bad ⟨P,Q,Subset.rfl,Subset.rfl,F.apart,fun v vp => F.left v vp (by simp [empty]),F.right⟩
    obtain ⟨a,ad⟩ := nonempty_iff_ne_empty.mpr empty
    obtain ⟨x,m,pair,ax,am,xm⟩ := F.privatePair a ad
    have outside := disjoint_left.mp (F.free a ad)
    rcases no a x m (outside (pair ▸ mem_insert_self ..)) (outside (pair ▸ mem_insert_of_mem (mem_singleton_self _))) ax am xm with rich|rich
    · have h := F.thin_at_terminal G T ad pair ax am xm; omega
    · have h := F.thin_at_terminal G T ad (pair.trans (pair_comm ..)) am ax xm.symm; omega

/-- Apply the extension when all degree-two vertices have already been pinned. -/
theorem catalogue_bound (P Q D : Finset V) (A : V→Finset V)
    (F : Frame G P Q D A) (no : NoThinPair G P Q)
    (quota : (types G).card≤(nonleaves G).card) (pinned : LowSample.twos G⊆P∪Q) :
    gamma G≤bound G := by
  obtain ⟨L,R,pl,qr,cut⟩ := simultaneous_extension G P Q D A F no
  apply PinnedColor34.complete G cut.1 quota _ cut.2.1 cut.2.2
  intro v vn vl vr
  by_contra! small
  have tv : v∈LowSample.twos G := mem_sdiff.mpr ⟨vn,fun hi => (not_le_of_gt small) (mem_filter.mp hi).2⟩
  exact (mem_union.mp (pinned tv)).elim (fun m => vl (pl m)) (fun m => vr (qr m))

end Graffiti384b.TriangleFrame
#print axioms Graffiti384b.TriangleFrame.Frame.thin_at_terminal
#print axioms Graffiti384b.TriangleFrame.simultaneous_extension
#print axioms Graffiti384b.TriangleFrame.catalogue_bound
