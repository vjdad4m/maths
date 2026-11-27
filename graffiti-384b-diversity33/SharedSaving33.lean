import SharedSample33

namespace Graffiti384b.ForcedCubics
open Finset SimpleGraph PositiveCore33
open private Repair.full_nbr Repair.nbr_mono Repair.triangles_le_choose from Repair384b
open private FiniteRange.bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- With a cubic of score at least two, any third neighbor has a link
to at least one member of the fixed pair. -/
private theorem third_contact {u p q x : V} (du : H.degree u=3) (us : 2≤trianglesAt H u)
    (pq : p≠q) (up : H.Adj u p) (uq : H.Adj u q) (ux : H.Adj u x) (xp : x≠p) (xq : x≠q) :
    H.Adj x p ∨ H.Adj x q := by
  have nx : H.neighborFinset u={x,p,q} := (eq_of_subset_of_card_le (insert_subset ((H.mem_neighborFinset ..).mpr ux)
    (insert_subset ((H.mem_neighborFinset ..).mpr up) (singleton_subset_iff.mpr ((H.mem_neighborFinset ..).mpr uq))))
    (by simp [xp,xq,pq,du])).symm
  obtain ⟨y,uy,xy⟩ := cubic_supported H du us ux
  have ym := (H.mem_neighborFinset ..).mpr uy
  rw [nx] at ym
  rcases (show y=x ∨ y=p ∨ y=q by simpa using ym) with same|rfl|rfl
  · exact (xy.ne same.symm).elim
  · exact Or.inl xy
  · exact Or.inr xy

/-- Two shared neighbors meeting all five-cliques give a 2-dominating
set of size at most fifteen. The two cubics are omitted and the shared pair is kept. -/
theorem shared_saving {u v p q : V} (n : Fintype.card V=32) (du : H.degree u=3)
    (us : trianglesAt H u=2) (dv : H.degree v=3) (vs : trianglesAt H v=3)
    (pq : p≠q) (up : H.Adj u p) (uq : H.Adj u q) (vp : H.Adj v p) (vq : H.Adj v q)
    (pos : ∀ w,0<trianglesAt H w) (inj : Function.Injective (trianglesAt H))
    (hit : ∀ C,H.IsNClique 5 C → p∈C ∨ q∈C) : gamma H≤15 := by
  classical
  have uv : u≠v := by intro eq; subst u; omega
  let S := ({u,v}:Finset V)ᶜ
  let J := H.induce (S:Set V)
  let i : S := ⟨p,by simp [S,up.ne.symm,vp.ne.symm]⟩
  let j : S := ⟨q,by simp [S,uq.ne.symm,vq.ne.symm]⟩
  have ij : i≠j := fun h => pq (congrArg Subtype.val h)
  let W := ({i,j}:Finset S)ᶜ
  have cardS : Fintype.card S=30 := by rw [Fintype.card_coe]; simp [S,card_compl,n,uv]
  have ws : W.card=28 := by simp [W,card_compl,cardS,ij]
  let f (w : S) := trianglesAt H w.val
  have fi : Function.Injective f := fun _ _ h => Subtype.ext (inj h)
  have range' (w : S) (_ : w∈W) : f w=1 ∨ 4≤f w := by
    have off : w.val≠u ∧ w.val≠v := by simpa [S,not_or] using w.property
    have x : f w≠2 := fun eq => off.1 (inj (eq.trans us.symm))
    have y : f w≠3 := fun eq => off.2 (inj (eq.trans vs.symm))
    have h : 0<f w := pos _; omega
  have sumdeg (w : S) : nbr H w.val {u,v}+J.degree w=H.degree w.val := by
    rw [EarAnchor.induced_degree]; exact Repair.full_nbr H w.val {u,v}
  have pairOff (w : S) (wm : w∈W) : w.val≠p ∧ w.val≠q := by
    have a : w≠i ∧ w≠j := by simpa [W,not_or] using wm
    exact ⟨fun h => a.1 (Subtype.ext h),fun h => a.2 (Subtype.ext h)⟩
  have im : i∉W := by simp [W]
  have jm : j∉W := by simp [W]
  have plain (w : S) (wm : w∈W) (away : ∀ b,b∉W → ¬J.Adj w b) :
      f w≤(turanGraph (J.degree w) 3).edgeFinset.card := by
    have np : ¬H.Adj w.val p := away i im
    have nq : ¬H.Adj w.val q := away j jm
    have off := pairOff w wm
    have nu : ¬H.Adj w.val u := fun h => (third_contact H du us.ge pq up uq h.symm off.1 off.2).elim np nq
    have nv : ¬H.Adj w.val v := fun h => np (EarAnchor.full_neighbors H dv vs h.symm vp off.1)
    have no : ({u,v}:Finset V).filter (H.Adj w.val)=∅ := filter_eq_empty_iff.mpr (by
      intro b bm; rcases (show b=u ∨ b=v by simpa using bm) with rfl|rfl
      · exact nu
      · exact nv)
    have h := sumdeg w
    change (({u,v}:Finset V).filter (H.Adj w.val)).card+_= _ at h
    rw [no,card_empty,Nat.zero_add] at h
    rw [h]
    exact EarPalette.pair_turan H pq off.1 off.2 np nq hit
  have single (w : S) (wm : w∈W) (b : S) (_ : b∉W) (_ : J.Adj w b) (inc : J.neighborFinset w⊆insert b W) :
      f w≤(J.degree w+1).choose 2 := by
    have off := pairOff w wm
    have nv : ¬H.Adj w.val v := by
      intro h
      have ip : J.Adj w i := EarAnchor.full_neighbors H dv vs h.symm vp off.1
      have jq : J.Adj w j := EarAnchor.full_neighbors H dv vs h.symm vq off.2
      have ib := (mem_insert.mp (inc ((J.mem_neighborFinset ..).mpr ip))).resolve_right im
      have jb := (mem_insert.mp (inc ((J.mem_neighborFinset ..).mpr jq))).resolve_right jm
      exact ij (ib.trans jb.symm)
    have sub : ({u,v}:Finset V).filter (H.Adj w.val)⊆{u} := by
      intro t' tm
      obtain ⟨inside,edge⟩ := mem_filter.mp tm
      rcases (show t'=u ∨ t'=v by simpa using inside) with rfl|rfl
      · exact mem_singleton_self _
      · exact (nv edge).elim
    have le : nbr H w.val {u,v}≤1 := (card_le_card sub).trans_eq (card_singleton _)
    have h := sumdeg w
    exact (Repair.triangles_le_choose H _).trans (Nat.choose_le_choose 2 (by omega))
  obtain ⟨k,km,small⟩ := sample J ws f fi range' plain single
  obtain ⟨_,ks⟩ := mem_powersetCard.mp km
  let T := Wᶜ∪k∪FiniteRange.bad J W k
  have front : Wᶜ∪k⊆T := subset_union_left
  have ti : i∈T := front (mem_union_left _ (mem_compl.mpr im))
  have tj : j∈T := front (mem_union_left _ (mem_compl.mpr jm))
  have dom : TwoDominates J T := by
    intro w out
    have wm : w∈W := by apply Classical.byContradiction; intro no; exact out (front (mem_union_left _ (mem_compl.mpr no)))
    apply (show 2≤nbr J w (Wᶜ∪k) from ?_).trans (Repair.nbr_mono J w front)
    apply Nat.le_of_not_gt; intro low
    exact out (mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨wm,fun h => out (front (mem_union_right _ h))⟩,low⟩))
  let D := T.map (Function.Embedding.subtype _)
  have lift {w : S} (m : w∈T) : w.val∈D := mem_map.mpr ⟨w,m,rfl⟩
  have domH : TwoDominates H D := by
    intro w out
    by_cases wm : w∈S
    · let x : S := ⟨w,wm⟩
      have h := dom x (fun m => out (lift m))
      have map : (T.filter (J.Adj x)).map (Function.Embedding.subtype _)=D.filter (H.Adj w) := by
        ext y; constructor
        · intro ym; obtain ⟨b,bm,rfl⟩ := mem_map.mp ym
          exact mem_filter.mpr ⟨lift (mem_filter.mp bm).1,(mem_filter.mp bm).2⟩
        · intro ym; obtain ⟨b,bm,rfl⟩ := mem_map.mp (mem_filter.mp ym).1
          exact mem_map.mpr ⟨b,mem_filter.mpr ⟨bm,(mem_filter.mp ym).2⟩,rfl⟩
      change 2≤(D.filter (H.Adj w)).card
      rwa [←map,card_map]
    · have m : w=u ∨ w=v := by simpa only [S,mem_compl,Classical.not_not,mem_insert,mem_singleton] using wm
      rcases m with rfl|rfl
      · exact PinnedColor34.two H pq up uq (lift ti) (lift tj)
      · exact PinnedColor34.two H pq vp vq (lift ti) (lift tj)
  have cap := card_union_le (Wᶜ∪k) (FiniteRange.bad J W k)
  have first := card_union_le Wᶜ k
  have pair : Wᶜ.card=2 := by simp [W,ij]
  have size : D.card=T.card := card_map ..
  have bound : gamma H≤D.card := Nat.sInf_le ⟨_,domH,rfl⟩
  change T.card≤_ at cap
  omega

end Graffiti384b.ForcedCubics
#print axioms Graffiti384b.ForcedCubics.shared_saving
