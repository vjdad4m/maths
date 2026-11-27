import FourPool28
namespace Graffiti384b.Four28
open Finset SimpleGraph
open private FiniteRange.bad from FiniteRange384b
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (J : SimpleGraph V) [DecidableRel J.Adj]

def pairReady (W k : Finset V) : Prop := ∃ x∈FiniteRange.bad J W k,∃ y∈FiniteRange.bad J W k,
  J.Adj x y ∧ 1≤nbr J x (Wᶜ∪k)
instance (W k : Finset V) : Decidable (pairReady J W k) := by unfold pairReady; infer_instance

/-- A failed neighbor supplies the second supporter of a singly supported
failure. Both are outside the original seed. -/
theorem trial_repair (W k : Finset V) :
    ∃ T,Wᶜ⊆T ∧ TwoDominates J T ∧
      T.card+(if pairReady J W k then 1 else 0)≤Wᶜ.card+k.card+(FiniteRange.bad J W k).card := by
  classical
  let B := Wᶜ∪k
  let F := FiniteRange.bad J W k
  have base : B.card≤Wᶜ.card+k.card := card_union_le ..
  have good (v : V) (vb : v∉B) (vf : v∉F) : 2≤nbr J v B := by
    have vw : v∈W := Classical.byContradiction (fun no => vb (mem_union_left k (mem_compl.mpr no)))
    exact Nat.le_of_not_gt (fun few => vf (mem_filter.mpr ⟨mem_sdiff.mpr ⟨vw,fun m => vb (mem_union_right _ m)⟩,few⟩))
  by_cases ready : pairReady J W k
  · obtain ⟨x,xf,y,yf,xy,old⟩ := ready
    let T := B∪F.erase x
    have bt : B⊆T := subset_union_left
    have yt : y∈T := mem_union_right _ (mem_erase.mpr ⟨xy.ne.symm,yf⟩)
    have yb : y∉B := by
      obtain ⟨yw,yk⟩ := mem_sdiff.mp (mem_filter.mp yf).1
      exact fun m => (mem_union.mp m).elim (fun c => mem_compl.mp c yw) yk
    have dom : TwoDominates J T := by
      intro v out
      by_cases eq : v=x
      · subst v
        obtain ⟨w,wm⟩ := card_pos.mp old
        obtain ⟨wb,xw⟩ := mem_filter.mp wm
        have wy : w≠y := fun eq => yb (eq ▸ wb)
        exact PinnedColor34.two J wy xw xy (bt wb) yt
      · have vf : v∉F := fun m => out (mem_union_right _ (mem_erase.mpr ⟨eq,m⟩))
        exact (good v (fun m => out (bt m)) vf).trans (Repair.nbr_mono J v bt)
    refine ⟨T,subset_union_left.trans bt,dom,?_⟩
    rw [if_pos (show pairReady J W k from ⟨x,xf,y,yf,xy,old⟩)]
    have drop := card_erase_add_one xf
    have size : T.card≤B.card+(F.erase x).card := card_union_le ..
    change T.card+1≤_+F.card
    change (F.erase x).card+1=F.card at drop
    omega
  · let T := B∪F
    have bt : B⊆T := subset_union_left
    refine ⟨T,subset_union_left.trans bt,fun v out => (good v (fun m => out (bt m))
      (fun m => out (mem_union_right _ m))).trans (Repair.nbr_mono J v bt),?_⟩
    rw [if_neg ready,Nat.add_zero]
    exact (card_union_le ..).trans (Nat.add_le_add_right base _)

theorem pair_frequency {W : Finset V} (ws : W.card=24) {x y : V} (xy : J.Adj x y)
    (xn : J.neighborFinset x⊆W) (yn : J.neighborFinset y⊆W)
    (xlo : 2≤J.degree x) (xd : J.degree x≤4) (yd : J.degree y≤4) :
    77220≤((W.powersetCard 9).filter (pairReady J W)).card := by
  classical
  let U := J.neighborFinset x∪J.neighborFinset y
  let A := U\{x,y}
  let B := W\U
  have uw : U⊆W := union_subset xn yn
  have xu : x∈U := mem_union_right _ ((J.mem_neighborFinset ..).mpr xy.symm)
  have yu : y∈U := mem_union_left _ ((J.mem_neighborFinset ..).mpr xy)
  have za : A.card+2=U.card := by
    rw [←card_pair xy.ne]; exact card_sdiff_add_card_eq_card (insert_subset xu (singleton_subset_iff.mpr yu))
  have zb : B.card=24-U.card := by rw [show B=W\U from rfl,card_sdiff uw,ws]
  have zu : U.card≤8 := by
    have le := card_union_le (J.neighborFinset x) (J.neighborFinset y)
    rw [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at le
    change (J.neighborFinset x∪J.neighborFinset y).card≤8; omega
  have more : 3≤U.card := by
    have sub : insert x (J.neighborFinset x)⊆U := insert_subset xu subset_union_left
    have lt := card_le_card sub
    rw [card_insert_of_not_mem (J.not_mem_neighborFinset_self _),card_neighborFinset_eq_degree] at lt
    omega
  let D := A ×ˢ B.powersetCard 8
  let f (p : V × Finset V) := insert p.1 p.2
  have imageOk (p : V × Finset V) (pm : p∈D) : f p∈(W.powersetCard 9).filter (pairReady J W) := by
    obtain ⟨pa,opts⟩ := mem_product.mp pm
    obtain ⟨bs,eight⟩ := mem_powersetCard.mp opts
    obtain ⟨pu,no⟩ := mem_sdiff.mp pa
    have pin : p.1∉p.2 := fun m => (mem_sdiff.mp (bs m)).2 pu
    let k := f p
    have km : k∈W.powersetCard 9 := mem_powersetCard.mpr ⟨insert_subset (uw pu) (bs.trans sdiff_subset),
      by rw [show k=insert p.1 p.2 from rfl,card_insert_of_not_mem pin,eight]⟩
    have out {z : V} (zm : z∈({x,y}:Finset V)) (zu : z∈U) : z∉k := by
      intro m; rcases mem_insert.mp m with eq|zt
      · exact no (eq ▸ zm)
      · exact (mem_sdiff.mp (bs zt)).2 zu
    have fail (v : V) (vw : v∈W) (vk : v∉k) (n : J.neighborFinset v⊆U) : v∈FiniteRange.bad J W k := by
      refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨vw,vk⟩,?_⟩
      have sub : (Wᶜ∪k).filter (J.Adj v)⊆{p.1} := by
        intro z zm; obtain ⟨zs,edge⟩ := mem_filter.mp zm
        have zU := n ((J.mem_neighborFinset ..).mpr edge)
        rcases mem_union.mp zs with zc|zk
        · exact (mem_compl.mp zc (uw zU)).elim
        · rcases mem_insert.mp zk with eq|zr
          · exact mem_singleton.mpr eq
          · exact ((mem_sdiff.mp (bs zr)).2 zU).elim
      exact ((card_le_card sub).trans_eq (card_singleton _)).trans_lt (by decide)
    have xf := fail x (uw xu) (out (mem_insert_self ..) xu) subset_union_left
    have yf := fail y (uw yu) (out (mem_insert_of_mem (mem_singleton_self _)) yu) subset_union_right
    have one {v : V} (vp : p.1∈J.neighborFinset v) : 1≤nbr J v (Wᶜ∪k) :=
      card_pos.mpr ⟨p.1,mem_filter.mpr ⟨mem_union_right _ (mem_insert_self ..),(J.mem_neighborFinset ..).mp vp⟩⟩
    apply mem_filter.mpr ⟨km,?_⟩
    rcases mem_union.mp pu with nx|ny
    · exact ⟨x,xf,y,yf,xy,one nx⟩
    · exact ⟨y,yf,x,xf,xy.symm,one ny⟩
  have recover (p : V × Finset V) (pm : p∈D) : ((f p)\B)={p.1} ∧ (f p)∩B=p.2 := by
    obtain ⟨pa,opts⟩ := mem_product.mp pm
    have sub := (mem_powersetCard.mp opts).1
    have pb : p.1∉B := fun m => (mem_sdiff.mp m).2 (mem_sdiff.mp pa).1
    constructor <;> ext z
    · simp only [f,mem_sdiff,mem_insert,mem_singleton]
      constructor
      · rintro ⟨eq|m,no⟩; exact eq; exact (no (sub m)).elim
      · rintro rfl; exact ⟨Or.inl rfl,pb⟩
    · simp only [f,mem_inter,mem_insert]
      constructor
      · rintro ⟨rfl|m,inside⟩; exact (pb inside).elim; exact m
      · intro m; exact ⟨Or.inr m,sub m⟩
  have bound := card_le_card_of_injOn f imageOk (by
    intro p pm q qm eq
    apply Prod.ext
    · exact singleton_inj.mp ((recover p pm).1.symm.trans ((congrArg (·\B) eq).trans (recover q qm).1))
    · exact (recover p pm).2.symm.trans ((congrArg (·∩B) eq).trans (recover q qm).2))
  change (A ×ˢ B.powersetCard 8).card≤_ at bound
  rw [card_product,card_powersetCard,zb] at bound
  have table : ∀ i : Fin 9,3 ≤ i.val → 77220≤(i.val-2)*(24-i.val).choose 8 := by decide
  have cert := table ⟨U.card,by omega⟩ more
  change 77220≤(U.card-2)*(24-U.card).choose 8 at cert
  rw [show U.card-2=A.card by omega] at cert
  exact cert.trans bound
end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.trial_repair
#print axioms Graffiti384b.Four28.pair_frequency
