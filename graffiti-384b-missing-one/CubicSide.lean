import SplitShore
namespace Graffiti384b.OddStars.CubicSide
open Finset SimpleGraph LeafCritical ShorePairs SplitShore
open private ShoreRanks.six_high from ShoreRanks
open private ShoreCounts.in_high from ShoreCounts
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The two fixed cubics and their nonadjacency exclude a six-vertex
high set. The ambient graph can have arbitrary further vertices. -/
theorem beyond_six (bad : bound G<gamma G) (one : 1∉types G) {u v : V}
    (su : trianglesAt G u=2) (sv : trianglesAt G v=3) (uv : ¬(patch G ∅).Adj u v)
    (classify : ∀w,(patch G ∅).degree w=3 ↔ w=u ∨ w=v)
    {A : Finset V} (mx : Maximum (patch G ∅) A) : 6<(high (patch G ∅)).card := by
  classical
  let J := patch G ∅
  let H := high J
  have sz := (PaletteCorollaries.upper_iff_no_one G bad).mpr one
  have du : J.degree u=3 := (classify u).mpr (Or.inl rfl)
  have dv : J.degree v=3 := (classify v).mpr (Or.inr rfl)
  have uh : u∈H := mem_filter.mpr ⟨mem_univ _,by omega⟩
  have vh : v∈H := mem_filter.mpr ⟨mem_univ _,by omega⟩
  have lower := ShoreRanks.six_high G bad sz ⟨u,uh⟩ mx
  by_contra! small
  have six : H.card=6 := by change 6≤H.card at lower; change H.card≤6 at small; omega
  have cover (w : V) : J.neighborFinset w⊆H.erase w := fun z zm =>
    let ed := (J.mem_neighborFinset ..).mp zm
    mem_erase.mpr ⟨ed.ne.symm,ShoreCounts.in_high G bad sz ed⟩
  let N := J.neighborFinset u
  have n : N.card=3 := (card_neighborFinset_eq_degree ..).trans du
  obtain ⟨p,pm,q,qm,pq,no⟩ : ∃p∈N,∃q∈N,p≠q ∧ ¬J.Adj p q := by
    by_contra! clique
    have fill : pairs J N=N.powersetCard 2 := filter_eq_self.mpr (fun _ k i im j jm ne =>
      clique i ((mem_powersetCard.mp k).1 im) j ((mem_powersetCard.mp k).1 jm) ne)
    have score : trianglesAt G u=(pairs J N).card := (patch_scores G ∅ u).symm
    rw [fill,card_powersetCard,n] at score
    have choose : Nat.choose 3 2=3 := by decide
    omega
  have must {b c : V} (bm : b∈N) (cm : c∈N) (bc : b≠c) (apart : ¬J.Adj b c) : J.Adj v b := by
    have ub := (J.mem_neighborFinset ..).mp bm
    have uc := (J.mem_neighborFinset ..).mp cm
    have bh := ShoreCounts.in_high G bad sz ub
    have ch := ShoreCounts.in_high G bad sz uc
    have bv : b≠v := fun e => uv (e ▸ ub)
    have cv : c≠v := fun e => uv (e ▸ uc)
    by_contra vb
    have nd : J.degree b≠3 := fun eq => ((classify _).mp eq).elim ub.ne.symm bv
    have highb : 3≤J.degree b := (mem_filter.mp bh).2
    let B := ((H.erase b).erase c).erase v
    have inC : c∈H.erase b := mem_erase.mpr ⟨bc.symm,ch⟩
    have inV : v∈(H.erase b).erase c := mem_erase.mpr ⟨cv.symm,mem_erase.mpr ⟨bv.symm,vh⟩⟩
    have sub : J.neighborFinset b⊆B := fun w wm =>
      let bw := (J.mem_neighborFinset ..).mp wm
      mem_erase.mpr ⟨fun e => vb (e ▸ bw.symm),mem_erase.mpr ⟨fun e => apart (e ▸ bw),cover b wm⟩⟩
    have low := card_le_card sub
    change (J.neighborFinset b).card≤(((H.erase b).erase c).erase v).card at low
    rw [card_neighborFinset_eq_degree,card_erase_of_mem inV,card_erase_of_mem inC,card_erase_of_mem bh,six] at low
    omega
  have vp := must pm qm pq no
  have vq := must qm pm pq.symm (fun e => no e.symm)
  exact no (FixedCubics.full_neighbors J dv ((patch_scores G ∅ v).trans sv) vp vq pq)

/-- The score-two and score-three cubics must lie on the same shore in
every maximum cut of a connected missing-one failure. -/
theorem same_shore (conn : G.Connected) (ord : 2<Fintype.card V) (bad : bound G<gamma G)
    (one : 1∉types G) :
    ∃u v : V,trianglesAt G u=2 ∧ trianglesAt G v=3 ∧
      (∀w,(patch G ∅).degree w=3 ↔ w=u ∨ w=v) ∧
      ∀A : Finset V,Maximum (patch G ∅) A → (u∈A ↔ v∈A) := by
  obtain ⟨_,u,v,_,su,sv,uv,char,crit⟩ := PaletteCorollaries.missing_one_failure G conn ord bad one
  refine ⟨u,v,su,sv,char,?_⟩
  intro A mx
  have big := beyond_six G bad one su sv uv char mx
  constructor
  · intro ua; by_contra va
    exact (not_le_of_gt big) (split_cap G bad one mx ua va char (crit _ mx))
  · intro va; by_contra ua
    exact (not_le_of_gt big) (split_cap G bad one mx va ua (fun w => (char w).trans or_comm)
      (by rw [crit _ mx,pair_comm]))
end Graffiti384b.OddStars.CubicSide
#print axioms Graffiti384b.OddStars.CubicSide.beyond_six
#print axioms Graffiti384b.OddStars.CubicSide.same_shore
