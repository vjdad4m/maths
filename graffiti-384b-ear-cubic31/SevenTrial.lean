import SevenModel
namespace Graffiti384b.Seven.Pattern
open Finset SimpleGraph
open private Repair.nbr_add Repair.nbr_mono Repair.full_nbr from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] {H : SimpleGraph V} [DecidableRel H.Adj]
variable (M : Seven.Pattern H)

theorem pattern_bound (n : Fintype.card V=30) (free : H.CliqueFree 5)
    (pos : ∀ v,0<trianglesAt H v) (fi : Function.Injective (trianglesAt H))
    (s0 : trianglesAt H (M.f 0)=1) (s1 : trianglesAt H (M.f 1)=2)
    (s2 : trianglesAt H (M.f 2)=5) : gamma H≤14 := by
  classical
  let S := spines.map M.f
  let T := tips.map M.f
  let W := M.exterior
  obtain ⟨dst,all,din,ns,nt,csp,ctp,fixed⟩ := finite_geometry
  have st : Disjoint S T := by simpa [S,T] using dst
  have board : S∪T=border.map M.f := (map_union ..).symm
  have aw : Disjoint (S∪T) W := disjoint_left.mpr (by
    intro v am wm; rw [board] at am; obtain ⟨j,_,rfl⟩ := mem_map.mp am
    exact mem_compl.mp wm (mem_map.mpr ⟨j,mem_univ _,rfl⟩))
  have ss : S.card=2 := (card_map ..).trans ns
  have ts : T.card=2 := (card_map ..).trans nt
  have ws : W.card=23 := by change (univ.map M.f)ᶜ.card=23; rw [card_compl,card_map,card_univ,n]; decide
  have vals (v : V) (vm : v∈(S∪T)∪W) : 3≤trianglesAt H v ∧ trianglesAt H v≠5 := by
    have off (j : Id) (jm : j∈inner) : v≠M.f j := by
      rintro rfl; rcases mem_union.mp vm with m|m
      · rw [board,mem_map'] at m; exact disjoint_left.mp din m jm
      · exact mem_compl.mp m (mem_map.mpr ⟨j,mem_univ _,rfl⟩)
    have skip (j : Id) (jm : j∈inner) : trianglesAt H v≠trianglesAt H (M.f j) := fun h => off j jm (fi h)
    have a := skip 0 (by decide); have b := skip 1 (by decide); have c := skip 2 (by decide)
    have := pos v; omega
  have wc (v : V) (vm : v∈W) (small : nbr H v W+nbr H v S+nbr H v T≤10) :
      trianglesAt H v≤RankTable.cap (nbr H v W+nbr H v S+nbr H v T) 3 := by
    have zero : nbr H v (inner.map M.f)=0 := card_eq_zero.mpr (eq_empty_of_forall_not_mem (by
      intro z zm; obtain ⟨j,jm,rfl⟩ := mem_map.mp (mem_filter.mp zm).1
      exact M.no_inner vm jm (mem_filter.mp zm).2))
    have d : Disjoint (border.map M.f) (inner.map M.f) := by simpa using din
    have whole : border.map M.f ∪ inner.map M.f=univ.map M.f := by rw [←map_union,all]
    have count := Repair.full_nbr H v (univ.map M.f)
    change nbr H v (univ.map M.f)+nbr H v W=_ at count
    rw [←whole,Repair.nbr_add H v d,zero,←board,Repair.nbr_add H v st] at count
    have deg : H.degree v=nbr H v W+nbr H v S+nbr H v T := by omega
    have u := RankTuran.local_turan H 3 (by decide) free v
    rw [deg] at u
    exact u.trans_eq (RankTable.cap_table ⟨nbr H v W+nbr H v S+nbr H v T,by omega⟩ ⟨3,by decide⟩ (by decide))
  have sc (v : V) (vm : v∈S) (small : nbr H v W+3≤10) : trianglesAt H v≤5+RankTable.cap (nbr H v W+3) 3 := by
    obtain ⟨j,jm,rfl⟩ := mem_map.mp vm
    obtain ⟨b,l⟩ := csp j jm
    have h := M.boundary_score free j
    dsimp only at h; rw [b] at h
    exact (h small).trans (Nat.add_le_add_right l _)
  have tc (v : V) (vm : v∈T) (small : nbr H v W+2≤10) : trianglesAt H v≤2+RankTable.cap (nbr H v W+2) 3 := by
    obtain ⟨j,jm,rfl⟩ := mem_map.mp vm
    obtain ⟨b,l⟩ := ctp j jm
    have h := M.boundary_score free j
    dsimp only at h; rw [b] at h
    exact (h small).trans (Nat.add_le_add_right l _)
  have lim := mass H st aw ss ts ws fi vals wc sc tc
  let K := W.powersetCard 8
  let fail (x : V) (k : Finset V) := failures H W k (fun w => nbr H w S+nbr H w (T.erase x))
  let hit (x w : V) := (K.filter (fun k => w∈fail x k)).card
  have per (w : V) (wm : w∈W) : (∑ x∈T,hit x w)≤weight (nbr H w W) (nbr H w T) (nbr H w S) := by
    exact two_fibers H ts ws wm (fun y => nbr H y S)
  have one (x : V) : (∑ k∈K,(fail x k).card)=∑ w∈W,hit x w := by
    have sub (k : Finset V) : fail x k⊆W := (filter_subset ..).trans sdiff_subset
    calc _ = ∑ k∈K,∑ w∈W,if w∈fail x k then 1 else 0 := by
           apply sum_congr rfl; intro k _; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub k)]
         _ = _ := by rw [sum_comm]; simp [hit,sum_boole]
  have total : (∑ x∈T,∑ k∈K,(fail x k).card)=∑ w∈W,∑ x∈T,hit x w := by
    calc _ = ∑ x∈T,∑ w∈W,hit x w := sum_congr rfl (fun x _ => one x)
         _ = _ := sum_comm
  have existsGood : ∃ x∈T,∃ k∈K,(fail x k).card≤2 := by
    apply Classical.byContradiction; intro no
    have lower (x : V) (xm : x∈T) (k : Finset V) (km : k∈K) : 3≤(fail x k).card := by
      exact Nat.le_of_not_gt (fun small => no ⟨x,xm,k,km,Nat.le_of_lt_succ small⟩)
    have lots : (∑ _x∈T,∑ _k∈K,3)≤∑ x∈T,∑ k∈K,(fail x k).card := sum_le_sum (fun x xm => sum_le_sum (lower x xm))
    have ks : K.card=(23:ℕ).choose 8 := by rw [show K=W.powersetCard 8 from rfl,card_powersetCard,ws]
    rw [total] at lots
    simp only [sum_const,nsmul_eq_mul,ts,ks,Nat.cast_id] at lots
    have bound := (lots.trans (sum_le_sum per)).trans_lt lim
    omega
  obtain ⟨x,xm,k,km,small⟩ := existsGood
  obtain ⟨kw,ks⟩ := mem_powersetCard.mp km
  obtain ⟨a,am,rfl⟩ := mem_map.mp xm
  let P := (pins a).map M.f
  let D := (P∪k)∪fail (M.f a) k
  have front : P∪k⊆D := subset_union_left
  have pin : P⊆D := subset_union_left.trans front
  have sub : S∪T.erase (M.f a)⊆P := by
    intro v vm; rcases mem_union.mp vm with m|m
    · obtain ⟨j,jm,rfl⟩ := mem_map.mp m
      exact mem_map.mpr ⟨j,mem_insert_of_mem (mem_union_left _ jm),rfl⟩
    · obtain ⟨ne,m⟩ := mem_erase.mp m; obtain ⟨j,jm,rfl⟩ := mem_map.mp m
      exact mem_map.mpr ⟨j,mem_insert_of_mem (mem_union_right _ (mem_erase.mpr ⟨fun h => ne (congrArg M.f h),jm⟩)),rfl⟩
  obtain ⟨p4,ok⟩ := fixed a am
  have ps : P.card=4 := (card_map ..).trans p4
  have dom : TwoDominates H D := by
    intro w out; by_cases wm : w∈W
    · have wk : w∉k := fun m => out (front (mem_union_right _ m))
      have good : 2≤nbr H w k+(nbr H w S+nbr H w (T.erase (M.f a))) := by
        apply Nat.le_of_not_gt; intro low
        exact out (mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨wm,wk⟩,low⟩))
      let A := S∪T.erase (M.f a)
      have inc : A⊆S∪T := union_subset_union_right (erase_subset ..)
      have d := Repair.nbr_add H w (aw.mono inc kw)
      have h := Repair.nbr_add H w (st.mono_right (erase_subset (M.f a) T))
      change nbr H w A=_ at h
      have low : 2≤nbr H w (A∪k) := by rw [d,h]; omega
      exact low.trans (Repair.nbr_mono H w ((union_subset_union_left sub).trans front))
    · have m : w∈univ.map M.f := not_not.mp (fun off => wm (mem_compl.mpr off))
      obtain ⟨j,_,rfl⟩ := mem_map.mp m
      have q := ok j (fun jm => out (pin (mem_map.mpr ⟨j,jm,rfl⟩)))
      rw [←M.restrict_nbr j (pins a)] at q
      exact q.trans (Repair.nbr_mono H _ pin)
  have size := card_union_le (P∪k) (fail (M.f a) k)
  have first := card_union_le P k
  have bound : gamma H≤D.card := Nat.sInf_le ⟨_,dom,rfl⟩
  change D.card≤_ at size
  omega

end Graffiti384b.Seven.Pattern
#print axioms Graffiti384b.Seven.Pattern.pattern_bound
