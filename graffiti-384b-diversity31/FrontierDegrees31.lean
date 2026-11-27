import FrontierTable31
namespace Graffiti384b.Frontier31
open Finset SimpleGraph CliqueChoice CliqueSample LowSample DegreeRows
open private Repair.triangles_le_choose from Repair384b
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 2400000 in
/-- One necessary dense degree can still be found after excluding any
specified degree between five and eight when 32 nonleaves are available. -/
theorem avoiding {skip : ℕ} (sk : skip∈({0,5,6,7,8}:Finset ℕ)) (t : (types G).card=31)
    (q : required skip≤(nonleaves G).card) (fail : bound G<gamma G) :
    ∃ v,5≤G.degree v ∧ G.degree v≤8 ∧ G.degree v≠skip ∧ RankTable.cap (G.degree v) 3<trianglesAt G v := by
  classical
  by_contra! no
  have sk9 : skip<9 := by simp only [mem_insert,mem_singleton] at sk; omega
  have lim := type_bound G
  have miss : ((high G).card+1)/2 < ((types G).card+1)/2 :=
    Nat.lt_of_not_ge (fun le => (not_lt_of_ge (exact_of_high G le)) fail)
  let h := (high G).card
  have hs : h∈({29,30}:Finset ℕ) := by simp only [mem_insert,mem_singleton]; dsimp [h]; omega
  letI : Nonempty V := by
    obtain ⟨v,_⟩ := card_pos.mp (show 0<(high G).card by omega); exact ⟨v⟩
  obtain ⟨P,ch⟩ := choose_from G Boundary.levels (fun _ z => (mem_Icc.mp z).1)
  let f := P.image (G.degree ·)
  let S := high G\P
  let m := h-f.card
  have sz : S.card=m := by dsimp [S,m,h,f]; rw [card_image_of_injOn ch.unique,card_sdiff ch.high_sub]
  obtain ⟨room,env,rew,strict⟩ := rows skip sk h hs f (mem_powerset.mpr ch.levels)
  have localCap (v : V) : trianglesAt G v≤capAt skip (G.degree v) := by
    unfold capAt; split_ifs with test
    · exact no v test.1 test.2.1 test.2.2
    · exact Repair.triangles_le_choose G v
  have dist (j : ℕ) (jj : j∈range 11) (pos : 3≤j) :
      (S.filter (fun v => G.degree v≤j)).card≤countAt skip h f j := by
    let L := (high G).filter (fun v => G.degree v≤j)
    let F := P.filter (fun v => G.degree v≤j)
    have cover : types G⊆((high G)\L).image (trianglesAt G)∪range (capAt skip j+1) := by
      intro a am; obtain ⟨v,_,rfl⟩ := mem_image.mp am
      by_cases low : G.degree v≤j
      · apply mem_union_right; apply mem_range.mpr
        have u := cap_mono ⟨_,sk9⟩ ⟨_,lt_of_le_of_lt low (mem_range.mp jj)⟩ ⟨_,mem_range.mp jj⟩ low
        exact Nat.lt_succ_of_le ((localCap v).trans u)
      · exact mem_union_left _ (mem_image.mpr ⟨v,mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,
          fun z => low (mem_filter.mp z).2⟩,rfl⟩)
    have c := (card_le_card cover).trans (card_union_le _ _); rw [t,card_range] at c
    have im := card_image_le (s:=high G\L) (f:=trianglesAt G)
    have cl : (high G\L).card+L.card=h := card_sdiff_add_card_eq_card (filter_subset ..)
    have sub : F⊆L := fun w wm => mem_filter.mpr ⟨ch.high_sub (mem_filter.mp wm).1,(mem_filter.mp wm).2⟩
    have fl : F.image (G.degree ·)=f.filter (·≤j) := by
      ext d; constructor
      · intro dm
        obtain ⟨v,vm,rfl⟩ := mem_image.mp dm
        obtain ⟨vp,vd⟩ := mem_filter.mp vm
        exact mem_filter.mpr ⟨mem_image_of_mem _ vp,vd⟩
      · intro dm
        obtain ⟨im,dj⟩ := mem_filter.mp dm
        obtain ⟨v,vm,rfl⟩ := mem_image.mp im
        exact mem_image.mpr ⟨v,mem_filter.mpr ⟨vm,dj⟩,rfl⟩
    have fc : F.card=(f.filter (·≤j)).card := by
      rw [←fl,card_image_of_injOn (ch.unique.mono (show (F:Set V)⊆P from filter_subset ..))]
    have eq : S.filter (fun v => G.degree v≤j)=L\F := by ext v; simp only [S,F,L,mem_filter,mem_sdiff]; tauto
    have count := card_sdiff_add_card_eq_card sub
    have bound := CliqueChoice.profile G ch j pos
    dsimp only at bound; rw [t] at bound
    change (S.filter (fun v => G.degree v≤j)).card+31+(f.filter (·≤j)).card≤h+slots f j Boundary.levels at bound
    unfold countAt
    apply le_min ((card_filter_le _ _).trans_eq sz)
    rw [eq] at bound ⊢; omega
  have obs := UnifiedSample.extraObstruction G ch 11 (countAt skip h f) dist (fun _ => 0)
    (by
      intro v vm
      rw [Nat.add_zero]
      exact FiniteRange.count_bad G _ 11 _ v vm (min_le_left _ _) (by
        change _<S.card; rw [sz]; omega)) (by decide) (sz ▸ env) (sz ▸ rew) fail
  dsimp only at obs
  simp only [sum_const_zero,Nat.mul_zero,Nat.add_zero,t] at obs
  change 6*(m-11)*m.choose 11+(twos G).card*(6*(m-2).choose 9)+6*(∑ d∈f,bonus m 11 d)≤
    6*(15*m.choose 11+UnifiedSample.chargeAt m 11 (countAt skip h f)) at obs
  change 6*(15*m.choose 11+UnifiedSample.chargeAt m 11 (countAt skip h f)) <
    6*(m-11)*m.choose 11+(required skip-h)*(6*(m-2).choose 9)+6*(∑ d∈f,bonus m 11 d) at strict
  have sub : high G⊆nonleaves G := fun v vm => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp vm).2; omega⟩
  have count : (twos G).card+h=(nonleaves G).card := card_sdiff_add_card_eq_card sub
  have credit := Nat.mul_le_mul_right (6*(m-2).choose 9) (show required skip-h≤(twos G).card by omega)
  omega

end Graffiti384b.Frontier31
#print axioms Graffiti384b.Frontier31.avoiding
