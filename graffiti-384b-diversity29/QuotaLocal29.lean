import Boundary384b
import UnifiedSample384b
import RankTable384b

namespace Graffiti384b.Quota29.Local
open Finset SimpleGraph CliqueChoice CliqueSample LowSample
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private LowSample.delta LowSample.weight from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def tested : Finset ℕ := {3}
private def cutoff (_h : ℕ) (_f : Finset ℕ) := 8
private def cap (d : ℕ) := RankTable.cap d 3
private def limit (h : ℕ) (f : Finset ℕ) (j : ℕ) :=
  let a := slots f j tested
  let n := if j≤cutoff h f then min a (cap j+1) else a
  min (h-f.card) (h+n-29-(f.filter (·≤j)).card)

private def batch (h : ℕ) := if h=27 then 10 else 11
private def Row (h : ℕ) (f : Finset ℕ) : Prop :=
  let m := h-f.card
  let b := batch h
  12≤m ∧ 2≤b ∧ envelope m b ∧ reward m b ∧
    6*(14*m.choose b+UnifiedSample.chargeAt m b (limit h f)) <
    6*(m-b)*m.choose b+(30-h)*(6*(m-2).choose (b-2))+6*(∑ d∈f,bonus m b d)

set_option maxRecDepth 32768 in
private theorem rows : ∀ h∈({27,28}:Finset ℕ),∀ f∈tested.powerset,Row h f := by
  unfold Row batch limit cutoff tested cap RankTable.cap UnifiedSample.chargeAt envelope reward LowSample.delta LowSample.weight bonus slots FiniteRange.badCount
  simp only [FiniteRange.badCount,Nat.choose_eq_fast_choose]
  decide

private theorem mono : ∀ d j : Fin 9,d.val≤j.val → cap d≤cap j := by decide

private theorem distribution {p : Finset V} (ch : Choice G p tested) (t : (types G).card=29)
    (localBound : ∀ v, G.degree v ≤ cutoff (high G).card (p.image (G.degree ·)) → trianglesAt G v ≤ cap (G.degree v))
    (j : ℕ) (hj : 3 ≤ j) :
    ((high G \ p).filter (fun v => G.degree v ≤ j)).card ≤ limit (high G).card (p.image (G.degree ·)) j := by
  let h := (high G).card
  let f := p.image (G.degree ·)
  let s := high G \ p
  let a := (high G).filter (fun v => G.degree v ≤ j)
  let b := p.filter (fun v => G.degree v ≤ j)
  have size : s.card=h-f.card := by dsimp [s,h,f]; rw [card_image_of_injOn ch.unique,card_sdiff ch.high_sub]
  have prof := CliqueChoice.profile G ch j hj
  dsimp only at prof
  rw [t] at prof
  change (s.filter _).card+29+(f.filter (· ≤ j)).card ≤ h+slots f j tested at prof
  have count := card_filter_le s (fun v => G.degree v ≤ j)
  change (s.filter _).card ≤ _
  unfold limit
  change (s.filter (fun v => G.degree v ≤ j)).card ≤ min (h-f.card) (h+(if j≤cutoff h f then min (slots f j tested) (cap j+1) else slots f j tested) -29-(f.filter (· ≤ j)).card)
  apply le_min (count.trans_eq size)
  split_ifs with small
  · have j9 : j<9 := by change j≤8 at small; omega
    have cover : types G ⊆ ((high G)\a).image (trianglesAt G) ∪ range (cap j+1) := by
      intro z hz
      obtain ⟨v,_,rfl⟩ := mem_image.mp hz
      by_cases vd : G.degree v ≤ j
      · apply mem_union_right
        apply mem_range.mpr
        have bounded := localBound v (vd.trans small)
        have step := mono ⟨G.degree v,by omega⟩ ⟨j,j9⟩ vd
        exact Nat.lt_succ_of_le (bounded.trans step)
      · apply mem_union_left
        exact mem_image.mpr ⟨v,mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,
          fun eq => vd (mem_filter.mp eq).2⟩,rfl⟩
    have possible := (card_le_card cover).trans (card_union_le _ _)
    rw [t,card_range] at possible
    have distinct := card_image_le (s := high G \ a) (f := trianglesAt G)
    have total : (high G \ a).card+a.card=h := card_sdiff_add_card_eq_card (filter_subset _ _)
    have sub : b ⊆ a := fun w hw => mem_filter.mpr ⟨ch.high_sub (mem_filter.mp hw).1,(mem_filter.mp hw).2⟩
    have eq : s.filter (fun v => G.degree v ≤ j) = a\b := by ext v; simp only [s,a,b,mem_filter,mem_sdiff]; tauto
    have im : b.image (G.degree ·) = f.filter (· ≤ j) := by ext d; simp [b,f]; aesop
    have bs : b.card=(f.filter (· ≤ j)).card := by
      rw [← im,card_image_of_injOn (ch.unique.mono (show (b : Set V) ⊆ p from filter_subset _ _))]
    have join := card_sdiff_add_card_eq_card sub
    rw [← eq,bs] at join
    omega
  · omega


/-- At 29 types and at least 30 nonleaves, the tripartite Turán cap
through degree eight suffices. -/
theorem exact_of_local_cap (t : (types G).card=29) (q : 30≤(nonleaves G).card)
    (localCap : ∀ v,G.degree v≤8 → trianglesAt G v≤RankTable.cap (G.degree v) 3) : gamma G≤bound G := by
  by_contra! fail
  have lim := type_bound G
  have miss : ((high G).card+1)/2<((types G).card+1)/2 :=
    Nat.lt_of_not_ge (fun le => (not_lt_of_ge (exact_of_high G le)) fail)
  let h := (high G).card
  have hh : h=27 ∨ h=28 := by dsimp [h]; omega
  letI : Nonempty V := by obtain ⟨v,_⟩ := card_pos.mp (show 0<(high G).card by change 0<h; omega); exact ⟨v⟩
  obtain ⟨p,ch⟩ := choose_from G tested (by intro z zm; have := mem_singleton.mp zm; omega)
  let f := p.image (G.degree ·)
  let m := h-f.card
  let b := batch h
  have hs : h∈({27,28}:Finset ℕ) := by simpa using hh
  obtain ⟨room,two,env,rew,win⟩ := rows h hs f (mem_powerset.mpr ch.levels)
  have size : (high G\p).card=m := by dsimp [m,h,f]; rw [card_image_of_injOn ch.unique,card_sdiff ch.high_sub]
  have obs := UnifiedSample.extraObstruction G ch b (limit h f) (fun j _ pos => distribution G ch t localCap j pos)
    (fun _ => 0) (by intro v hv; rw [Nat.add_zero]; exact FiniteRange.count_bad G _ b _ v hv (min_le_left _ _) (by omega))
    two (size ▸ env) (size ▸ rew) fail
  dsimp only at obs
  simp only [sum_const_zero,Nat.mul_zero,Nat.add_zero,t] at obs
  change 6*(m-b)*m.choose b+(twos G).card*(6*(m-2).choose (b-2))+6*(∑ d∈f,bonus m b d)≤
    6*(14*m.choose b+UnifiedSample.chargeAt m b (limit h f)) at obs
  change 6*(14*m.choose b+UnifiedSample.chargeAt m b (limit h f)) <
    6*(m-b)*m.choose b+(30-h)*(6*(m-2).choose (b-2))+6*(∑ d∈f,bonus m b d) at win
  have sub : high G⊆nonleaves G := fun v vm => mem_filter.mpr ⟨mem_univ _,by have := (mem_filter.mp vm).2; omega⟩
  have total : (twos G).card+h=(nonleaves G).card := card_sdiff_add_card_eq_card sub
  have val := Nat.mul_le_mul_right (6*(m-2).choose (b-2)) (show 30-h≤(twos G).card by omega)
  omega

theorem exact_of_five_free (t : (types G).card=29) (q : 30≤(nonleaves G).card)
    (free : G.CliqueFree 5) : gamma G≤bound G := by
  apply exact_of_local_cap G t q
  intro v dv
  exact (RankTuran.local_turan G 3 (by decide) free v).trans_eq
    (RankTable.cap_table ⟨G.degree v,by omega⟩ ⟨3,by decide⟩ (by decide))

end Graffiti384b.Quota29.Local
#print axioms Graffiti384b.Quota29.Local.exact_of_local_cap
#print axioms Graffiti384b.Quota29.Local.exact_of_five_free
