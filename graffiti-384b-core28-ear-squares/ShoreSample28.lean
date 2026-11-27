import RankTable384b
namespace Graffiti384b.Core28
open Finset SimpleGraph JointRank
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def floorD (s : ℕ) := if s≤1 then 2 else if s≤3 then 3 else if s≤5 then 4 else if s≤8 then 5
  else if s≤12 then 6 else if s≤16 then 7 else if s≤21 then 8 else if s≤27 then 9 else 10

private theorem floor_table : ∀ s : Fin 32,0<s.val → ∀ d : Fin 10,d.val<floorD s →
    RankTable.cap d 3<s.val := by decide

theorem degree_floor (cf : G.CliqueFree 5) (v : V) {s : ℕ} (lo : 0<s) (hi : s<32)
    (under : s≤trianglesAt G v) : floorD s≤G.degree v := by
  by_contra! less
  have cap : floorD s≤10 := by unfold floorD; split_ifs <;> decide
  have value := RankTuran.local_turan G 3 (by decide) cf v
  have num := RankTable.cap_table ⟨G.degree v,by omega⟩ ⟨3,by decide⟩ (by decide)
  change (turanGraph (G.degree v) 3).edgeFinset.card=RankTable.cap (G.degree v) 3 at num
  have lt := floor_table ⟨s,hi⟩ lo ⟨G.degree v,by omega⟩ less
  change RankTable.cap (G.degree v) 3<s at lt
  omega

def fee (n b s : ℕ) := FiniteRange.badCount n b (floorD s)

theorem degree_budget (n b : ℕ) (nc : Fintype.card V=n) (half : n≤2*gamma G)
    (d : V → ℕ) (lower : ∀ v,d v≤G.degree v) :
    n.choose b*(n/2-b)≤∑ v,FiniteRange.badCount n b (d v) := by
  classical
  let W := (univ:Finset V)
  let opts := W.powersetCard b
  let fail := fun k => FiniteRange.bad G W k
  let hit := fun v => (opts.filter (fun k => v∈fail k)).card
  have per (v : V) (vm : v∈W) : hit v≤FiniteRange.badCount n b (d v) := by
    have room := G.degree_lt_card_verts v
    have bound := FiniteRange.count_bad G W b _ v vm (lower v) (by simpa [W] using (lower v).trans_lt room)
    simpa [W,opts,hit,fail,fee,nc] using bound
  have total : (∑ k∈opts,(fail k).card)=∑ v∈W,hit v := by
    have sub (k : Finset V) : fail k⊆W := (filter_subset ..).trans sdiff_subset
    calc _ = ∑ k∈opts,∑ v∈W,if v∈fail k then 1 else 0 := by
           apply sum_congr rfl; intro k _; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub k)]
         _ = _ := by rw [sum_comm]; simp [hit,sum_boole]
  have need (k : Finset V) (km : k∈opts) : n/2-b≤(fail k).card := by
    have kb := (mem_powersetCard.mp km).2
    let D := k∪fail k
    have dom : TwoDominates G D := by
      intro v vd
      have vk : v∉k := fun h => vd (mem_union_left _ h)
      have vf : v∉fail k := fun h => vd (mem_union_right _ h)
      have enough : 2≤nbr G v (Wᶜ∪k) := by
        by_contra! low
        exact vf (mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,vk⟩,low⟩)
      have sub : Wᶜ∪k⊆D := by simp [W,D]
      exact enough.trans (card_le_card (filter_subset_filter _ sub))
    have upper : gamma G≤D.card := Nat.sInf_le ⟨D,dom,rfl⟩
    have size : D.card≤k.card+(fail k).card := card_union_le .. 
    omega
  have many := sum_le_sum need
  rw [total] at many
  have optsN : opts.card=n.choose b := by rw [show opts=W.powersetCard b from rfl,card_powersetCard,show W.card=n from card_univ.trans nc]
  calc _ = ∑ _k∈opts,(n/2-b) := by simp [optsN]
       _ ≤ _ := many
       _ ≤ _ := sum_le_sum per

/-- A half-tight five-clique-free graph pays the displayed deficiency budget for
any positive integer labels lying below its triangle counts. -/
theorem budget (n b : ℕ) (nc : Fintype.card V=n) (half : n≤2*gamma G)
    (free : G.CliqueFree 5) (f : V → ℕ)
    (positive : ∀ v,0<f v) (small : ∀ v,f v<32) (low : ∀ v,f v≤trianglesAt G v) :
    n.choose b*(n/2-b)≤∑ v,fee n b (f v) := by
  exact degree_budget G n b nc half (fun v => floorD (f v))
    (fun v => degree_floor G free v (positive v) (small v) (low v))

def batch (n : ℕ) := if n≤14 then n/2-1 else if n≤20 then n/2-2 else if n≤26 then n/2-3 else 10

set_option maxRecDepth 32768 in
private theorem offset_table : ∀ n : Fin 29,6≤n.val → n.val%2=0 →
    (∑ i∈range n.val,fee n (batch n) (4+i))<n.val.choose (batch n)*(n.val/2-batch n) := by
  unfold fee batch floorD FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]
  decide

/-- A tight even five-clique-free graph of order at most 28 with distinct
positive scores must realize at least one of the three smallest scores. -/
theorem small_score (n : ℕ) (nc : Fintype.card V=n) (room : 6≤n) (hi : n≤28) (ev : n%2=0)
    (free : G.CliqueFree 5) (fi : Function.Injective (trianglesAt G)) (half : n≤2*gamma G) :
    ∃ v,trianglesAt G v<4 := by
  classical
  by_contra! no
  let rank := JointRank.rank (univ:Finset V) (trianglesAt G)
  have rlo (v : V) : 4+rank v≤trianglesAt G v := rank_lower _ _ fi.injOn 4 (fun w _ => no w) (mem_univ _)
  have rhi (v : V) : rank v<n := by
    have mem := mem_image_of_mem (JointRank.rank univ (trianglesAt G)) (mem_univ v)
    rw [rank_range _ _ fi.injOn,card_univ,nc] at mem
    exact mem_range.mp mem
  have pay := budget G n (batch n) nc half free (fun v => 4+rank v)
    (fun v => by change 0<4+rank v; omega) (fun v => by change 4+rank v<32; have := rhi v; omega) rlo
  have sm := sum_by_rank univ (trianglesAt G) fi.injOn (fun i => fee n (batch n) (4+i))
  change (∑ v,fee n (batch n) (4+rank v))=_ at sm
  rw [card_univ,nc] at sm
  rw [sm] at pay
  exact (Nat.not_le_of_gt (offset_table ⟨n,by omega⟩ room ev)) pay
end Graffiti384b.Core28
#print axioms Graffiti384b.Core28.budget
#print axioms Graffiti384b.Core28.small_score
