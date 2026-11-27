import SevenFinish

namespace Graffiti384b.EarCredit
open SimpleGraph Finset
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private Repair.omit_set Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def active (P k : Finset V) := P.filter (fun z => 2≤nbr G z k)

/-- A fixed vertex may be dropped once two of its mutually adjacent neighbors
are sampled. Its remaining neighbors then see both witnesses as well. -/
theorem trial {P k : Finset V} (sub : k⊆Pᶜ)
    (simplicial : ∀ z∈P,∀ u v,G.Adj z u → G.Adj z v → u≠v → G.Adj u v)
    (n : Fintype.card V=30) (hi : 15≤gamma G) :
    Pᶜ.card-k.card+(active G P k).card≤15+(FiniteRange.bad G Pᶜ k).card := by
  classical
  let W := Pᶜ
  let F := FiniteRange.bad G W k
  let A := (W\k)\F
  let R := active G P k
  let O := A∪R
  have aw : A⊆W := sdiff_subset.trans sdiff_subset
  have rp : R⊆P := filter_subset ..
  have keep : k⊆Oᶜ := by
    intro y ym; apply mem_compl.mpr; intro m; rcases mem_union.mp m with a|r
    · exact (mem_sdiff.mp (mem_sdiff.mp a).1).2 ym
    · exact mem_compl.mp (sub ym) (rp r)
  have safe (v : V) (m : v∈O) : 2≤nbr G v Oᶜ := by
    rcases mem_union.mp m with a|r
    · have outside := (mem_sdiff.mp (mem_sdiff.mp a).1).2
      by_cases exposed : ∃ z∈R,G.Adj z v
      · obtain ⟨z,zm,zv⟩ := exposed
        have inc : k.filter (G.Adj z)⊆Oᶜ.filter (G.Adj v) := by
          intro y ym; obtain ⟨yk,zy⟩ := mem_filter.mp ym
          exact mem_filter.mpr ⟨keep yk,simplicial z (rp zm) v y zv zy (fun h => outside (h ▸ yk))⟩
        exact (mem_filter.mp zm).2.trans (card_le_card inc)
      · have good : 2≤nbr G v (Wᶜ∪k) := Nat.le_of_not_gt (fun h =>
          (mem_sdiff.mp a).2 (mem_filter.mpr ⟨(mem_sdiff.mp a).1,h⟩))
        apply good.trans (card_le_card ?_)
        intro y ym
        obtain ⟨mem,vy⟩ := mem_filter.mp ym
        refine mem_filter.mpr ⟨?_,vy⟩
        rcases mem_union.mp mem with off|yk
        · exact mem_compl.mpr (fun h => (mem_union.mp h).elim (fun m => mem_compl.mp off (aw m)) (fun m => exposed ⟨y,m,vy.symm⟩))
        · exact keep yk
    · exact (mem_filter.mp r).2.trans (Repair.nbr_mono G _ keep)
  have bound := Repair.omit_set G O safe
  have dis : Disjoint A R := disjoint_left.mpr (fun _ a r => mem_compl.mp (aw a) (rp r))
  have size : O.card=A.card+R.card := card_union_of_disjoint dis
  have part : A.card+F.card=W.card-k.card := by
    rw [←card_sdiff sub]; exact card_sdiff_add_card_eq_card (filter_subset ..)
  change W.card-k.card+R.card≤15+F.card
  omega

theorem active_fiber {P : Finset V} (b : ℕ) {z : V} (zm : z∈P) (pool : G.neighborFinset z⊆Pᶜ) :
    CliqueSample.bonus Pᶜ.card b (G.degree z)≤((Pᶜ.powersetCard b).filter (fun k => z∈active G P k)).card := by
  classical
  let W := Pᶜ
  have off : z∉W := fun m => mem_compl.mp m zm
  have inc : (W.powersetCard b).filter (fun k => z∉active G P k) ⊆
      ((insert z W).powersetCard b).filter (fun k => z∈FiniteRange.bad G (insert z W) k) := by
    intro k km; obtain ⟨s,no⟩ := mem_filter.mp km
    obtain ⟨kw,kb⟩ := mem_powersetCard.mp s
    have same : nbr G z ((insert z W)ᶜ∪k)=nbr G z k := by
      apply congrArg card; ext y; simp only [mem_filter,mem_union]; constructor
      · rintro ⟨m,zy⟩; exact ⟨m.resolve_left (fun h => mem_compl.mp h (mem_insert_of_mem (pool ((G.mem_neighborFinset ..).mpr zy)))),zy⟩
      · rintro ⟨m,zy⟩; exact ⟨Or.inr m,zy⟩
    exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨kw.trans (subset_insert ..),kb⟩,
      mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_insert_self ..,fun m => off (kw m)⟩,
      same ▸ Nat.lt_of_not_ge (fun h => no (mem_filter.mpr ⟨zm,h⟩))⟩⟩
  have deg : G.degree z≤W.card := by rw [←card_neighborFinset_eq_degree]; exact card_le_card pool
  have up := FiniteRange.count_bad G (insert z W) b (G.degree z) z (mem_insert_self ..) le_rfl (by rw [card_insert_of_not_mem off]; omega)
  rw [card_insert_of_not_mem off] at up
  have first := (card_le_card inc).trans up
  have tot := filter_card_add_filter_neg_card_eq_card (s:=W.powersetCard b) (fun k => z∈active G P k)
  rw [card_powersetCard] at tot
  unfold CliqueSample.bonus
  change W.card.choose b-FiniteRange.badCount (W.card+1) b (G.degree z)≤((W.powersetCard b).filter (fun k => z∈active G P k)).card
  omega

theorem sum_count {P : Finset V} (b : ℕ) (n : Fintype.card V=30) (hi : 15≤gamma G)
    (sc : ∀ z∈P,∀ u v,G.Adj z u → G.Adj z v → u≠v → G.Adj u v)
    (ind : ∀ z∈P,G.neighborFinset z⊆Pᶜ) :
    let W := Pᶜ
    (W.card-b)*W.card.choose b+(∑ z∈P,CliqueSample.bonus W.card b (G.degree z))≤
    15*W.card.choose b+∑ w∈W,((W.powersetCard b).filter (fun k => w∈FiniteRange.bad G W k)).card := by
  classical
  let W := Pᶜ
  let K := W.powersetCard b
  have count (B : Finset V) (f : Finset V→Finset V) (sub : ∀ k,f k⊆B) :
      (∑ k∈K,(f k).card)=∑ w∈B,(K.filter (fun k => w∈f k)).card := by
    calc _ = ∑ k∈K,∑ w∈B,if w∈f k then 1 else 0 := by
           apply sum_congr rfl; intro k _; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub k)]
         _ = _ := by rw [sum_comm]; simp [sum_boole]
  have low := sum_le_sum (s:=K) (fun k km => by
    obtain ⟨kw,kb⟩ := mem_powersetCard.mp km
    have h := trial G (P:=P) kw sc n hi
    rw [kb] at h; exact h)
  have activeSum := sum_le_sum (fun z zm => active_fiber G b zm (ind z zm))
  rw [sum_add_distrib,sum_add_distrib,count P (active G P) (fun _ => filter_subset ..),
    count W (FiniteRange.bad G W) (fun _ => (filter_subset ..).trans sdiff_subset)] at low
  have ks : K.card=W.card.choose b := card_powersetCard ..
  simp only [sum_const,nsmul_eq_mul,ks,Nat.cast_id] at low
  dsimp only
  rw [Nat.mul_comm (Pᶜ.card-b),Nat.mul_comm 15]
  exact (Nat.add_le_add_left activeSum _).trans low

end Graffiti384b.EarCredit
#print axioms Graffiti384b.EarCredit.trial
#print axioms Graffiti384b.EarCredit.sum_count
