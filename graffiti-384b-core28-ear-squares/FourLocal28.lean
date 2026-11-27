import FourCharges28

namespace Graffiti384b.Four28
open Finset SimpleGraph JointRank
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Centers outside the closed neighborhoods of P whose links exceed Mantel's bound. -/
def remote (P : Finset V) (h : ℕ) : Finset V :=
  univ.filter (fun v => v∉P ∧ nbr G v P=0 ∧ G.degree v≤h ∧
    RankTable.cap (G.degree v) 2<trianglesAt G v)

private theorem protected_zero (P : Finset V) (v : V) (support : 2≤nbr G v P) :
    fibers G Pᶜ 9 v=0 := by
  apply card_eq_zero.mpr
  apply filter_eq_empty_iff.mpr
  intro s _
  intro fail
  have low := (mem_filter.mp fail).2
  rw [compl_compl] at low
  have more := support.trans (Repair.nbr_mono G v (show P⊆P∪s from subset_union_left))
  omega

/-- For a single arbitrary seed, or two seeds protecting the rank-zero
vertex, the two weighted sample budgets force distant four-clique centers. -/
theorem remote_count (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (free : G.CliqueFree 5) (half : 14≤gamma G)
    (P : Finset V) (size : P.card∈({1,2}:Finset ℕ))
    (special : P.card=2 → ∃ e,trianglesAt G e=1 ∧ 2≤nbr G e P)
    (h : ℕ) (hm : h∈({8,9}:Finset ℕ)) : h-7≤(remote G P h).card := by
  classical
  let k := P.card
  let W := Pᶜ
  let rk := rank univ (trianglesAt G)
  let d := fun v => min (G.degree v) 10
  have options : k=1 ∨ k=2 := by simpa only [mem_insert,mem_singleton,k] using size
  have cuts : h=8 ∨ h=9 := by simpa only [mem_insert,mem_singleton] using hm
  have ws : W.card=28-k := by simp [W,k,card_compl,n]
  have wc : Wᶜ.card=k := by simp [W,k]
  have rankpos (v : V) : 1+rk v≤trianglesAt G v := rank_lower _ _ fi.injOn 1 (fun v _ => pos v) (mem_univ _)
  have lo (v : V) : d v≤G.degree v := min_le_left ..
  have hi (v : V) : d v≤10 := min_le_right ..
  have full := Core28.degree_budget G 28 10 n (by omega) d lo
  have seeded := pool_budget G W 9
  rw [ws,wc] at seeded
  have req : (28-k).choose 9*(5-k)≤∑ v,fibers G W 9 v :=
    (Nat.mul_le_mul_left _ (by omega : 5-k≤gamma G-k-9)).trans seeded
  have lim (v : V) : fullPrice k*FiniteRange.badCount 28 10 (d v)+seedPrice k*fibers G W 9 v≤
      charge k h (rk v)+(if v∈remote G P h then extra k else 0) := by
    have ri : rk v<28 := by
      have m := mem_image_of_mem (rank univ (trianglesAt G)) (mem_univ v)
      rwa [rank_range _ _ fi.injOn,card_univ,n,mem_range] at m
    have cap : rk v+1≤RankTable.cap (d v) 3 ∨ d v=10 := by
      by_cases maxed : d v=10
      · exact Or.inr maxed
      have eq : G.degree v=d v := by dsimp [d] at *; omega
      have upper := RankTuran.local_turan G 3 (by decide) free v
      have row := RankTable.cap_table ⟨d v,by have := hi v; omega⟩ ⟨3,by decide⟩ (by decide)
      change (turanGraph (d v) 3).edgeFinset.card=RankTable.cap (d v) 3 at row
      rw [eq,row] at upper
      apply Or.inl; have := rankpos v; omega
    have tab := charge_rows k size h hm ⟨rk v,ri⟩ ⟨d v,by have := hi v; omega⟩ cap
    dsimp only at tab
    by_cases vm : v∈W
    · by_cases spec : k=2 ∧ rk v=0
      · obtain ⟨e,se,sp⟩ := special spec.1
        have re := rankpos e
        have same : rk v=rk e := by omega
        have ve := rank_inj univ (trianglesAt G) fi.injOn (mem_univ v) (mem_univ e) same
        have z := protected_zero G P v (ve ▸ sp)
        rw [z,Nat.mul_zero,Nat.add_zero]
        exact tab.1.trans (Nat.le_add_right ..)
      · have use := tab.2 (by omega)
        have outside : v∉P := mem_compl.mp vm
        by_cases touched : ∃ w∈P,G.Adj v w
        · obtain ⟨w,wp,edge⟩ := touched
          have one : 1≤d v := by
            have dg := (G.card_neighborFinset_eq_degree v) ▸
              (card_pos.mpr ⟨w,(G.mem_neighborFinset ..).mpr edge⟩ : 0<(G.neighborFinset v).card)
            dsimp [d]; omega
          have short := BoundaryFiber.count G W 9 (d v) vm (fun m => mem_compl.mp m wp) edge (lo v) one
          change fibers G W 9 v≤_ at short
          rw [ws] at short
          exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ short) _).trans
            (use.1.trans (Nat.le_add_right ..))
        · have all := FiniteRange.count_bad G W 9 (d v) v vm (lo v) (by rw [ws]; have := hi v; omega)
          change fibers G W 9 v≤_ at all
          rw [ws] at all
          apply (Nat.add_le_add_left (Nat.mul_le_mul_left _ all) _).trans
          by_cases far : v∈remote G P h
          · rw [if_pos far]; exact use.2.2
          · rw [if_neg far,Nat.add_zero]
            apply use.2.1
            by_cases big : h<d v
            · exact Or.inr big
            · apply Or.inl
              have eq : G.degree v=d v := by dsimp [d] at *; omega
              have nn : nbr G v P=0 := by
                change (P.filter (G.Adj v)).card=0
                rw [filter_eq_empty_iff.mpr (fun x xm ed => touched ⟨x,xm,ed⟩),card_empty]
              have notbig : trianglesAt G v≤RankTable.cap (G.degree v) 2 := Nat.le_of_not_gt
                (fun gt => far (mem_filter.mpr ⟨mem_univ _,outside,nn,by omega,gt⟩))
              rw [eq] at notbig; have := rankpos v; omega
    · have z : fibers G W 9 v=0 := by
        apply card_eq_zero.mpr
        exact filter_eq_empty_iff.mpr (fun s _ m => vm (mem_sdiff.mp (mem_filter.mp m).1).1)
      rw [z,Nat.mul_zero,Nat.add_zero]
      exact tab.1.trans (Nat.le_add_right ..)
  have both := sum_le_sum (s:=univ) (fun v _ => lim v)
  simp only [sum_add_distrib,←mul_sum] at both
  have rks := sum_by_rank univ (trianglesAt G) fi.injOn (charge k h)
  rw [card_univ,n] at rks
  change (∑ v,charge k h (rk v))=_ at rks
  have rebate : (∑ v,if v∈remote G P h then extra k else 0)=(remote G P h).card*extra k := by simp
  rw [rks,rebate] at both
  change (28:ℕ).choose 10*4≤_ at full
  have joint := (Nat.add_le_add (Nat.mul_le_mul_left (fullPrice k) full) (Nat.mul_le_mul_left (seedPrice k) req)).trans both
  have row := totals k size h hm
  by_contra! few
  have card : (remote G P h).card≤h-8 := by
    rcases cuts with rfl|rfl <;> simp_all only [Nat.reduceSub] <;> omega
  exact (Nat.not_lt_of_ge (joint.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (extra k) card) _))) row

end Graffiti384b.Four28
#print axioms Graffiti384b.Four28.remote_count
