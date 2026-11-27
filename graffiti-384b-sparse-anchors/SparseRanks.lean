import SparseMass
import AnchorCuts
namespace Graffiti384b.SparsePairs
open Finset SimpleGraph JointRank Simplicial16
open private SparsePairs.active29 from SparseMass
open private Repair.triangles_le_choose from Repair384b
open private FiniteRange.bad FiniteRange.count_bad from FiniteRange384b
open private EarCredit.credited from CreditRanks31
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private def row (r : ℕ) := if r=0 then 12701405 else if r=1 then 10538255
  else if r<4 then 10341168 else if r<8 then 7072408 else if r<13 then 4585308
  else if r<19 then 2821728 else if r<25 then 1646008 else 906984

/-- The saving for an unselected anchor, in the uniform sample of eleven high vertices. -/
def credit (r : ℕ) := if r=0 then 4975245 else if r=1 then 6080855
  else if r<4 then 5883768 else if r<8 then 4576264 else if r<13 then 3233230
  else if r<19 then 2116296 else if r<25 then 1293292 else 739024

def augmented (r d : ℕ) := max (credit r + if r=0 ∧ 4≤d then 3124550 else 0)
  (row r-(29-min d 10).choose 11)

theorem credit_le_augmented (r d : ℕ) : credit r≤augmented r d :=
  (Nat.le_add_right ..).trans (le_max_left ..)

/-- Lower bounds for an anchor whose actual degree is larger than the lowest
degree permitted at its triangle-count rank. -/
theorem degree_discount {r d : ℕ} :
    (r≤1 → 5≤d → 8042111≤augmented r d) ∧
    (r≤3 → 5≤d → 7845024≤augmented r d) ∧
    (r≤7 → 9≤d → 6904448≤augmented r d) := by
  have tab : ∀ i : Fin 8,∀ j : Fin 11,
      (i.val≤1 → 5≤j.val → 8042111≤row i-(29-j.val).choose 11) ∧
      (i.val≤3 → 5≤j.val → 7845024≤row i-(29-j.val).choose 11) ∧
      (9≤j.val → 6904448≤row i-(29-j.val).choose 11) := by
    unfold row; simp only [Nat.choose_eq_fast_choose]; decide
  have h (small : r≤7) := tab ⟨r,by omega⟩ ⟨min d 10,by omega⟩
  have right := le_max_right (credit r+if r=0 ∧ 4≤d then 3124550 else 0) (row r-(29-min d 10).choose 11)
  change _≤augmented r d at right
  exact ⟨fun a b => ((h (by omega)).1 a (by dsimp only; omega)).trans right,
    fun a b => ((h (by omega)).2.1 a (by dsimp only; omega)).trans right,
    fun a b => ((h a).2.2 (by dsimp only; omega)).trans right⟩

def massBound (bonus : ℕ) : Prop :=
  let X := high G
  let E := LowSample.twos G
  let K := X.powersetCard 11
  bonus+3*(29:ℕ).choose 11+(∑ e∈E,(29-nbr G e X).choose (11-nbr G e X))+
    (∑ v∈X,(K.filter (fun s => v∈activated G X s)).card)+
    (∑ v∈X,(K.filter (fun s => v∈TwoEars.extra G X E s)).card)≤
    ∑ v∈X,(K.filter (fun s => v∈FiniteRange.bad G X s)).card

private def refund (hit : Bool) (r d : ℕ) := if r=0 ∧ d=3 then (if hit then 0 else 1562275)
  else if r+2=d.choose 2 then (28:ℕ).choose 10-FiniteRange.badCount 29 10 d else 0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
private theorem table : ∀ r : Fin 29,∀ d : Fin 11,3≤d.val → (r.val+2≤d.val.choose 2 ∨ d.val=10) →
    (d.val=10 ∨ d.val+r.val+1≤29+2*(d.val.choose 2-(r.val+2))) →
    FiniteRange.badCount 29 11 d≤row r+refund false r d ∧
    (29-d.val).choose 11+augmented r d≤row r+refund true r d := by
  unfold row refund augmented credit FiniteRange.badCount
  simp only [Nat.choose_eq_fast_choose]; decide

set_option maxHeartbeats 2000000 in
theorem rank_account (t : (types G).card=31) (q : (nonleaves G).card=31)
    (failure : bound G<gamma G) (bonus : ℕ) (mass : massBound G bonus) :
    let X := high G
    let A := (LowSample.twos G).biUnion (G.neighborFinset ·)
    bonus+(∑ a∈A, augmented (rank X (trianglesAt G) a) (G.degree a))≤12407000 := by
  classical
  let X := high G
  let E := LowSample.twos G
  let A := E.biUnion (G.neighborFinset ·)
  let r := rank X (trianglesAt G)
  change bonus+(∑ a∈A,augmented (r a) (G.degree a))≤12407000
  obtain ⟨hs,es⟩ := TwoEars.profile G t q failure
  obtain ⟨inj,lo,_,_⟩ := Repair.maximal_diversity G (by omega)
  have sed (e : V) (he : e∈E) : G.degree e=2 := by
    obtain ⟨m,off⟩ := mem_sdiff.mp he
    have lower := (mem_filter.mp m).2
    by_contra h; exact off (mem_filter.mpr ⟨mem_univ _,by omega⟩)
  have aa : A⊆X := by
    intro a am; obtain ⟨e,em,ea⟩ := mem_biUnion.mp am
    exact TwoEars.high_anchors G t q failure (sed e em) ea
  have rk {v : V} (vh : v∈X) : r v<29 := by
    have h := mem_image_of_mem (rank X (trianglesAt G)) vh
    rwa [rank_range _ _ inj,hs,mem_range] at h
  have lr {v : V} (vh : v∈X) : 2+r v≤trianglesAt G v := rank_lower _ _ inj 2 lo vh
  have fit {v : V} (vh : v∈high G) :
      G.degree v+r v+1≤29+2*((G.degree v).choose 2-(r v+2)) := by
    let L := (high G).filter (fun w => trianglesAt G w<trianglesAt G v)
    let U := (G.neighborFinset v).filter (fun w => trianglesAt G v≤trianglesAt G w)
    have inc : insert v L⊆high G := insert_subset vh (filter_subset ..)
    have off : v∉L := fun h => lt_irrefl _ (mem_filter.mp h).2
    have sub : U⊆high G\insert v L := by
      intro w wm; obtain ⟨wn,sw⟩ := mem_filter.mp wm
      have wh : w∈high G := by
        by_contra h
        have lw : G.degree w≤2 := Nat.le_of_not_gt (fun h' => h (mem_filter.mpr ⟨mem_univ _,h'⟩))
        have limit := (Repair.triangles_le_choose G w).trans (Nat.choose_le_choose 2 lw)
        have vv := lo v vh
        rw [show (2:ℕ).choose 2=1 by decide] at limit; omega
      exact mem_sdiff.mpr ⟨wh,fun h => (mem_insert.mp h).elim (fun eq => G.not_mem_neighborFinset_self _ (eq ▸ wn)) (fun sm => (not_lt_of_ge sw) (mem_filter.mp sm).2)⟩
    have count := card_le_card sub
    rw [card_sdiff inc,hs,card_insert_of_not_mem off] at count
    have lc : L.card=r v := rfl
    have dense := JointDense.dense_neighbor_bound G v
    change G.degree v≤U.card+_ at dense
    have lower := lr vh
    have small := rk vh
    rw [lc] at count; omega
  let K := X.powersetCard 11
  let bill := fun v => (K.filter (fun s => v∈FiniteRange.bad G X s)).card
  let act := fun v => (K.filter (fun s => v∈activated G X s)).card
  let ext := fun v => (K.filter (fun s => v∈TwoEars.extra G X E s)).card
  have each (v : V) (vh : v∈X) :
      bill v+(if v∈A then augmented (r v) (G.degree v) else 0)≤row (r v)+act v+ext v := by
    let d := min (G.degree v) 10
    have dg : d≤G.degree v := min_le_left ..
    have dl : d≤10 := min_le_right ..
    have dh : d=10 ∨ d=G.degree v := by dsimp [d]; omega
    have low := lr vh
    have top := rk vh
    have cap := Repair.triangles_le_choose G v
    have dc : r v+2≤d.choose 2 ∨ d=10 := dh.elim (fun h => Or.inr h)
      (fun h => Or.inl (by rw [h,Nat.add_comm]; exact low.trans cap))
    have tab := table ⟨r v,top⟩ ⟨d,by omega⟩ (le_min (mem_filter.mp vh).2 (by decide)) dc
      (dh.imp_right (fun eq => eq ▸ fit vh))
    dsimp only at tab
    have saved (hit : Bool) (ok : hit=false → v∉A) : refund hit (r v) d≤act v+ext v := by
      unfold refund
      split
      · rename_i first
        obtain ⟨zero,three⟩ := first
        cases hit with
        | true => exact Nat.zero_le _
        | false =>
          have free : nbr G v E=0 := card_eq_zero.mpr (eq_empty_iff_forall_not_mem.mpr (by
            intro i im; obtain ⟨em,vi⟩ := mem_filter.mp im
            exact ok rfl (mem_biUnion.mpr ⟨i,em,(G.mem_neighborFinset ..).mpr vi.symm⟩)))
          have dd : G.degree v=3 := by rcases dh with h|h <;> omega
          rw [dd,show (3:ℕ).choose 2=3 by decide] at cap
          by_cases sc : trianglesAt G v=2
          · exact (cubic29 G X E hs vh sc dd free).trans (Nat.le_add_left ..)
          · have sat : saturated G v := by unfold saturated; rw [dd,show (3:ℕ).choose 2=3 by decide]; omega
            have ac := SparsePairs.active29 G X hs vh sat 10 3 (by omega) (by decide)
            exact (show 1562275≤(28:ℕ).choose 10-FiniteRange.badCount 29 10 3 by simp only [FiniteRange.badCount,Nat.choose_eq_fast_choose]; decide).trans (ac.trans (Nat.le_add_right ..))
      · split
        · rename_i eq
          have dd : d=G.degree v := dh.resolve_left (fun ten => by rw [ten,show (10:ℕ).choose 2=45 by decide] at eq; omega)
          have sat : saturated G v := by unfold saturated; rw [←dd] at cap ⊢; omega
          exact (SparsePairs.active29 G X hs vh sat 10 d dg (by omega)).trans (Nat.le_add_right ..)
        · exact Nat.zero_le _
    by_cases hit : v∈A
    · obtain ⟨e,he,ev⟩ := mem_biUnion.mp hit
      have b := EarCredit.credited G (W:=X) vh (fun eh => (mem_sdiff.mp he).2 eh) ((G.mem_neighborFinset ..).mp ev).symm 11
      rw [show X.card=29 from hs] at b
      have h := b.trans (Nat.choose_le_choose 11 (show 29-G.degree v≤29-d by omega))
      change bill v≤_ at h
      have sv := saved true (by simp)
      have same : augmented (r v) (G.degree v)=augmented (r v) d := by
        unfold augmented; have iff : 4≤G.degree v ↔ 4≤d := by dsimp [d]; omega
        have cutoff : min d 10=d := min_eq_left dl
        rw [cutoff]
        change max _ (row (r v)-(29-d).choose 11)=_
        by_cases four : 4≤G.degree v
        · simp [four,iff.mp four]
        · have small : ¬4≤d := fun h => four (iff.mpr h)
          simp [four,small]
      rw [if_pos hit,same]; omega
    · have h := FiniteRange.count_bad G X 11 d v vh dg (by change d<(high G).card; omega)
      rw [show X.card=29 from hs] at h
      have sv := saved false (fun _ => hit)
      change bill v≤_ at h
      rw [if_neg hit]; omega
  have sum := sum_le_sum (s:=X) each
  have pay : (∑ v∈X,if v∈A then augmented (r v) (G.degree v) else 0)=∑ v∈A,augmented (r v) (G.degree v) := by
    rw [←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr aa]
  have total := sum_by_rank X (trianglesAt G) inj row
  rw [show X.card=29 from hs,show (∑ i∈range 29,row i)=125572520 by decide] at total
  change (∑ v∈X,row (r v))=_ at total
  simp only [sum_add_distrib,pay,total] at sum
  rw [bound,t] at failure
  change bonus+3*(29:ℕ).choose 11+(∑ e∈E,(29-nbr G e X).choose (11-nbr G e X))+
    (∑ v∈X,act v)+(∑ v∈X,ext v)≤∑ v∈X,bill v at mass
  have inc (e : V) (em : e∈E) : nbr G e X=2 := by
    have ne := TwoEars.high_anchors G t q (by rw [bound,t]; omega) (sed e em)
    have eq : X.filter (G.Adj e)=G.neighborFinset e := by
      ext v; simp only [mem_filter,mem_neighborFinset]; exact ⟨And.right,fun ev => ⟨ne ((G.mem_neighborFinset ..).mpr ev),ev⟩⟩
    unfold nbr; rw [eq,card_neighborFinset_eq_degree,sed e em]
  rw [sum_congr rfl (fun e em => show (29-nbr G e X).choose (11-nbr G e X)=4686825 by rw [inc e em]; decide),
    sum_const,show E.card=2 from es,smul_eq_mul,show (29:ℕ).choose 11=34597290 by rw [Nat.choose_eq_fast_choose]; decide] at mass
  change bonus+3*34597290+2*4686825+(∑ v∈X,act v)+(∑ v∈X,ext v)≤∑ v∈X,bill v at mass
  omega

theorem base_mass (t : (types G).card=31) (q : (nonleaves G).card=31) (bad : bound G<gamma G) :
    massBound G 0 := by
  classical
  let X := high G
  let E := LowSample.twos G
  have sep : Disjoint X E := disjoint_left.mpr (fun _ h e => (mem_sdiff.mp e).2 h)
  have sed (e : V) (he : e∈E) : G.degree e=2 := by
    obtain ⟨m,off⟩ := mem_sdiff.mp he
    have lower := (mem_filter.mp m).2
    by_contra h; exact off (mem_filter.mpr ⟨mem_univ _,by omega⟩)
  have ind : ∀u∈E,∀v∈E,¬G.Adj u v := by
    intro u um v vm uv
    exact (mem_sdiff.mp vm).2 (TwoEars.high_anchors G t q bad (sed u um) ((G.mem_neighborFinset ..).mpr uv))
  obtain ⟨hs,_⟩ := TwoEars.profile G t q bad
  obtain ⟨inj,_,_,_⟩ := Repair.maximal_diversity G (by omega)
  rw [bound,t] at bad
  simpa only [massBound,Nat.zero_add] using extra_mass G X E hs sep ind sed Subset.rfl inj (by omega)

theorem anchor_budget (t : (types G).card=31) (q : (nonleaves G).card=31)
    (failure : bound G<gamma G) :
    let X := high G
    let A := (LowSample.twos G).biUnion (G.neighborFinset ·)
    (∑ a∈A, credit (rank X (trianglesAt G) a))≤12407000 := by
  have total := rank_account G t q failure 0 (base_mass G t q failure)
  dsimp only at total ⊢
  simp only [Nat.zero_add] at total
  exact (sum_le_sum (fun a _ => credit_le_augmented (rank (high G) (trianglesAt G) a) (G.degree a))).trans total

end Graffiti384b.SparsePairs
#print axioms Graffiti384b.SparsePairs.credit_le_augmented
#print axioms Graffiti384b.SparsePairs.degree_discount
#print axioms Graffiti384b.SparsePairs.rank_account
#print axioms Graffiti384b.SparsePairs.base_mass
#print axioms Graffiti384b.SparsePairs.anchor_budget
