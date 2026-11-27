import FourFront
namespace Graffiti384b.Four29
open Finset SimpleGraph Donor JointRank
open private Four29.inside Four29.outside from DenseFour
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
/-- Four reserved, low-scoring anchors create four holes in the ranks
of the remaining high vertices past their common score cap. -/
private theorem rank_gap {X W H : Finset V} (score : V→ℕ) (inj : Set.InjOn score (H:Set V))
    (rich : ∀w∈H,2≤score w) (xh : X⊆H) (wh : W⊆H) (dis : Disjoint X W)
    (ws : W.card=4) (cap : ℕ) (bounded : ∀w∈W,score w≤cap)
    {v : V} (vm : v∈X) (threshold : cap≤rank X score v+5) : rank X score v+6≤score v := by
  classical
  let L := X.filter (fun z => score z<score v)
  have lh : L⊆H := (filter_subset ..).trans xh
  have vl : v∉L := fun m => (lt_irrefl _) (mem_filter.mp m).2
  have d : Disjoint (insert v L) W := dis.mono_left (insert_subset vm (filter_subset ..))
  have lower := JointRank.rank_lower H score inj 2 rich (xh vm)
  have large : cap<score v := by
    by_contra! small
    have image : ((insert v L ∪ W).image score)⊆Icc 2 cap := by
      intro z zm
      obtain ⟨x,xm,rfl⟩ := mem_image.mp zm
      rcases mem_union.mp xm with xl|xw
      · rcases mem_insert.mp xl with rfl|xl
        · exact mem_Icc.mpr ⟨rich _ (xh vm),small⟩
        · exact mem_Icc.mpr ⟨rich _ (lh xl),((mem_filter.mp xl).2.le.trans small)⟩
      · exact mem_Icc.mpr ⟨rich _ (wh xw),bounded _ xw⟩
    have ct := card_le_card image
    rw [card_image_of_injOn (inj.mono (union_subset (insert_subset (xh vm) lh) wh)),
      card_union_of_disjoint d,card_insert_of_not_mem vl,ws,Nat.card_Icc] at ct
    change cap≤L.card+5 at threshold
    omega
  have sub : L∪W⊆H.filter (fun z => score z<score v) := by
    intro x xm
    rcases mem_union.mp xm with xl|xw
    · exact mem_filter.mpr ⟨lh xl,(mem_filter.mp xl).2⟩
    · exact mem_filter.mpr ⟨wh xw,(bounded _ xw).trans_lt large⟩
  have ct := card_le_card sub
  rw [card_union_of_disjoint (dis.mono_left (filter_subset ..)),ws] at ct
  change L.card+4≤rank H score v at ct
  change L.card+6≤score v
  omega


/-- Every reserved global rank subtracts its own row from the sum of
twenty-seven possible repairs. The formula applies with arbitrary prices. -/
theorem four_missing_rows (t : (types G).card=29) (h : (high G).card=27)
    (q : (nonleaves G).card=29) (bad : bound G<gamma G) {e f : V}
    (de : G.degree e=2) (df : G.degree f=2) (ne : e≠f) (p z : ℕ) :
    let X := pool G e f
    let W := roots G e f
    let r := rank (high G) (trianglesAt G)
    3*(23:ℕ).choose 8+(exposed G X).card*p+(twice G X).card*z+(∑w∈W,cost (r w) p z) ≤
      ∑i∈range 27,cost i p z := by
  classical
  dsimp only
  let H := high G
  let X := pool G e f
  let W := roots G e f
  let r := rank H (trianglesAt G)
  have D := data_of_failure G t h q bad de df ne
  have fail : Fintype.card V-15<gamma G := by simpa only [bound,t] using bad
  have rankLo (v : V) (vm : v∈X) : r v<27 ∧ 2+r v≤trianglesAt G v := by
    have vh : v∈H := (mem_sdiff.mp vm).1
    refine ⟨mem_range.mp ?_,rank_lower H (trianglesAt G) D.scoreInj 2 D.rich vh⟩
    rw [←h,←rank_range (high G) (trianglesAt G) D.scoreInj]; exact mem_image_of_mem _ vh
  have budget := repair_budget G D.trial D.poolSize (card_pair ne) fail r p z rankLo
  have add := sum_sdiff D.highRoots (f:=fun v => cost (r v) p z)
  have ord := sum_by_rank H (trianglesAt G) D.scoreInj (fun i => cost i p z)
  rw [show H.card=27 from h] at ord
  change (∑v∈X,cost (r v) p z)+(∑v∈W,cost (r v) p z)=∑v∈H,cost (r v) p z at add
  change _≤∑i∈range 27,cost i p z
  exact (Nat.add_le_add_right budget _).trans_eq (add.trans ord)

private def adjust (s i : ℕ) := if s ≤ i + 5 then i + 4 else i
private def levels : List (ℕ×ℕ×ℕ) := [(0,5,0),(4,6,24024),(6,7,24024),(9,8,38610),
  (10,9,38610),(11,10,38610),(12,11,38610),(13,12,38610),(14,15,57200)]

private theorem level_ok : ∀z∈levels,(∑i∈range 23,cost (adjust z.2.1 i) z.2.2 0) <
    3*(23:ℕ).choose 8+z.1*z.2.2 := by
  unfold levels cost adjust Four29.inside Four29.outside
  simp only [Nat.choose_eq_fast_choose]
  decide

/-- If all four reserved scores are bounded by s, four ranks must be
skipped past s. The exposure/score pairs checked here include (6,7),
(12,11), and (14,15). -/
theorem low_anchor_scores (t : (types G).card=29) (h : (high G).card=27)
    (q : (nonleaves G).card=29) {e f : V} (de : G.degree e=2) (df : G.degree f=2) (ne : e≠f)
    (m s : ℕ) (level : (m,s)∈([(0,5),(4,6),(6,7),(9,8),(10,9),(11,10),(12,11),(13,12),(14,15)] : List (ℕ×ℕ)))
    (exposure : m≤(exposed G (pool G e f)).card) (cap : ∀w∈roots G e f,trianglesAt G w≤s) :
    gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt; intro bad
  have D := data_of_failure G t h q bad de df ne
  have fail : Fintype.card V-15<gamma G := by simpa only [bound,t] using bad
  let X := pool G e f
  let r := rank X (trianglesAt G)
  have lookup : levels.map (fun p => (p.1,p.2.1))=[(0,5),(4,6),(6,7),(9,8),(10,9),(11,10),(12,11),(13,12),(14,15)] := rfl
  rw [←lookup] at level
  obtain ⟨⟨m',s',p⟩,index,eq⟩ := List.mem_map.mp level
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
  have admiss (v : V) (vm : v∈X) : adjust s' (r v)<27 ∧ 2+adjust s' (r v)≤trianglesAt G v := by
    have ri : r v<23 := mem_range.mp (by rw [←D.poolSize,←rank_range X (trianglesAt G) D.trial.distinct]; exact mem_image_of_mem _ vm)
    have base := rank_lower X (trianglesAt G) D.trial.distinct 2 D.trial.rich vm
    unfold adjust
    split
    · rename_i jump
      have full := rank_gap (trianglesAt G) D.scoreInj D.rich (show X⊆high G from sdiff_subset) D.highRoots
        (disjoint_left.mpr (fun _ vx => (mem_sdiff.mp vx).2)) D.rootsSize s' cap vm jump
      change r v+6≤trianglesAt G v at full
      omega
    · exact ⟨by omega,base⟩
  have budget := repair_budget G D.trial D.poolSize (card_pair ne) fail (fun v => adjust s' (r v)) p 0 admiss
  rw [sum_by_rank X (trianglesAt G) D.trial.distinct (fun i => cost (adjust s' i) p 0),D.poolSize] at budget
  have paid := level_ok _ index
  change (∑i∈range 23,cost (adjust s' i) p 0)<3*(23:ℕ).choose 8+m'*p at paid
  have fee := Nat.mul_le_mul_right p exposure
  change m'*p≤(exposed G (pool G e f)).card*p at fee
  omega
/-- Regression for the rank estimate. With the last four global ranks
reserved, assign one exterior contact to ranks 15 through 22 and zero to
the other retained ranks. Even optimizing either price cannot close this row. -/
theorem eight_contact_gap (p z : ℕ) :
    3*(23:ℕ).choose 8+8*p+359828 ≤ ∑i∈range 23,cost i p z := by
  let charge (i : ℕ) := if i<15 then Four29.inside i else Four29.outside i+p
  have bound : (∑i∈range 23,charge i)≤∑i∈range 23,cost i p z := by
    apply sum_le_sum; intro i _
    unfold charge cost
    split
    · exact le_max_left ..
    · exact (le_max_left ..).trans (le_max_right ..)
  have exactCount : (∑i∈range 23,charge i)=1830770+8*p := by
    simp [sum_range_succ,charge,Four29.inside,Four29.outside]
    omega
  rw [exactCount] at bound
  rw [show (23:ℕ).choose 8=490314 by decide]
  omega
end Graffiti384b.Four29
#print axioms Graffiti384b.Four29.eight_contact_gap
#print axioms Graffiti384b.Four29.four_missing_rows
#print axioms Graffiti384b.Four29.low_anchor_scores
