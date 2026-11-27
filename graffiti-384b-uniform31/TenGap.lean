import SparseFrontier
namespace Graffiti384b.TenPins
open Finset SimpleGraph JointRank SparsePairs
open private SparsePairs.score_credit from SparseFrontier
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Anchor and ear data supplied by the 31/31 failure profile. -/
structure AnchorData (A : Finset V) : Prop where
  highPins : A⊆high G
  four : A.card=4
  ears : ∀u∈LowSample.twos G,G.neighborFinset u⊆A
  owns : ∀a∈A,∃u∈LowSample.twos G,G.Adj a u
  singleEar : ∀a∈A,nbr G a (LowSample.twos G)≤1
  sparsePin : ∃p∈A,nbr G p A≤1
  rowSize : ∀a∈A,nbr G a (high G\A)≤14
  unionPins : (LowSample.twos G).biUnion (G.neighborFinset ·)=A

theorem anchor_data (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2) :
    AnchorData G (G.neighborFinset e∪G.neighborFinset f) := by
  classical
  let A := G.neighborFinset e∪G.neighborFinset f
  let X := high G\A
  let H := X.filter (fun v => 0<nbr G v A)
  let m := H.card
  let E := LowSample.twos G
  obtain ⟨dis,ah,ac,_,mc,_,_⟩ := AnchorPairs.four_anchor_frontier G t q bad ef de df
  change m≤14 at mc
  change A.card=4 at ac
  have getE {a : V} (d : G.degree a=2) : a∈E := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  obtain ⟨hs,es⟩ := TwoEars.profile G t q bad
  have eq : ({e,f}:Finset V)=E := eq_of_subset_of_card_le (insert_subset (getE de) (singleton_subset_iff.mpr (getE df)))
    (by rw [card_pair ef]; exact es.le)
  have full : E.biUnion (G.neighborFinset ·)=A := by rw [←eq]; simp [A]
  have own (v : V) (vm : v∈A) : ∃ i∈E,G.Adj v i := by
    obtain ⟨i,im,iv⟩ := mem_biUnion.mp (full.symm ▸ vm)
    exact ⟨i,im,((G.mem_neighborFinset ..).mp iv).symm⟩
  have into (a : V) (aa : a∈A) : X.filter (G.Adj a)⊆H := by
    intro i im; obtain ⟨ix,ai⟩ := mem_filter.mp im
    exact mem_filter.mpr ⟨ix,card_pos.mpr ⟨a,mem_filter.mpr ⟨aa,ai.symm⟩⟩⟩
  have misses {s u a : V} (ds : G.degree s=2) (as' : a∈G.neighborFinset s)
      (no : ∀ b∈G.neighborFinset u,¬G.Adj a b) :
      nbr G a (G.neighborFinset s∪G.neighborFinset u)≤1 := by
    have inc : (G.neighborFinset s∪G.neighborFinset u).filter (G.Adj a)⊆(G.neighborFinset s).erase a := by
      intro i im; obtain ⟨ins,ai⟩ := mem_filter.mp im
      exact mem_erase.mpr ⟨ai.ne.symm,(mem_union.mp ins).resolve_right (fun m => no i m ai)⟩
    have z := card_le_card inc; rwa [card_erase_of_mem as',card_neighborFinset_eq_degree,ds] at z
  have existsP : ∃ p∈A,nbr G p A≤1 := by
    rcases AnchorPairs.missing_cross G t q bad ef de df with ⟨a,am,no⟩|⟨a,am,no⟩
    · exact ⟨a,mem_union_left _ am,misses de am no⟩
    · refine ⟨a,mem_union_right _ am,?_⟩
      simpa only [A,union_comm (G.neighborFinset e)] using misses df am no
  have low (a : V) (_aa : a∈A) : nbr G a E≤1 := by
    have avoid : ¬G.Adj a e ∨ ¬G.Adj a f := by
      by_cases ae : G.Adj a e
      · exact Or.inr (fun af => disjoint_left.mp dis ((G.mem_neighborFinset ..).mpr ae.symm) ((G.mem_neighborFinset ..).mpr af.symm))
      · exact Or.inl ae
    rw [←eq]; rcases avoid with h|h <;> simp [nbr,filter_insert,filter_singleton,h,ef] <;> split <;> simp
  exact ⟨ah,ac,fun u um z zm => (show z∈A from full ▸ mem_biUnion.mpr ⟨u,um,zm⟩),own,low,existsP,
    fun a aa => (card_le_card (into a aa)).trans mc,full⟩

/-- Every other anchor scores at least ten if the selected anchor has only
private exterior neighbors inducing maximum degree one. -/
theorem secondary_gap (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) {e f w : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2)
    (wa : w∈G.neighborFinset e∪G.neighborFinset f) :
    let A := G.neighborFinset e∪G.neighborFinset f
    let X := high G\A
    (∀ i∈X,G.Adj w i → nbr G i A=1) →
    (∀ i∈X.filter (G.Adj w),nbr G i (X.filter (G.Adj w))≤1) →
    ∀ a∈A,a≠w → 10≤trianglesAt G a := by
  classical
  let A := G.neighborFinset e∪G.neighborFinset f
  let X := high G\A
  let E := LowSample.twos G
  let r := rank (high G) (trianglesAt G)
  let k := fun a => nbr G a X
  let c := fun a => credit (r a)
  dsimp only
  intro privateRow matchingRow
  change ∀ a∈A,a≠w → 10≤trianglesAt G a
  have data := anchor_data G t q bad ef de df
  have ah := data.highPins; have ac : A.card=4 := data.four
  have full : E.biUnion (G.neighborFinset ·)=A := data.unionPins
  have own := data.owns; have low := data.singleEar; have existsP := data.sparsePin
  have wx : k w≤14 := data.rowSize w wa
  obtain ⟨hs,_⟩ := TwoEars.profile G t q bad
  have wcap (p : V) (pa : p∈A) (pd : nbr G p A≤1) :
      trianglesAt G w≤1+(if w=p then 0 else 1)+k w/2 := by
    have mix : ∀ i∈high G\A,∀ j∈A,G.Adj w i → G.Adj w j → ¬G.Adj i j := by
      intro i ix j ja wi wj ij; have h := privateRow i ix wi
      have z := PinnedColor34.two G wj.ne wi.symm ij wa ja; change 2≤nbr G i A at z; change nbr G i A=1 at h; omega
    simpa [k,X] using link_budget G A ac wa pa pd (low w wa) false true (fun _ => matchingRow) (fun _ => mix)
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by omega)
  have ranks (a : V) (aa : a∈A) : r a<29 ∧ 2+r a≤trianglesAt G a := by
    have h := mem_image_of_mem (rank (high G) (trianglesAt G)) (ah aa)
    rw [rank_range _ _ inj,hs,mem_range] at h
    exact ⟨h,rank_lower _ _ inj 2 floor (ah aa)⟩
  obtain ⟨p,pa,pd⟩ := existsP
  have wd := wcap p pa pd
  have wr := ranks w wa
  have wlim : trianglesAt G w≤2+k w/2 := by split at wd <;> omega
  have weighted (L : ℕ) (hc : L≤augmented (r w) (G.degree w)) : L+(∑a∈A.erase w,c a)≤12407000 := by
    let val := fun a => augmented (r a) (G.degree a)
    have tot := rank_account G t q bad 0 (base_mass G t q bad)
    change 0+(∑a∈E.biUnion (G.neighborFinset ·),val a)≤12407000 at tot; rw [full] at tot
    have le := sum_le_sum (s:=A.erase w) (fun a _ => credit_le_augmented (r a) (G.degree a))
    change (∑a∈A.erase w,c a)≤∑a∈A.erase w,val a at le
    have split := sum_erase_add A val wa; change L≤val w at hc
    omega
  have degree : 1+k w+nbr G w A≤G.degree w := by
    obtain ⟨u,um,wu⟩ := own w wa
    let R := X.filter (G.Adj w)
    let I := A.filter (G.Adj w)
    have dj : Disjoint R I := disjoint_left.mpr (fun i im ia => (mem_sdiff.mp (mem_filter.mp im).1).2 (mem_filter.mp ia).1)
    have uh : u∉high G := (mem_sdiff.mp um).2
    have off : u∉R∪I := fun ui => (mem_union.mp ui).elim
      (fun ur => uh (mem_sdiff.mp (mem_filter.mp ur).1).1) (fun ua => uh (ah (mem_filter.mp ua).1))
    have inc : insert u (R∪I)⊆G.neighborFinset w := insert_subset ((G.mem_neighborFinset ..).mpr wu)
      (union_subset (fun _ im => (G.mem_neighborFinset ..).mpr (mem_filter.mp im).2)
        (fun _ im => (G.mem_neighborFinset ..).mpr (mem_filter.mp im).2))
    have z := card_le_card inc
    rw [card_insert_of_not_mem off,card_union_of_disjoint dj,card_neighborFinset_eq_degree] at z
    change k w+nbr G w A+1≤_ at z; omega
  let S := A.erase w
  have cap : 6904448+(∑a∈S,c a)≤12407000 := by
    by_cases sc : trianglesAt G w=2
    · obtain ⟨u,um,wu⟩ := own w wa
      have z := two_score_budget G t q bad um wu.symm sc
      change 3124550+(∑a∈E.biUnion (G.neighborFinset ·),c a)≤12407000 at z
      rw [full] at z
      have zero : r w=0 := by omega
      have cost : c w=4975245 := by simp [c,zero,credit]
      have split := sum_erase_add A c wa; change (∑a∈S,c a)+c w=_ at split; omega
    · by_cases small : k w≤7
      · have five : 5≤G.degree w := by
          by_cases three : k w≤3
          · have two : 2≤nbr G w A := by
              apply Nat.le_of_not_gt; intro few
              have h := wcap w wa (by omega)
              rw [if_pos rfl] at h; omega
            omega
          · omega
        have z := weighted _ (degree_discount.2.1 (by omega) five)
        change 7845024+(∑a∈S,c a)≤12407000 at z; omega
      · exact weighted _ (degree_discount.2.2 (by omega) (by omega))
  have sz : S.card=3 := by dsimp [S]; rw [card_erase_of_mem wa,ac]
  intro a aa aw
  apply Nat.le_of_not_gt; intro small
  have aS : a∈S := mem_erase.mpr ⟨aw,aa⟩
  have rt := ranks a aa
  have ca := (SparsePairs.score_credit ⟨r a,rt.1⟩).2.1 (by dsimp only; omega)
  change 4576264≤c a at ca
  have tab : ∀ j : Fin 29,739024≤credit j := by unfold credit; decide
  have sum : (∑_i∈S.erase a,739024)≤∑i∈S.erase a,c i := sum_le_sum (fun i im => tab ⟨r i,(ranks i (mem_erase.mp (mem_erase.mp im).2).2).1⟩)
  change (∑_i∈S.erase a,739024)≤∑i∈S.erase a,c i at sum
  rw [sum_const,card_erase_of_mem aS,sz,smul_eq_mul] at sum
  have split := sum_erase_add S c aS; omega
end Graffiti384b.TenPins
#print axioms Graffiti384b.TenPins.anchor_data
#print axioms Graffiti384b.TenPins.secondary_gap
