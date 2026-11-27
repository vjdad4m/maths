import FinishEight
namespace Graffiti384b.NinePins
open Finset SimpleGraph JointRank SparsePairs
open private SparsePairs.score_credit from SparseFrontier
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A private anchor row of size four through seven and maximum internal
degree one leaves at least six exterior contacts for the other anchors. -/
theorem six_beyond_matching (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) {e f w : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2)
    (wa : w∈G.neighborFinset e∪G.neighborFinset f) :
    let A := G.neighborFinset e∪G.neighborFinset f
    let X := high G\A
    (∀ i∈X,G.Adj w i → nbr G i A=1) →
    (∀ i∈X.filter (G.Adj w),nbr G i (X.filter (G.Adj w))≤1) →
    4≤nbr G w X → nbr G w X≤7 →
    nbr G w X+6≤(X.filter (fun z => 0<nbr G z A)).card := by
  classical
  let A := G.neighborFinset e∪G.neighborFinset f
  let X := high G\A
  let H := X.filter (fun v => 0<nbr G v A)
  let m := H.card
  let E := LowSample.twos G
  let r := rank (high G) (trianglesAt G)
  let k := fun a => nbr G a X
  let c := fun a => credit (r a)
  change (∀ i∈X,G.Adj w i → nbr G i A=1) → (∀ i∈X.filter (G.Adj w),nbr G i (X.filter (G.Adj w))≤1) → 4≤k w → k w≤7 → k w+6≤m
  intro privateRow matchingRow lower upper
  obtain ⟨dis,ah,ac,_,_,_,_⟩ := AnchorPairs.four_anchor_frontier G t q bad ef de df
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
  have share (a : V) (aa : a∈A) (aw : a≠w) : k a+k w≤m := by
    have dj : Disjoint (X.filter (G.Adj a)) (X.filter (G.Adj w)) := disjoint_left.mpr (by
      intro i ai wi
      have ct := PinnedColor34.two G aw (mem_filter.mp ai).2.symm (mem_filter.mp wi).2.symm aa wa
      have one := privateRow i (mem_filter.mp wi).1 (mem_filter.mp wi).2; omega)
    have h := card_le_card (union_subset (into a aa) (into w wa))
    rwa [card_union_of_disjoint dj] at h
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
  have wcap (p : V) (pa : p∈A) (pd : nbr G p A≤1) :
      trianglesAt G w≤1+(if w=p then 0 else 1)+k w/2 := by
    have mix : ∀ i∈high G\A,∀ j∈A,G.Adj w i → G.Adj w j → ¬G.Adj i j := by
      intro i ix j ja wi wj ij; have h := privateRow i ix wi
      have z := PinnedColor34.two G wj.ne wi.symm ij wa ja; change 2≤nbr G i A at z; omega
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
  have reduced (a : V) (aa : a∈A) (aw : a≠w) :
      trianglesAt G a≤2+(k a).choose 2+k a*2 := by
    have allowed : ∀ i∈high G\A,∀ j∈A,G.Adj a i → G.Adj a j → G.Adj i j → j∈A.erase w := by
      intro i ix j ja ai _ ij; apply mem_erase.mpr; refine ⟨?_,ja⟩
      rintro rfl; have one := privateRow i ix ij.symm
      have two := PinnedColor34.two G aw ai.symm ij aa wa; omega
    have ct := link_local G A (A.erase w) ac aa pa pd (low a aa) true false (by simp) allowed (by simp)
    have ae : a∈A.erase w := mem_erase.mpr ⟨aw,aa⟩
    have inc : (A.erase w).filter (G.Adj a)⊆(A.erase w).erase a :=
      fun v im => mem_erase.mpr ⟨(mem_filter.mp im).2.ne.symm,(mem_filter.mp im).1⟩
    have z := card_le_card inc
    rw [card_erase_of_mem ae,card_erase_of_mem wa,ac] at z
    change nbr G a (A.erase w)≤2 at z
    have prod := Nat.mul_le_mul_left (k a) z
    simp only [if_true,Bool.false_eq_true,if_false] at ct
    change trianglesAt G a≤1+(if a=p then 0 else 1)+(k a).choose 2+k a*nbr G a (A.erase w) at ct
    split at ct <;> omega
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
  have paid := weighted 7845024 (degree_discount.2.1 (by omega) (by omega))
  apply Nat.le_of_not_gt
  intro neg
  let S := A.erase w
  have sz : S.card=3 := by dsimp [S]; rw [card_erase_of_mem wa,ac]
  have cap' (a : V) (am : a∈S) : trianglesAt G a≤22 := by
    obtain ⟨aw,aa⟩ := mem_erase.mp am
    have lim : k a≤5 := by have z := share a aa aw; omega
    have ck := Nat.choose_le_choose 2 lim
    rw [show (5:ℕ).choose 2=10 by decide] at ck
    have h := reduced a aa aw; omega
  have cheap : ∃ a∈S,trianglesAt G a≤20 := by
    apply Classical.byContradiction; intro no
    have sub : S.image (trianglesAt G)⊆{21,22} := by
      intro z zm; obtain ⟨a,am,rfl⟩ := mem_image.mp zm
      have lo : ¬trianglesAt G a≤20 := fun h => no ⟨a,am,h⟩
      have hi := cap' a am; simp only [mem_insert,mem_singleton]; omega
    have x := card_le_card sub
    have si : Set.InjOn (trianglesAt G) (S:Set V) := inj.mono (fun _ am => ah (mem_erase.mp am).2)
    rw [card_image_of_injOn si,sz,card_pair (by decide : (21:ℕ)≠22)] at x; omega
  obtain ⟨a,am,asc⟩ := cheap
  have rt := ranks a (mem_erase.mp am).2
  have ca  := (SparsePairs.score_credit ⟨r a,rt.1⟩).2.2.2 (by dsimp only; omega)
  change 2116296≤c a at ca
  have pays (i : V) (im : i∈S.erase a) : 1293292≤c i := by
    have is := (mem_erase.mp im).2; have h := cap' i is
    have ir := ranks i (mem_erase.mp is).2
    have tab : ∀ h : Fin 29,h.val≤20 → 1293292≤credit h := by unfold credit; decide
    exact tab ⟨r i,ir.1⟩ (by dsimp only; omega)
  have sum := sum_le_sum pays; rw [sum_const,card_erase_of_mem am,sz,smul_eq_mul] at sum
  have split := sum_erase_add S c am
  change 7845024+(∑a∈S,c a)≤12407000 at paid
  omega

end Graffiti384b.NinePins
#print axioms Graffiti384b.NinePins.six_beyond_matching
