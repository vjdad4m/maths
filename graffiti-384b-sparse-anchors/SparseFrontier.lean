import SparseCubic
import PrivateContacts
namespace Graffiti384b.SparsePairs
open Finset SimpleGraph JointRank
open private LowSample.two_degree from LowSample384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem score_credit : ∀ r : Fin 29,
    (r.val≤3 → 4975245≤credit r) ∧ (r.val≤7 → 4576264≤credit r) ∧
    (r.val≤12 → 3233230≤credit r) ∧ (r.val≤18 → 2116296≤credit r) := by
  unfold credit; decide

/-- An anchor from the matching-neighborhood theorem owns only private
exterior contacts. At least eight exterior vertices touch an anchor; at most three private
contacts force at least six further contacts outside that row. -/
theorem sparse_frontier (t : (types G).card=31) (q : (nonleaves G).card=31)
    (bad : bound G<gamma G) {e f : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2) :
    let A := G.neighborFinset e∪G.neighborFinset f
    let X := high G\A
    let m := (X.filter (fun v => 0<nbr G v A)).card
    8≤m ∧ ∃ w∈A,
      (∀ i∈X,G.Adj w i → nbr G i A=1) ∧
      (∀ i∈X.filter (G.Adj w),nbr G i (X.filter (G.Adj w))≤1) ∧
      nbr G w X+5≤m ∧
      (nbr G w X≤1 → nbr G w X+10≤m) ∧
      (nbr G w X≤3 → nbr G w X+6≤m) ∧ (nbr G w X≤3 → m<nbr G w X+10 →
        (¬∃ i∈A,∃j∈A,G.Adj w i ∧ G.Adj w j ∧ G.Adj i j) ∧ trianglesAt G w≤1+nbr G w X/2) ∧
      (m=8 → nbr G w X=2 ∧ trianglesAt G w=2) := by
  classical
  let A := G.neighborFinset e∪G.neighborFinset f
  let X := high G\A
  let H := X.filter (fun v => 0<nbr G v A)
  let m := H.card
  let E := LowSample.twos G
  let r := rank (high G) (trianglesAt G)
  let k := fun a => nbr G a X
  let c := fun a => credit (r a)
  change 8≤m ∧ ∃ w∈A, _ 
  obtain ⟨dis,ah,ac,_,mc,_,_⟩ := AnchorPairs.four_anchor_frontier G t q bad ef de df
  change m≤14 at mc
  change A.card=4 at ac
  have getE {a : V} (d : G.degree a=2) : a∈E := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨mem_univ _,by omega⟩,fun h => by have := (mem_filter.mp h).2; omega⟩
  obtain ⟨hs,es⟩ := TwoEars.profile G t q bad
  have eq : ({e,f}:Finset V)=E := eq_of_subset_of_card_le (insert_subset (getE de) (singleton_subset_iff.mpr (getE df)))
    (by rw [card_pair ef]; exact es.le)
  have full : E.biUnion (G.neighborFinset ·)=A := by rw [←eq]; simp [A]
  have sub (v : V) (vm : v∈E) : G.neighborFinset v⊆A := fun i im => full ▸ mem_biUnion.mpr ⟨v,vm,im⟩
  have own (v : V) (vm : v∈A) : ∃ i∈E,G.Adj v i := by
    obtain ⟨i,im,iv⟩ := mem_biUnion.mp (full.symm ▸ vm)
    exact ⟨i,im,((G.mem_neighborFinset ..).mp iv).symm⟩
  obtain ⟨w,wa,blind,matchingRow⟩ := ForkGuard34.matching G (W:=A) ah sub own (by omega) bad
  have privateRow (i : V) (ix : i∈X) (wi : G.Adj w i) : nbr G i A=1 := by
    have pos := card_pos.mpr (show (A.filter (G.Adj i)).Nonempty from ⟨w,mem_filter.mpr ⟨wa,wi.symm⟩⟩)
    change 0<nbr G i A at pos
    by_contra h; exact blind i (mem_filter.mpr ⟨ix,by omega⟩) wi
  have into (a : V) (aa : a∈A) : X.filter (G.Adj a)⊆H := by
    intro i im; obtain ⟨ix,ai⟩ := mem_filter.mp im
    exact mem_filter.mpr ⟨ix,card_pos.mpr ⟨a,mem_filter.mpr ⟨aa,ai.symm⟩⟩⟩
  have wx : k w≤m := card_le_card (into w wa)
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
  have y (a : V) (aa : a∈A) : nbr G a A≤3 := by
    have sub' : A.filter (G.Adj a)⊆A.erase a := fun i im => mem_erase.mpr ⟨(mem_filter.mp im).2.ne.symm,(mem_filter.mp im).1⟩
    have h := card_le_card sub'; rwa [card_erase_of_mem aa,ac] at h
  have cap (p : V) (pa : p∈A) (pd : nbr G p A≤1) (a : V) (aa : a∈A) :
      trianglesAt G a≤1+(if a=p then 0 else 1)+(k a).choose 2+k a*nbr G a A := by
    simpa [k,X] using link_budget G A ac aa pa pd (low a aa) true false (by simp) (by simp)
  have wcap (p : V) (pa : p∈A) (pd : nbr G p A≤1) :
      trianglesAt G w≤1+(if w=p then 0 else 1)+k w/2 := by
    have mix : ∀ i∈high G\A,∀ j∈A,G.Adj w i → G.Adj w j → ¬G.Adj i j := by
      intro i ix j ja wi wj ij; have h := privateRow i ix wi
      have z := PinnedColor34.two G wj.ne wi.symm ij wa ja; omega
    simpa [k,X] using link_budget G A ac wa pa pd (low w wa) false true (fun _ => matchingRow) (fun _ => mix)
  obtain ⟨inj,floor,_,_⟩ := Repair.maximal_diversity G (by omega)
  have ranks (a : V) (aa : a∈A) : r a<29 ∧ 2+r a≤trianglesAt G a := by
    have h := mem_image_of_mem (rank (high G) (trianglesAt G)) (ah aa)
    rw [rank_range _ _ inj,hs,mem_range] at h
    exact ⟨h,rank_lower _ _ inj 2 floor (ah aa)⟩
  have allPaid := anchor_budget G t q bad
  change (∑ a∈E.biUnion (G.neighborFinset ·),c a)≤12407000 at allPaid
  rw [full] at allPaid
  obtain ⟨p,pa,pd⟩ := existsP
  have wd := wcap p pa pd
  have wr := ranks w wa
  have wlim : trianglesAt G w≤2+k w/2 := by split at wd <;> omega
  have creditW := score_credit ⟨r w,wr.1⟩
  dsimp only at creditW
  change (r w≤3 → 4975245≤c w) ∧ (r w≤7 → 4576264≤c w) ∧ (r w≤12 → 3233230≤c w) ∧ (r w≤18 → 2116296≤c w) at creditW
  have four : k w+4≤m := by
    apply Nat.le_of_not_gt
    intro neg
    have pays (a : V) (am : a∈A.erase w) : 3233230≤c a := by
      obtain ⟨aw,aa⟩ := mem_erase.mp am
      have h := share a aa aw
      have xs : k a≤3 := by omega
      have ki := Nat.choose_le_choose 2 xs
      have prod := Nat.mul_le_mul xs (y a aa)
      have z := cap p pa pd a aa
      rw [show (3:ℕ).choose 2=3 by decide] at ki
      have rt := ranks a aa
      exact (score_credit ⟨r a,rt.1⟩).2.2.1 (by dsimp only; split at z <;> omega)
    have sum := sum_le_sum pays; rw [sum_const,card_erase_of_mem wa,ac,smul_eq_mul] at sum
    have split := sum_erase_add A c wa
    have cw := creditW.2.1 (by omega)
    omega
  have boundary (eq4 : m=k w+4) (small : k w≤7) : (∀ p∈A,nbr G p A≤1 → p=w) ∧ 2≤k w := by
    have uniq (u : V) (ua : u∈A) (ud : nbr G u A≤1) : u=w := by
      apply Classical.byContradiction
      intro ne
      have ul := share u ua ne
      have us : k u≤4 := by omega
      have kuu := Nat.choose_le_choose 2 us
      rw [show (4:ℕ).choose 2=6 by decide] at kuu
      have ub := cap u ua ud u ua
      simp only [ite_self,if_pos,if_true] at ub
      have ur := ranks u ua
      have pu := Nat.mul_le_mul us ud
      have cu := (score_credit ⟨r u,ur.1⟩).2.2.1 (by dsimp only; omega)
      let S := (A.erase w).erase u
      have uw : u∈A.erase w := mem_erase.mpr ⟨ne,ua⟩
      have pays (a : V) (am : a∈S) : 2116296≤c a := by
        obtain ⟨_,am'⟩ := mem_erase.mp am
        obtain ⟨aw,aa⟩ := mem_erase.mp am'
        have z := share a aa aw
        have lim : k a≤4 := by omega
        have ck := Nat.choose_le_choose 2 lim
        rw [show (4:ℕ).choose 2=6 by decide] at ck
        have prod := Nat.mul_le_mul lim (y a aa)
        have cap' := cap u ua ud a aa
        have rt := ranks a aa
        exact (score_credit ⟨r a,rt.1⟩).2.2.2 (by dsimp only; split at cap' <;> omega)
      have sum := sum_le_sum pays
      have sc : S.card=2 := by dsimp [S]; rw [card_erase_of_mem uw,card_erase_of_mem wa,ac]
      rw [sum_const,sc,smul_eq_mul] at sum
      have eq1 := sum_erase_add A c wa
      have eq2 := sum_erase_add (A.erase w) c uw
      change (∑ a∈S,c a)+c u=_ at eq2
      change _≤c u at cu
      have cw := creditW.1 (by omega)
      omega
    have mp := uniq p pa pd
    have cap' := wcap p pa pd
    rw [mp,if_pos rfl] at cap'
    exact ⟨uniq,by omega⟩
  have charged (sc : trianglesAt G w=2) : 3124550+(∑ a∈A,c a)≤12407000 := by
    obtain ⟨u,um,wu⟩ := own w wa
    have b := two_score_budget G t q bad um wu.symm sc
    change 3124550+(∑ a∈E.biUnion (G.neighborFinset ·),c a)≤12407000 at b
    rwa [full] at b
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
  have strong (sm : k w≤3) : 8042111+(∑a∈A.erase w,c a)≤12407000 := by
    by_cases sc : trianglesAt G w=2
    · have paid := charged sc; have split := sum_erase_add A c wa
      have cw := creditW.1 (by omega); omega
    · have ytwo : 2≤nbr G w A := by
        apply Nat.le_of_not_gt; intro neg
        have low := wcap w wa (by omega)
        simp only [if_pos rfl,if_true] at low; omega
      exact weighted _ (degree_discount.1 (by omega) (by omega))
  have fullTriangle (small : k w≤3) (triangle : ∃ i∈A,∃j∈A,G.Adj w i ∧ G.Adj w j ∧ G.Adj i j) : k w+10≤m := by
    have pr (a : V) (aa : a∈A) : 739024≤c a ∧ (trianglesAt G a≤5 → 4975245≤c a) ∧
        (trianglesAt G a≤14 → 3233230≤c a) ∧ (trianglesAt G a≤20 → 2116296≤c a) ∧
        (trianglesAt G a≤23 → 1293292≤c a) := by
      have rt := ranks a aa
      have tab : ∀ h : Fin 29,739024≤credit h ∧ (h.val≤21 → 1293292≤credit h) := by unfold credit; decide
      have z := score_credit ⟨r a,rt.1⟩
      have zz := tab ⟨r a,rt.1⟩
      change 739024≤c a ∧ (r a≤21 → 1293292≤c a) at zz
      change (r a≤3 → 4975245≤c a) ∧ (r a≤7 → 4576264≤c a) ∧ (r a≤12 → 3233230≤c a) ∧
        (r a≤18 → 2116296≤c a) at z
      exact ⟨zz.1,fun h => z.1 (by omega),fun h => z.2.2.1 (by omega),fun h => z.2.2.2 (by omega),
        fun h => zz.2 (by omega)⟩
    rcases mem_union.mp wa with we|wf
    · exact ten_contacts G A t q bad de df ef rfl dis ac ah we privateRow triangle low ⟨p,pa,pd⟩ c pr (strong small)
    · exact ten_contacts G A t q bad df de ef.symm (union_comm ..) dis.symm ac ah wf privateRow triangle low ⟨p,pa,pd⟩ c pr (strong small)
  have noMix : ∀ i∈high G\A,∀j∈A,G.Adj w i → G.Adj w j → ¬G.Adj i j := by
    intro i ix j ja wi wj ij
    have one := privateRow i ix wi
    have two := PinnedColor34.two G wj.ne wi.symm ij wa ja; omega
  have noTriangle (no : ¬∃ i∈A,∃j∈A,G.Adj w i ∧ G.Adj w j ∧ G.Adj i j) :
      trianglesAt G w≤1+k w/2 := by
    have ct := link_with_triangle G A A ac wa pa pd (low w wa) false false true (fun _ => matchingRow)
      (fun _ i ia j ja wi wj ij => no ⟨i,ia,j,ja,wi,wj,ij⟩)
      (fun _ _ _ ha _ _ _ => ha) (fun _ => noMix)
    simpa only [Bool.false_eq_true,if_false,or_true,if_true,Nat.add_zero] using ct
  have ten (small : k w≤1) : k w+10≤m := by
    by_cases tri : ∃ i∈A,∃j∈A,G.Adj w i ∧ G.Adj w j ∧ G.Adj i j
    · exact fullTriangle (by omega) tri
    · have sc := noTriangle tri; omega
  have five : k w+5≤m := by
    apply Nat.le_of_not_gt; intro neg
    have paid : 6904448+(∑a∈A.erase w,c a)≤12407000 := by
      by_cases low : k w≤3
      · have h := strong low; omega
      · by_cases mid : k w≤7
        · have bd := boundary (by omega) mid
          have pw := bd.1 p pa pd
          have mb := wcap p pa pd
          rw [pw,if_pos rfl] at mb
          have h := weighted 7845024 (degree_discount.2.1 (by omega) (by omega)); omega
        · exact weighted _ (degree_discount.2.2 (by omega) (by omega))
    have pays (a : V) (am : a∈A.erase w) : 2116296≤c a := by
      obtain ⟨aw,aa⟩ := mem_erase.mp am
      have lim : k a≤4 := by have z := share a aa aw; omega
      have ck := Nat.choose_le_choose 2 lim
      rw [show (4:ℕ).choose 2=6 by decide] at ck
      have cap' := reduced a aa aw
      have rt := ranks a aa
      exact (score_credit ⟨r a,rt.1⟩).2.2.2 (by dsimp only; omega)
    have sum := sum_le_sum pays; rw [sum_const,card_erase_of_mem wa,ac,smul_eq_mul] at sum
    omega
  have six (sm : k w≤3) : k w+6≤m := by
    apply Nat.le_of_not_gt; intro neg
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
    have ca := (score_credit ⟨r a,rt.1⟩).2.2.2 (by dsimp only; omega)
    change 2116296≤c a at ca
    have pays (i : V) (im : i∈S.erase a) : 1293292≤c i := by
      have is := (mem_erase.mp im).2; have h := cap' i is
      have ir := ranks i (mem_erase.mp is).2
      have tab : ∀ h : Fin 29,h.val≤20 → 1293292≤credit h := by unfold credit; decide
      exact tab ⟨r i,ir.1⟩ (by dsimp only; omega)
    have sum := sum_le_sum pays; rw [sum_const,card_erase_of_mem am,sz,smul_eq_mul] at sum
    have split := sum_erase_add S c am
    have paid := strong sm
    change 8042111+(∑a∈S,c a)≤12407000 at paid
    omega
  have minEight : 8≤m := by
    by_cases small : k w≤1
    · have z := ten small; omega
    · by_cases mid : k w≤3
      · have z := six mid; omega
      · omega
  have lowProfile (sm : k w≤3) (near : m<k w+10) :
      (¬∃ i∈A,∃j∈A,G.Adj w i ∧ G.Adj w j ∧ G.Adj i j) ∧ trianglesAt G w≤1+k w/2 := by
    have no := fun tri => (not_lt_of_ge (fullTriangle sm tri)) near
    exact ⟨no,noTriangle no⟩
  refine ⟨minEight,w,wa,privateRow,matchingRow,five,ten,six,lowProfile,?_⟩
  intro eq8; change m=8 at eq8
  have high : ¬k w≤1 := fun sm => by have h := ten sm; omega
  have z := six (by omega)
  change k w=2 ∧ trianglesAt G w=2
  have sc := (lowProfile (by omega) (by omega)).2
  omega
end Graffiti384b.SparsePairs
#print axioms Graffiti384b.SparsePairs.sparse_frontier
