import HighEarBypass33

namespace Graffiti384b.HighEar
open Finset SimpleGraph OneEar EarFrame33
open private AnchorParity.join AnchorParity.initialPart from ParityAnchor33
open private HighEar.outside_cubic from HighEarPins33
open private Repair.nbr_mono from Repair384b
variable {V : Type*} {G : SimpleGraph V} {e a b : V} {n : ℕ}

/-- Replacing the segment between the first and last visits to a clique
uses one or two edges. Distant contacts strictly shorten an even route. -/
private theorem shorten [DecidableEq V] {C : Finset V} (cl : G.IsClique (C : Set V))
    (size : 3≤C.card) (miss : e∉C) (p : Route G e a b n) {r s : ℕ} (gap : r+2<s) (sn : s≤n)
    (rc : p.atIdx r∈C) (sc : p.atIdx s∈C) : ∃ k,k<n ∧ k%2=0 ∧ Nonempty (Route G e a b k) := by
  classical
  let I := (range (n+1)).filter (fun i => p.atIdx i∈C)
  have rm : r∈I := mem_filter.mpr ⟨mem_range.mpr (by omega),rc⟩
  have sm : s∈I := mem_filter.mpr ⟨mem_range.mpr (by omega),sc⟩
  let non : I.Nonempty := ⟨r,rm⟩
  let i := I.min' non
  let j := I.max' non
  have im : i∈I := min'_mem .. 
  have jm : j∈I := max'_mem ..
  have ir : i≤r := min'_le _ _ rm
  have sj : s≤j := le_max' _ _ sm
  have ij : i<j := by omega
  have jn : j≤n := by have := mem_range.mp (mem_filter.mp jm).1; omega
  have ic := (mem_filter.mp im).2
  have jc := (mem_filter.mp jm).2
  have diff : p.atIdx i≠p.atIdx j := fun h => by have := p.unique i (by omega) j jn h; omega
  have pair : ({p.atIdx i,p.atIdx j} : Finset V).card=2 := card_pair diff
  obtain ⟨z,zc,zout⟩ := exists_mem_not_mem_of_card_lt_card (show ({p.atIdx i,p.atIdx j} : Finset V).card<C.card by omega)
  have zne : z≠p.atIdx i ∧ z≠p.atIdx j := by simpa [not_or] using zout
  have ze : z≠e := fun h => miss (h ▸ zc)
  let L := AnchorParity.initialPart p i (by omega)
  let R := p.suffix j jn
  have lr (u : ℕ) (ui : u ≤ i) (v : ℕ) (vn : v≤n-j) : L.atIdx u≠R.atIdx v := by
    intro h; change p.atIdx u=p.atIdx (j+v) at h
    have := p.unique u (by omega) (j+v) (by omega) h; omega
  have left (u : ℕ) (ui : u ≤ i) : L.atIdx u≠z := by
    intro h; change p.atIdx u=z at h
    have um : u∈I := mem_filter.mpr ⟨mem_range.mpr (by omega),h ▸ zc⟩
    have lu : i≤u := min'_le _ _ um
    have eq : u=i := by omega
    exact zne.1 (eq ▸ h.symm)
  have right (v : ℕ) (vn : v≤n-j) : z≠R.atIdx v := by
    intro h; change z=p.atIdx (j+v) at h
    have vm : j+v∈I := mem_filter.mpr ⟨mem_range.mpr (by omega),h ▸ zc⟩
    have ub : j+v≤j := le_max' _ _ vm
    exact zne.2 ((show j+v=j by omega) ▸ h)
  let R' := R.prepend (cl zc jc zne.2) ze right
  have lr' (u : ℕ) (ui : u ≤ i) (v : ℕ) (vn : v≤n-j+1) : L.atIdx u≠R'.atIdx v := by
    cases v with
    | zero => exact left u ui
    | succ v => exact lr u ui v (by omega)
  by_cases even : (i+1+(n-j))%2=0
  · exact ⟨_,by omega,even,⟨AnchorParity.join L R (cl ic jc diff) lr⟩⟩
  · exact ⟨i+1+(n-j+1),by omega,by omega,⟨AnchorParity.join L R' (cl ic zc zne.1.symm) lr'⟩⟩

theorem short_contacts [DecidableEq V] {C : Finset V} (cl : G.IsClique (C : Set V))
    (size : 3≤C.card) (miss : e∉C) (h : ∃ k,k%2=0 ∧ Nonempty (Route G e a b k)) :
    ∃ m,∃ p : Route G e a b m,m%2=0 ∧
      ∀ i j,i≤m → j≤m → p.atIdx i∈C → p.atIdx j∈C → (j ≤ i + 2) := by
  classical
  let m := Nat.find h
  obtain ⟨ev,⟨p⟩⟩ := Nat.find_spec h
  refine ⟨m,p,ev,?_⟩
  intro i j _ hj ic jc
  apply Nat.le_of_not_gt; intro gap
  obtain ⟨k,less,ek,r⟩ := shorten cl size miss p gap hj ic jc
  have lo : m≤k := Nat.find_min' h ⟨ek,r⟩
  omega

variable [Fintype V] [DecidableEq V] (G) [DecidableRel G.Adj]

omit [Fintype V] in
/-- The pins on the ear cycle demand at most two vertices of each clique
color if all visits to the clique occur within two indices. -/
theorem cycle_pins {e x : V} {K : Finset V} (ke : e∉K) (xe : x≠e)
    {n : ℕ} (big : 2≤n) (even : n%2=0) (f : ℕ → V)
    (step : ∀ i<n,G.Adj (f i) (f (i+1))) (inj : ∀ i≤n,∀ j≤n,f i=f j → i=j)
    (avoid : ∀ i≤n,f i≠e) (noX : ∀ i≤n,f i≠x) (first : G.Adj e (f 0)) (last : G.Adj e (f n))
    (span : ∀ i j,i≤n → j≤n → f i∈K → f j∈K → (j ≤ i + 2)) :
    ∃ P Q,Frame G P Q ∧ e∈Q ∧ x∉P ∧ x∉Q ∧ (P∩K).card≤2 ∧ (Q∩K).card≤2 ∧
      (∀ i≤n,i%2=0 → f i∈P) ∧ (∀ i≤n,i%2=1 → f i∈Q) ∧
      ∀ z,z≠e → (∀ i≤n,f i≠z) → z∉P∪Q := by
  classical
  let side (k : ℕ) := (((range (n+1)).filter (fun i => i%2=k)).image f)
  let P := side 0
  let Q := insert e (side 1)
  have mem (k i : ℕ) (hi : i≤n) (par : i%2=k) : f i∈side k :=
    mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr (by omega),par⟩,rfl⟩
  have index {k : ℕ} {v : V} (m : v∈side k) : ∃ i≤n, i%2=k ∧ f i=v := by
    obtain ⟨i,im,fi⟩ := mem_image.mp m
    exact ⟨i,Nat.le_of_lt_succ (mem_range.mp (mem_filter.mp im).1),(mem_filter.mp im).2,fi⟩
  have dis : Disjoint P Q := by
    apply disjoint_left.mpr
    intro v vp vq
    obtain ⟨i,hi,ei,rfl⟩ := index vp
    rcases mem_insert.mp vq with eq | vq
    · exact avoid i hi eq
    · obtain ⟨j,hj,oj,eq⟩ := index vq
      have := inj j hj i hi eq
      omega
  have middle (i : ℕ) (lo : 0 < i) (up : i < n) :
      2 ≤ nbr G (f i) (side (1-i%2)) := by
    have prev := step (i-1) (by omega)
    rw [show i-1+1=i by omega] at prev
    exact PinnedColor34.two G (fun eq => by have := inj (i-1) (by omega) (i+1) (by omega) eq; omega)
      prev.symm (step i up) (mem _ _ (by omega) (by omega)) (mem _ _ (by omega) (by omega))
  have eqm : e∈Q := mem_insert_self ..
  have frame : Frame G P Q := by
    refine ⟨dis,?_,?_⟩
    · intro v vp
      obtain ⟨i,hi,par,rfl⟩ := index vp
      by_cases iz : i=0
      · subst i
        exact PinnedColor34.two G (Ne.symm (avoid 1 (by omega))) first.symm (step 0 (by omega))
          eqm (mem_insert_of_mem (mem 1 1 (by omega) rfl))
      by_cases en : i=n
      · subst i
        have prev := step (n-1) (by omega)
        rw [show n-1+1=n by omega] at prev
        exact PinnedColor34.two G (Ne.symm (avoid (n-1) (by omega))) last.symm prev.symm eqm
          (mem_insert_of_mem (mem 1 _ (by omega) (by omega)))
      have h := middle i (by omega) (by omega)
      rw [par] at h
      exact h.trans (card_le_card (filter_subset_filter _ (subset_insert ..)))
    · intro v vq
      rcases mem_insert.mp vq with rfl | vm
      · exact PinnedColor34.two G (fun eq => by have := inj 0 (by omega) n le_rfl eq; omega)
          first last (mem 0 0 (by omega) rfl) (mem 0 n le_rfl even)
      · obtain ⟨i,hi,par,rfl⟩ := index vm
        have h := middle i (by omega) (by omega)
        simpa only [par,Nat.sub_self] using h

  have few (k : ℕ) : (side k∩K).card≤2 := by
    let I := (range (n+1)).filter (fun i => i%2=k ∧ f i∈K)
    have incl : side k∩K⊆I.image f := by
      intro y ym; obtain ⟨s,sk⟩ := mem_inter.mp ym
      obtain ⟨i,hi,par,rfl⟩ := index s
      exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr (by omega),par,sk⟩,rfl⟩
    by_cases non : I.Nonempty
    · let base := I.min' non
      obtain ⟨br,bc,bm⟩ := mem_filter.mp (min'_mem I non)
      have bn := mem_range.mp br
      have sub : I⊆{base,base+2} := by
        intro j jm; obtain ⟨jr,jp,jk⟩ := mem_filter.mp jm
        have low : base≤j := min'_le _ _ jm
        have dist := span base j (by omega) (by have := mem_range.mp jr; omega) bm jk
        change base%2=k at bc
        exact (show j=base ∨ j=base+2 by omega).elim (fun h => h ▸ mem_insert_self ..)
          (fun h => h ▸ mem_insert_of_mem (mem_singleton_self _))
      have cnt := card_le_card sub
      rw [card_pair (by omega : base≠base+2)] at cnt
      exact (card_le_card incl).trans ((card_image_le).trans cnt)
    · rw [not_nonempty_iff_eq_empty.mp non,image_empty] at incl
      rw [subset_empty.mp incl,card_empty]; decide
  have xoff (k : ℕ) (h : x∈side k) : False := by
    obtain ⟨i,hi,_,eq⟩ := index h
    exact noX i hi eq
  have same : Q∩K=side 1∩K := by ext y; simp only [Q,mem_inter,mem_insert]; by_cases h : y=e <;> simp_all
  refine ⟨P,Q,frame,eqm,xoff 0,fun h => (mem_insert.mp h).elim xe (xoff 1),few 0,same ▸ few 1,mem 0,fun i hi par => mem_insert_of_mem (mem 1 i hi par),?_⟩
  intro z ze away m
  have miss {k : ℕ} (h : z∈side k) : False := by obtain ⟨i,hi,_,eq⟩ := index h; exact away i hi eq
  exact (mem_union.mp m).elim miss (fun q => (mem_insert.mp q).elim ze miss)

/-- Complete any compatible ear-frame pins to a two–two split of the four
clique vertices. The omitted pivot would require an uncredited cubic. -/
theorem merge_pins {R K A B : Finset V} {e x : V} (de : G.degree e=2)
    (pos : ∀ v,0<trianglesAt G v) (inj : Function.Injective (trianglesAt G))
    (tight : CliquePivot33.Tight G R) (cl : G.IsNClique 4 K) (off : x∉K) (see : ∀ v∈K,G.Adj x v)
    (frame : Frame G A B) (eb : e∈B) (xa : x∉A) (xb : x∉B)
    (ha : (A∩K).card≤2) (hb : (B∩K).card≤2) :
    ∃ u,u∉R ∧ G.degree u=3 ∧ G.Adj u x := by
  classical
  have inK : A∩K⊆K\(B∩K) := fun y ym =>
    mem_sdiff.mpr ⟨(mem_inter.mp ym).2,fun m => disjoint_left.mp frame.1 (mem_inter.mp ym).1 (mem_inter.mp m).1⟩
  obtain ⟨P,ap,pk,ps⟩ := exists_subsuperset_card_eq inK ha
    (show 2≤(K\(B∩K)).card by rw [card_sdiff inter_subset_right,cl.2]; omega)
  let Q := K\P
  have pK : P⊆K := pk.trans sdiff_subset
  have qK : Q⊆K := sdiff_subset
  have qs : Q.card=2 := by rw [show Q=K\P from rfl,card_sdiff pK,cl.2,ps]
  have pb : Disjoint P B := disjoint_left.mpr (fun y pm bm =>
    (mem_sdiff.mp (pk pm)).2 (mem_inter.mpr ⟨bm,pK pm⟩))
  have aq : Disjoint A Q := disjoint_left.mpr (fun y am qm =>
    (mem_sdiff.mp qm).2 (ap (mem_inter.mpr ⟨am,qK qm⟩)))
  have pq : Disjoint P Q := disjoint_left.mpr (fun y pm qm => (mem_sdiff.mp qm).2 pm)
  have full {y : V} {S : Finset V} (sz : S.card=2) (h : ∀ v∈S,G.Adj y v) : 2≤nbr G y S := by
    have eq := filter_true_of_mem h; simp [nbr,eq,sz]
  have fr : Frame G (A∪P) (B∪Q) := by
    refine ⟨by simp only [disjoint_union_left,disjoint_union_right]; exact ⟨⟨frame.1,pb⟩,aq,pq⟩,?_,?_⟩
    · intro y ym
      rcases mem_union.mp ym with ya|yp
      · exact (frame.2.1 y ya).trans (Repair.nbr_mono G y subset_union_left)
      · exact (full qs (fun v vq => cl.1 (pK yp) (qK vq) (fun h => disjoint_left.mp pq yp (h ▸ vq)))).trans
          (Repair.nbr_mono G y subset_union_right)
    · intro y ym
      rcases mem_union.mp ym with yb|yq
      · exact (frame.2.2 y yb).trans (Repair.nbr_mono G y subset_union_left)
      · exact (full ps (fun v vp => cl.1 (qK yq) (pK vp) (fun h => disjoint_left.mp pq (h ▸ vp) yq))).trans
          (Repair.nbr_mono G y subset_union_right)
  obtain ⟨u,_,_,ur,du,ux⟩ := HighEar.outside_cubic G de pos inj (mem_union_left _ eb) tight fr
    (fun h => (mem_union.mp h).elim xa (fun m => off (pK m)))
    (fun h => (mem_union.mp h).elim xb (fun m => off (qK m)))
    ((full ps (fun y ym => see y (pK ym))).trans (Repair.nbr_mono G x subset_union_right))
    ((full qs (fun y ym => see y (qK ym))).trans (Repair.nbr_mono G x subset_union_right))
  exact ⟨u,ur,du,ux⟩

end Graffiti384b.HighEar
#print axioms Graffiti384b.HighEar.short_contacts
#print axioms Graffiti384b.HighEar.cycle_pins
#print axioms Graffiti384b.HighEar.merge_pins
