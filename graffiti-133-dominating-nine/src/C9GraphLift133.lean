import NoFiveHoles133
import PentagonStructure133

namespace Graffiti133C9
open SimpleGraph Graffiti133 Graffiti133NoFive Finset
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 500000

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

def HasProfile {P : Type*} (H : Hole G 9) (contacts : P → Finset (Fin 9)) (v : V) (p : P) : Prop :=
  Outside H.c v ∧ ∀ i, G.Adj v (H.c i) ↔ i ∈ contacts p

def markedPairs {P : Type*} [LinearOrder P] (s : Finset P)
    (mayEdge : P → P → Prop) [DecidableRel mayEdge] : Finset (P × P) :=
  (s ×ˢ s).filter fun ab => ab.1 < ab.2 ∧ mayEdge ab.1 ab.2

private theorem inject_profile {P : Type*} (H : Hole G 9) (h4 : FourCycleFree G)
    (contacts : P → Finset (Fin 9)) (two : ∀ p, 2 ≤ (contacts p).card)
    {x y : V} {i : P} (hx : HasProfile H contacts x i) (hy : HasProfile H contacts y i) : x=y := by
  obtain ⟨a,ha,b,hb,ab⟩ := Finset.one_lt_card.mp (show 1 < (contacts i).card from two i)
  exact h4 _ _ _ _ (H.inj.ne ab) ((hx.2 a).mpr ha).symm ((hx.2 b).mpr hb).symm
    ((hy.2 a).mpr ha).symm ((hy.2 b).mpr hb).symm

private noncomputable def row (G : SimpleGraph V) (v : V) (S : Finset V) : ℕ :=
  ∑ w ∈ S, @ite ℕ (G.Adj v w) (Classical.propDecidable _) 1 0

private lemma row_card (v : V) (S : Finset V) :
    row G v S = (S.filter fun w => G.Adj v w).card := by
  classical
  exact (Finset.card_filter _ _).symm

private lemma local_bound (v : V) : localIndependence G v ≤ row G v Finset.univ := by
  classical
  obtain ⟨A,hA,eA⟩ := Graffiti133Pentagon.PentagonFrame.maxLocalSet (G:=G) v
  rw [←eA,row_card]
  exact Finset.card_le_card (fun x hx => Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,(Graffiti133Pentagon.PentagonFrame.memLocalSet.mp hA).1 x hx⟩)

private lemma row_symm (A B : Finset V) :
    (∑ x ∈ A, row G x B) = ∑ y ∈ B, row G y A := by
  classical
  unfold row
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [G.adj_comm y x]

private lemma cycle_row (H : Hole G 9) (i : Fin 9) :
    row G (H.c i) (Finset.univ.image H.c) = 2 := by
  classical
  change (∑ w ∈ Finset.univ.image H.c, (if G.Adj (H.c i) w then 1 else 0 : ℕ))=2
  rw [Finset.sum_image (fun _ _ _ _ eq => H.inj eq)]
  have aux : ∀ i : Fin 9, (Finset.univ.filter fun j => Cyclic i j).card = 2 := by decide
  rw [←aux i,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  exact if_congr (H.adj i j) rfl rfl

private lemma contact_row {P : Type*} (H : Hole G 9) (contacts : P → Finset (Fin 9))
    {x : V} {i : P} (hx : HasProfile H contacts x i) :
    row G x (Finset.univ.image H.c) = (contacts i).card := by
  classical
  change (∑ w ∈ Finset.univ.image H.c, (if G.Adj x w then 1 else 0 : ℕ))=_
  rw [Finset.sum_image (fun _ _ _ _ eq => H.inj eq)]
  have e : (Finset.univ.filter fun j => j∈contacts i)=contacts i := by ext j; simp
  rw [←e,Finset.card_filter]
  apply Finset.sum_congr rfl
  intro j _
  exact if_congr (hx.2 j) rfl rfl

private noncomputable def lowEdges {P : Type*} [LinearOrder P] (O : Finset V) (q : V → P)
    (G : SimpleGraph V) : Finset (V × V) := by
  classical
  exact (O ×ˢ O).filter (fun p => G.Adj p.1 p.2 ∧ q p.1 < q p.2)

private lemma low_mem {P : Type*} [LinearOrder P] {O : Finset V} {q : V → P} {p : V × V} :
    p∈lowEdges O q G ↔ (p.1∈O ∧ p.2∈O) ∧ G.Adj p.1 p.2 ∧ q p.1 < q p.2 := by
  classical
  simp only [lowEdges,Finset.mem_filter,Finset.mem_product]

private lemma twice_low {P : Type*} [LinearOrder P] (O : Finset V) (q : V → P)
    (inj : Set.InjOn q ↑O) :
    (∑ x ∈ O, row G x O) = 2 * (lowEdges O q G).card := by
  classical
  let L := lowEdges O q G
  let R := (O ×ˢ O).filter fun p => G.Adj p.1 p.2 ∧ q p.2 < q p.1
  let A := (O ×ˢ O).filter fun p => G.Adj p.1 p.2
  have rm (p : V×V) : p∈R ↔ (p.1∈O ∧ p.2∈O) ∧ G.Adj p.1 p.2 ∧ q p.2 < q p.1 := by
    simp only [R,Finset.mem_filter,Finset.mem_product]
  have am (p : V×V) : p∈A ↔ (p.1∈O ∧ p.2∈O) ∧ G.Adj p.1 p.2 := by
    simp only [A,Finset.mem_filter,Finset.mem_product]
  have eq : L ∪ R = A := by
    ext p
    rw [Finset.mem_union,low_mem,rm,am]
    constructor
    · rintro (⟨ho,e,_⟩ | ⟨ho,e,_⟩) <;> exact ⟨ho,e⟩
    · rintro ⟨ho,e⟩
      have ne : q p.1 ≠ q p.2 := fun eq => e.ne (inj ho.1 ho.2 eq)
      rcases lt_or_gt_of_ne ne with a | b
      · exact Or.inl ⟨ho,e,a⟩
      · exact Or.inr ⟨ho,e,b⟩
  have dis : Disjoint L R := Finset.disjoint_left.mpr fun p a b =>
    (not_lt_of_ge (le_of_lt (low_mem.mp a).2.2)) ((rm _).mp b).2.2
  have same : L.card=R.card := by
    refine Finset.card_bij (fun x _ => x.swap) ?_ ?_ ?_
    · intro x hx
      obtain ⟨⟨a,b⟩,e,h⟩ := low_mem.mp hx
      exact (rm _).mpr ⟨⟨b,a⟩,e.symm,h⟩
    · intro a _ b _ e
      exact congrArg Prod.swap e
    · intro x hx
      obtain ⟨⟨a,b⟩,e,h⟩ := (rm _).mp hx
      exact ⟨x.swap,low_mem.mpr ⟨⟨b,a⟩,e.symm,h⟩,rfl⟩
  have cnt : A.card = 2*L.card := by
    rw [←eq,Finset.card_union_of_disjoint dis,←same,Nat.two_mul]
  rw [←cnt]
  unfold row
  rw [←Finset.sum_product O O (fun p : V × V => if G.Adj p.1 p.2 then (1:ℕ) else 0)]
  exact (Finset.card_filter _ _).symm

/-- The all-graph reduction to a finite contact-score budget. The input
compatibility and marking theorems are only required on actual profiles. -/
theorem graph_budget (H : Hole G 9) (h4 : FourCycleFree G)
    (contacts : Fin 57 → Finset (Fin 9)) (two : ∀ p, 2 ≤ (contacts p).card)
    (classify : ∀ x, Outside H.c x → ∃ p, HasProfile H contacts x p)
    (okPair mayEdge : Fin 57 → Fin 57 → Prop) [DecidableRel mayEdge]
    (compat : ∀ {x y i j}, x≠y → HasProfile H contacts x i → HasProfile H contacts y j →
      i < j → okPair i j)
    (marked : ∀ {x y i j}, G.Adj x y → HasProfile H contacts x i → HasProfile H contacts y j →
      i < j → mayEdge i j)
    (budget : ∀ S : Finset (Fin 57), (∀ i ∈ S, ∀ j ∈ S, i < j → okPair i j) →
      (∑ i ∈ S, ((contacts i).card-2)) + (markedPairs S mayEdge).card ≤ 9) :
    (∑ v : V, localIndependence G v) ≤ 4 * Fintype.card V := by
  classical
  let C : Finset V := Finset.univ.image H.c
  let O : Finset V := Finset.univ \ C
  have old : C.card=9 := by rw [Finset.card_image_of_injective _ H.inj]; simp
  have size : O.card+9=Fintype.card V := by
    have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ C)
    rw [old,Finset.card_univ] at h
    exact h
  have out (v : V) (hv : v∈O) : Outside H.c v := by
    intro i e
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,e.symm⟩)
  let q (v : V) := if hv : v∈O then Classical.choose (classify v (out v hv)) else 0
  have prof (v : V) (hv : v∈O) : HasProfile H contacts v (q v) := by
    rw [show q v=Classical.choose (classify v (out v hv)) from dif_pos hv]
    exact Classical.choose_spec (classify v (out v hv))
  have qi : Set.InjOn q ↑O := by
    intro u hu v hv eq
    exact inject_profile H h4 contacts two (prof u hu) (eq.symm ▸ prof v hv)
  let S := O.image q
  have hclique (i : Fin 57) (hi : i∈S) (j : Fin 57) (hj : j∈S) (ij : i < j) : okPair i j := by
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hj
    exact compat (fun e => (ne_of_lt ij) (congrArg q e)) (prof x hx) (prof y hy) ij
  have markedBound : (lowEdges O q G).card ≤ (markedPairs S mayEdge).card := by
    refine Finset.card_le_card_of_injOn (fun p => (q p.1,q p.2)) ?_ ?_
    · intro p hp
      obtain ⟨⟨a,b⟩,e,lt⟩ := low_mem.mp hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ a,
        Finset.mem_image_of_mem _ b⟩,lt,marked e (prof _ a) (prof _ b) lt⟩
    · intro a ha b hb e
      have ha := (low_mem.mp ha).1
      have hb := (low_mem.mp hb).1
      exact Prod.ext (qi ha.1 hb.1 (congrArg Prod.fst e)) (qi ha.2 hb.2 (congrArg Prod.snd e))
  have score : (∑ v ∈ O, ((contacts (q v)).card-2)) + (lowEdges O q G).card ≤ 9 := by
    have b := budget S hclique
    rw [show (∑ i ∈ S, ((contacts i).card-2)) =
      ∑ v ∈ O, ((contacts (q v)).card-2) from Finset.sum_image (fun _ a _ b e => qi a b e)] at b
    omega
  have cSum : (∑ v ∈ C, row G v C)=18 := by
    change (∑ v ∈ Finset.univ.image H.c, row G v C)=18
    rw [Finset.sum_image (fun _ _ _ _ e => H.inj e)]
    have cRow (i : Fin 9) : row G (H.c i) C=2 := cycle_row H i
    simp_rw [cRow]
    simp
  have weight : (∑ v ∈ O,row G v C) =
      (∑ v ∈ O,((contacts (q v)).card-2)) + 2*O.card := by
    have eq (v : V) (hv : v∈O) : row G v C= ((contacts (q v)).card-2)+2 := by
      rw [contact_row H contacts (prof v hv)]
      have := two (q v)
      omega
    rw [Finset.sum_congr rfl eq,Finset.sum_add_distrib]
    simp [Nat.mul_comm]
  have split (f : V → ℕ) : (∑ v : V, f v) = (∑ v ∈ C,f v)+(∑ v ∈ O,f v) := by
    simpa [O,Nat.add_comm] using (Finset.sum_sdiff (f:=f) (Finset.subset_univ C)).symm
  have rows (v : V) : row G v Finset.univ = row G v C + row G v O :=
    split (fun w => @ite ℕ (G.Adj v w) (Classical.propDecidable _) 1 0)
  refine (Finset.sum_le_sum (fun v _ => local_bound v)).trans ?_
  rw [split (fun v => row G v Finset.univ)]
  simp_rw [rows,Finset.sum_add_distrib]
  rw [cSum,row_symm (G:=G) C O,weight,twice_low O q qi]
  omega

#print axioms graph_budget
end Graffiti133C9
