import PathMaximum180
import TriangleRotation180

set_option warningAsError true
namespace Minimal180
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open scoped BigOperators
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Orient a spanning tree toward r. Its internal edges on D are counted
by those nonroot vertices of D whose predecessor remains in D. -/
theorem parent_edge_count (T : SimpleGraph V) [DecidableRel T.Adj] (tr : T.IsTree)
    (r : V) (D : Finset V) :
    ∃ p : V → V, (∀ v≠r, T.Adj v (p v) ∧ T.dist v r=T.dist (p v) r+1) ∧
    (T.edgeFinset∩D.sym2).card=((D.erase r).filter (fun v => p v∈D)).card := by
  classical
  let p (v : V) := if h : v=r then r else (Graffiti169.exists_predecessor T tr.isConnected r v h).choose
  have spec (v : V) (ne : v≠r) : T.Adj v (p v) ∧ T.dist v r=T.dist (p v) r+1 := by
    simpa only [p,dif_neg ne] using (Graffiti169.exists_predecessor T tr.isConnected r v ne).choose_spec
  let f (v : V) := s(v,p v)
  have inj {i j} (ir : i≠r) (jr : j≠r) (same : f i=f j) : i=j := by
    rcases Sym2.eq_iff.mp same with h|⟨h,k⟩
    · exact h.1
    · have a := (spec i ir).2
      have b := (spec j jr).2
      rw [k] at a
      rw [← h] at b
      omega
  have sub : (univ.erase r).image f⊆T.edgeFinset := by
    intro e he
    obtain ⟨i,hi,rfl⟩ := mem_image.mp he
    exact mem_edgeFinset.mpr (spec i (mem_erase.mp hi).1).1
  have card := card_image_of_injOn (s:=univ.erase r) (f:=f)
    (fun i hi j hj equ => inj (mem_erase.mp hi).1 (mem_erase.mp hj).1 equ)
  have erase := card_erase_add_one (mem_univ r)
  rw [card_univ] at erase
  have all := eq_of_subset_of_card_le sub (by have := tr.card_edgeFinset; omega)
  let K := (D.erase r).filter (fun v => p v∈D)
  have form : T.edgeFinset∩D.sym2=K.image f := by
    ext e
    constructor
    · intro he
      obtain ⟨old,ind⟩ := mem_inter.mp he
      rw [← all] at old
      obtain ⟨v,hv,rfl⟩ := mem_image.mp old
      obtain ⟨vd,pd⟩ := mk_mem_sym2_iff.mp ind
      exact mem_image.mpr ⟨v,mem_filter.mpr ⟨mem_erase.mpr ⟨(mem_erase.mp hv).1,vd⟩,pd⟩,rfl⟩
    · intro he
      obtain ⟨v,hv,rfl⟩ := mem_image.mp he
      obtain ⟨vr,pd⟩ := mem_filter.mp hv
      obtain ⟨ne,vd⟩ := mem_erase.mp vr
      exact mem_inter.mpr ⟨mem_edgeFinset.mpr (spec v ne).1,mk_mem_sym2_iff.mpr ⟨vd,pd⟩⟩
  refine ⟨p,spec,?_⟩
  rw [form,card_image_of_injOn (s:=K) (f:=f) (fun i hi j hj eq =>
    inj (mem_erase.mp (mem_filter.mp hi).1).1 (mem_erase.mp (mem_filter.mp hj).1).1 eq)]

theorem independent_mass (T : SimpleGraph V) [DecidableRel T.Adj] (B : Finset V) (ind : Indep T B) :
    ∑ v∈B, T.degree v = (B.biUnion (fun v => T.incidenceFinset v)).card := by
  classical
  have dis : (↑B : Set V).PairwiseDisjoint (fun x => T.incidenceFinset x) := by
    intro u hu v hv ne
    apply Finset.disjoint_left.mpr
    intro e h₁ h₂
    change e∈T.incidenceFinset u at h₁
    change e∈T.incidenceFinset v at h₂
    rw [T.incidenceFinset_eq_filter] at h₁ h₂
    obtain ⟨he,hu'⟩ := mem_filter.mp h₁
    rw [(Sym2.mem_and_mem_iff ne).mp ⟨hu',(mem_filter.mp h₂).2⟩] at he
    exact ind u hu v hv ne (mem_edgeFinset.mp he)
  simp [card_biUnion dis]

/-- Exact deficit for any tree alternating on P, with an internal root.
The quantity |D| minus the induced edge count is the number of components
of the forest on D=(A∪P) minus (A∩P). -/
theorem tree_defect (T : SimpleGraph V) [DecidableRel T.Adj] (tr : T.IsTree) (hn : 1<Fintype.card V)
    (r : V) (internal : r∉leaves T) (A P : Finset V) (ai : Indep T A)
    (cross : ∀ {x y}, T.Adj x y → (x∈P ↔ y∉P)) :
    let X := A∪P
    let D := X\(A∩P)
    Fintype.card V+((eligible A P r)∩leaves T).card+(T.edgeFinset∩D.sym2).card =
      1+A.card+P.card+D.card+∑ v∈X, (T.degree v-2) := by
  classical
  let X := A∪P
  let D := X\(A∩P)
  let Y := A\P
  have pi : Indep T P := fun _ a _ b _ e => (cross e).mp a b
  have yi : Indep T Y := fun x h y k => ai x (mem_sdiff.mp h).1 y (mem_sdiff.mp k).1
  have memInc {v a b : V} : s(a,b)∈T.incidenceFinset v ↔ T.Adj a b ∧ (v=a ∨ v=b) := by
    rw [T.incidenceFinset_eq_filter]
    simp [Sym2.mem_iff]
  have whole : P.biUnion (fun v => T.incidenceFinset v)=T.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_biUnion,memInc,mem_edgeFinset]
      constructor
      · rintro ⟨_,_,e,_⟩; exact e
      · intro e
        by_cases h : b∈P
        · exact ⟨b,h,e,Or.inr rfl⟩
        · exact ⟨a,(cross e).mpr h,e,Or.inl rfl⟩
  have inner : Y.biUnion (fun v => T.incidenceFinset v)=T.edgeFinset∩D.sym2 := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_biUnion,memInc,mem_inter,mem_edgeFinset,mk_mem_sym2_iff]
      have acrossA (e : T.Adj a b) := cross e
      have bt (e : T.Adj a b) := cross e.symm
      have an (e : T.Adj a b) (ha : a∈A) : b∉A := fun hb => ai a ha b hb e.ne e
      have bn (e : T.Adj a b) (hb : b∈A) : a∉A := fun ha => an e ha hb
      simp only [Y,D,X,mem_sdiff,mem_union,mem_inter]
      constructor
      · rintro ⟨v,⟨va,vp⟩,e,h|h⟩ <;> subst v
        · specialize bt e; specialize an e va; tauto
        · specialize acrossA e; specialize bn e va; tauto
      · rintro ⟨e,aD,bD⟩
        by_cases ap : a∈P
        · exact ⟨b,⟨bD.1.resolve_right ((cross e).mp ap),(cross e).mp ap⟩,e,Or.inr rfl⟩
        · exact ⟨a,⟨aD.1.resolve_right ap,ap⟩,e,Or.inl rfl⟩
  have cover : P∪Y=X := by ext x; simp [Y,X]; tauto
  have dis : Disjoint P Y := disjoint_left.mpr (fun _ h k => (mem_sdiff.mp k).2 h)
  have mass : ∑ v∈P∪Y, T.degree v = (∑ v∈P,T.degree v)+(∑ v∈Y,T.degree v) := sum_union dis
  rw [cover,independent_mass T P pi,whole,independent_mass T Y yi,inner] at mass
  have vertex (v : V) : T.degree v+(if v∈leaves T then 1 else 0)=2+(T.degree v-2) := by
    obtain ⟨w,e⟩ := exists_adj T tr.isConnected hn v
    have pos := (T.degree_pos_iff_exists_adj v).mpr ⟨w,e⟩
    have lf : v∈leaves T ↔ T.degree v=1 := by simp [leaves,SimpleGraph.degree,SimpleGraph.neighborFinset]
    split_ifs with h
    · have := lf.mp h; omega
    · have := mt lf.mpr h; omega
  have sum : (∑ v∈X, (T.degree v+if v∈leaves T then 1 else 0))=(∑ v∈X,(2+(T.degree v-2))) :=
    sum_congr rfl (fun v _ => vertex v)
  simp only [sum_add_distrib,sum_const,smul_eq_mul] at sum
  have leafCount : (∑ v∈X, if v∈leaves T then 1 else 0 : ℕ)=(X∩leaves T).card := by
    simp [filter_mem_eq_inter]
  rw [leafCount,mass] at sum
  have same : eligible A P r∩leaves T=X∩leaves T := by
    ext v
    simp only [mem_inter,eligible_iff,X,mem_union]
    by_cases eq : v=r
    · subst v; simp [internal]
    · simp [eq]
  have id : A∩P ⊆ X := inter_subset_left.trans subset_union_left
  have cardD := card_sdiff_add_card_eq_card id
  have cup := card_union_add_card_inter A P
  change X.card+(A∩P).card=_ at cup
  change D.card+(A∩P).card=_ at cardD
  change Fintype.card V+_+(T.edgeFinset∩D.sym2).card=1+A.card+P.card+D.card+∑ v∈X, (T.degree v-2)
  rw [same]
  have := tr.card_edgeFinset
  omega

theorem forest_strict (T : SimpleGraph V) [DecidableRel T.Adj] (tr : T.IsTree)
    (D : Finset V) (ne : D.Nonempty) : (T.edgeFinset∩D.sym2).card<D.card := by
  obtain ⟨z,hz⟩ := ne
  obtain ⟨p,_,eq⟩ := parent_edge_count T tr z D
  rw [eq]
  have b := card_le_card (filter_subset (fun v => p v∈D) (D.erase z))
  have one := card_erase_add_one hz
  omega

/-- The component count of the induced forest on the symmetric difference
can absorb any bipartite rank deficit. Tightness then forces the tree to be
optimal and precludes branching anywhere in the union of the marked sets. -/
theorem rigid_of_forest_gap (J T : SimpleGraph V) [DecidableRel T.Adj] (tr : T.IsTree) (sub : T≤J)
    (hn : 1<Fintype.card V) (r : V) (internal : r∉leaves T) (A P : Finset V)
    (ai : Indep J A) (cross : ∀ {x y}, T.Adj x y → (x∈P ↔ y∉P))
    (tight : weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card)
    (gap : let D := (A∪P)\(A∩P)
           (T.edgeFinset∩D.sym2).card+Fintype.card V≤D.card+bipartiteNum J) :
    (eligible A P r∩leaves T).card=weightedLeaves J (eligible A P r) ∧
    ∀ w∈A∪P, T.degree w≤2 := by
  classical
  let D := (A∪P)\(A∩P)
  change (T.edgeFinset∩D.sym2).card+Fintype.card V≤D.card+bipartiteNum J at gap
  have identity := tree_defect T tr hn r internal A P (fun x hx y hy nq e => ai x hx y hy nq (sub e)) cross
  change Fintype.card V+_+(T.edgeFinset∩D.sym2).card=1+A.card+P.card+D.card+_ at identity
  have bound : (eligible A P r∩leaves T).card≤weightedLeaves J (eligible A P r) :=
    le_sup (f:=fun K => (eligible A P r∩leaves K).card) (mem_filter.mpr ⟨mem_univ _,sub,tr⟩)
  refine ⟨by omega,?_⟩
  intro w hw
  have term := single_le_sum (f:=fun v => T.degree v-2) (fun _ _ => Nat.zero_le _) hw
  change T.degree w-2 ≤ ∑ v∈A∪P, (T.degree v-2) at term
  omega

/-- If the lower graph omits one bipartite vertex, a tight state whose two
marks differ forces every parity tree with internal root to be optimal.
All vertices marked by either set have degree at most two in that tree. -/
theorem one_defect_rigid (J T : SimpleGraph V) [DecidableRel T.Adj] (tr : T.IsTree) (sub : T≤J)
    (hn : 1<Fintype.card V) (r : V) (internal : r∉leaves T) (A P : Finset V)
    (ai : Indep J A) (ne : A≠P) (cross : ∀ {x y}, T.Adj x y → (x∈P ↔ y∉P))
    (rank : bipartiteNum J+1=Fintype.card V)
    (tight : weightedLeaves J (eligible A P r)+bipartiteNum J=1+A.card+P.card) :
    (eligible A P r∩leaves T).card=weightedLeaves J (eligible A P r) ∧
    (∀ w∈A∪P, T.degree w≤2) ∧
    let D := (A∪P)\(A∩P)
    (T.edgeFinset∩D.sym2).card+1=D.card := by
  classical
  let D := (A∪P)\(A∩P)
  have pos : D.Nonempty := by
    by_contra! no
    apply ne
    ext v
    have h : v∉D := fun hv => no ⟨v,hv⟩
    simp only [D,mem_sdiff,mem_inter,mem_union] at h
    tauto
  have f := forest_strict T tr D pos
  have identity := tree_defect T tr hn r internal A P (fun x hx y hy nq e => ai x hx y hy nq (sub e)) cross
  change Fintype.card V+_+(T.edgeFinset∩D.sym2).card=1+A.card+P.card+D.card+_ at identity
  have bound : (eligible A P r∩leaves T).card≤weightedLeaves J (eligible A P r) :=
    le_sup (f:=fun K => (eligible A P r∩leaves K).card) (mem_filter.mpr ⟨mem_univ _,sub,tr⟩)
  refine ⟨by omega,?_,by change (T.edgeFinset∩D.sym2).card+1=D.card; omega⟩
  intro w hw
  have term := single_le_sum (f:=fun v => T.degree v-2) (fun _ _ => Nat.zero_le _) hw
  change T.degree w-2 ≤ ∑ v∈A∪P, (T.degree v-2) at term
  omega

#print axioms rigid_of_forest_gap
#print axioms forest_strict
#print axioms one_defect_rigid
#print axioms parent_edge_count
#print axioms tree_defect
end Minimal180
