import StarBranch180

set_option warningAsError true
namespace Minimal180.OppositeGain
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Transversals HigherRank
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The exact tree defect gains one when one exceptional edge has both
ends outside both marks and every other edge alternates on P. -/
theorem one_horizontal_defect (T : SimpleGraph V) [DecidableRel T.Adj] (tr : T.IsTree) (hn : 1<Fintype.card V)
    (r : V) (internal : r∉leaves T) (A P : Finset V) (ai : Indep T A)
    (u v : V) (edge : T.Adj u v) (uo : u∉A∪P) (vo : v∉A∪P)
    (cross : ∀ {x y}, T.Adj x y → s(x,y)≠s(u,v) → (x∈P ↔ y∉P)) :
    let X := A∪P
    let D := X\(A∩P)
    Fintype.card V+((eligible A P r)∩leaves T).card+(T.edgeFinset∩D.sym2).card =
      2+A.card+P.card+D.card+∑ v∈X, (T.degree v-2) := by
  classical
  let X := A∪P
  let D := X\(A∩P)
  let Y := A\P
  let uv := s(u,v)
  have special {x y : V} (eq : s(x,y)=uv) : x∉A∪P ∧ y∉A∪P := by
    rcases Sym2.eq_iff.mp eq with ⟨e,f⟩|⟨e,f⟩
    · exact ⟨e ▸ uo,f ▸ vo⟩
    · exact ⟨e ▸ vo,f ▸ uo⟩
  have pi : Indep T P := by
    intro x xp y yp _ ed
    by_cases eq : s(x,y)=uv
    · exact (special eq).1 (mem_union_right _ xp)
    · exact (cross ed eq).mp xp yp
  have yi : Indep T Y := fun x h y k => ai x (mem_sdiff.mp h).1 y (mem_sdiff.mp k).1
  have memInc {v a b : V} : s(a,b)∈T.incidenceFinset v ↔ T.Adj a b ∧ (v=a ∨ v=b) := by
    rw [T.incidenceFinset_eq_filter]
    simp [Sym2.mem_iff]
  have whole : P.biUnion (fun v => T.incidenceFinset v)=T.edgeFinset.erase uv := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_biUnion,memInc,mem_erase,mem_edgeFinset]
      constructor
      · rintro ⟨w,wm,ed,h|h⟩ <;> subst w
        · exact ⟨fun eq => (special eq).1 (mem_union_right _ wm),ed⟩
        · exact ⟨fun eq => (special eq).2 (mem_union_right _ wm),ed⟩
      · rintro ⟨ne,ed⟩
        by_cases h : b∈P
        · exact ⟨b,h,ed,Or.inr rfl⟩
        · exact ⟨a,(cross ed ne).mpr h,ed,Or.inl rfl⟩
  have inner : Y.biUnion (fun v => T.incidenceFinset v)=T.edgeFinset∩D.sym2 := by
    ext e
    induction e using Sym2.ind with
    | _ a b =>
      simp only [mem_biUnion,memInc,mem_inter,mem_edgeFinset,mk_mem_sym2_iff]
      by_cases eq : s(a,b)=uv
      · have oa := (special eq).1
        have ob := (special eq).2
        have aA : a∉A := fun m => oa (mem_union_left _ m)
        have bA : b∉A := fun m => ob (mem_union_left _ m)
        constructor
        · rintro ⟨w,wm,_,h|h⟩ <;> subst w
          · exact (aA (mem_sdiff.mp wm).1).elim
          · exact (bA (mem_sdiff.mp wm).1).elim
        · rintro ⟨_,ad,_⟩;exact (oa (mem_sdiff.mp ad).1).elim
      have acrossA (e : T.Adj a b) := cross e eq
      have bt (e : T.Adj a b) := cross e.symm (fun h => eq ((Sym2.eq_swap).trans h))
      have an (e : T.Adj a b) (ha : a∈A) : b∉A := fun hb => ai a ha b hb e.ne e
      have bn (e : T.Adj a b) (hb : b∈A) : a∉A := fun ha => an e ha hb
      simp only [Y,D,X,mem_sdiff,mem_union,mem_inter]
      constructor
      · rintro ⟨v,⟨va,vp⟩,e,h|h⟩ <;> subst v
        · specialize bt e; specialize an e va; tauto
        · specialize acrossA e; specialize bn e va; tauto
      · rintro ⟨e,aD,bD⟩
        by_cases ap : a∈P
        · exact ⟨b,⟨bD.1.resolve_right ((acrossA e).mp ap),(acrossA e).mp ap⟩,e,Or.inr rfl⟩
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
  change Fintype.card V+_+(T.edgeFinset∩D.sym2).card=2+A.card+P.card+D.card+∑ v∈X, (T.degree v-2)
  rw [same]
  have ec := tr.card_edgeFinset
  have one := card_erase_add_one (show uv∈T.edgeFinset from mem_edgeFinset.mpr edge)
  omega

#print axioms one_horizontal_defect
end Minimal180.OppositeGain
