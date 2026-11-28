import StarStructure
import OuterForest
import Proof324
import Criterion

namespace CographTree
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
local notation "n" => Fintype.card V

theorem neighbor_center {c : V} (h : StarAt G c) :
    G.neighborFinset c = univ.erase c := by
  classical
  ext v
  simp [h c v, ne_comm]

omit [DecidableEq V] in
theorem neighbor_leaf {c v : V} (h : StarAt G c) (hv : v ≠ c) :
    G.neighborFinset v = {c} := by
  classical
  ext w
  simp [h v w,hv]

theorem degree_center {c : V} (h : StarAt G c) : G.degree c = n - 1 := by
  classical
  change (G.neighborFinset c).card = _
  rw [neighbor_center G h,card_erase_of_mem (mem_univ _),card_univ]

omit [DecidableEq V] in
theorem degree_leaf {c v : V} (h : StarAt G c) (hv : v ≠ c) : G.degree v = 1 := by
  change (G.neighborFinset v).card = _
  simp [neighbor_leaf G h hv]

theorem max_degree {c : V} (h : StarAt G c) : G.maxDegree = n - 1 := by
  letI : Nonempty V := ⟨c⟩
  exact le_antisymm (Nat.le_sub_one_of_lt G.maxDegree_lt_card_verts)
    (degree_center G h ▸ G.degree_le_maxDegree c)

omit [DecidableRel G.Adj] in
theorem indep {c : V} (h : StarAt G c) (hn : 2 ≤ n) :
    G.indepNum = n - 1 := by
  classical
  let D : Finset V := univ.erase c
  have hd : D.card = n-1 := by simp [D,card_erase_of_mem (mem_univ _)]
  have hind : G.IsIndepSet (D : Set V) := by
    rw [G.isIndepSet_iff]
    intro x hx y hy _ e
    simp only [D,coe_erase,coe_univ,Set.mem_diff,Set.mem_univ,Set.mem_singleton_iff,true_and] at hx hy
    exact (by simpa [hx,hy] using (h x y).mp e : False)
  refine le_antisymm ?_ (hd ▸ hind.card_le_indepNum)
  obtain ⟨A,hA⟩ := G.exists_isNIndepSet_indepNum
  rw [← hA.card_eq, ← hd]
  by_cases hc : c ∈ A
  · have sub : A ⊆ {c} := by
      intro x hx
      rw [mem_singleton]
      by_contra hx'
      exact ((G.isIndepSet_iff).mp hA.isIndepSet) hc hx (Ne.symm hx')
        ((h c x).mpr (Or.inl ⟨rfl,hx'⟩))
    have le := card_le_card sub
    simp at le
    omega
  · apply card_le_card
    intro x hx
    exact mem_erase.mpr ⟨fun he => hc (he ▸ hx),mem_univ _⟩

omit [DecidableRel G.Adj] in
theorem outer {c : V} (h : StarAt G c) (ht : G.IsTree) (hn : 2 ≤ n) :
    AutoGraphForge370.outerNumber G = some (n-1) := by
  classical
  let D : Finset V := univ.erase c
  have hd : D.card = n-1 := by simp [D,card_erase_of_mem (mem_univ _)]
  have leaves : ∃ v, v ≠ c := by
    by_contra! all
    have e : D = ∅ := by ext x; simp [D,all x]
    simp [e] at hd
    omega
  obtain ⟨v,hv⟩ := leaves
  have outside (x : V) : x ∉ D ↔ x = c := by simp [D]
  have feasible : AutoGraphForge370.OuterDominating G D := by
    refine ⟨?_,?_⟩
    · intro x hx
      have eq := (outside x).mp hx
      subst x
      exact ⟨v,by simp [D,hv],(h c v).mpr (Or.inl ⟨rfl,hv⟩)⟩
    · have uniq (x : ↥((D : Set V)ᶜ)) : (x : V) = c := (outside x).mp x.property
      rw [connected_iff]
      refine ⟨?_,⟨⟨c,(outside c).mpr rfl⟩⟩⟩
      intro a b
      have ee : a = b := Subtype.ext ((uniq a).trans (uniq b).symm)
      subst b
      exact Reachable.rfl
  unfold AutoGraphForge370.outerNumber
  split
  · rename_i ex
    congr 1
    refine le_antisymm (Nat.find_min' ex ⟨D,feasible,hd⟩) ?_
    obtain ⟨S,hS,hcard⟩ := Nat.find_spec ex
    rw [← hcard, ← indep G h hn]
    exact AutoGraphForge370.forest_indep_le_outer_card ht.IsAcyclic S hS
  · rename_i nex
    exact False.elim (nex ⟨_,D,feasible,hd⟩)

omit [DecidableEq V] in
theorem edge_size (ht : G.IsTree) : G.edgeFinset.card = n - 1 := by
  have h := (isTree_iff_connected_and_card.mp ht).2
  rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,← G.edgeFinset_card] at h
  omega


private theorem degree_bag {c : V} (h : StarAt G c) :
    univ.val.map (fun v => G.degree v) = (n-1) ::ₘ Multiset.replicate (n-1) 1 := by
  let D : Finset V := univ.erase c
  have hnD : c ∉ D := by simp [D]
  have e : insert c D = univ := insert_erase (mem_univ c)
  have he := congrArg Finset.val e
  rw [insert_val_of_not_mem hnD] at he
  rw [← he, Multiset.map_cons, degree_center G h]
  congr 1
  have leafCard : (D.val.map (fun v => G.degree v)).card = n-1 := by
    simp [D,card_erase_of_mem (mem_univ c)]
  rw [← leafCard]
  exact Multiset.eq_replicate_card.mpr (by
    intro b hb
    obtain ⟨v,hv,rfl⟩ := Multiset.mem_map.mp hb
    exact degree_leaf G h ((mem_erase.mp (show v ∈ D from hv)).1))

open private residueAux descending hhTail descending_perm descending_sorted from Proof324

theorem star_residue {c : V} (h : StarAt G c) (hn : 2 ≤ n) :
    Graffiti324.residue G = n-1 := by
  let m := n-1
  let L := Graffiti324.degreeList G
  have hm : 1 ≤ m := by dsimp [m]; omega
  have bag : (L : Multiset ℕ) = ((m :: List.replicate m 1 : List ℕ) : Multiset ℕ) := by
    dsimp [L,Graffiti324.degreeList]
    rw [← Multiset.map_coe,Finset.coe_toList]
    change univ.val.map _ = m ::ₘ (List.replicate m 1 : Multiset ℕ)
    rw [Multiset.coe_replicate]
    convert degree_bag G h using 2; (congr 1; exact Subsingleton.elim _ _)
  have sort : descending L = m :: List.replicate m 1 := by
    apply List.eq_of_perm_of_sorted ((descending_perm L).trans (Multiset.coe_eq_coe.mp bag))
      (descending_sorted L)
    change List.Pairwise _ (_ :: _)
    rw [List.pairwise_cons]
    exact ⟨fun a ha => (List.eq_of_mem_replicate ha).symm ▸ hm,
      (List.sorted_replicate _ _).mpr (Or.inr le_rfl)⟩
  have len : L.length = m+1 := by
    dsimp [L,m]
    simp [Graffiti324.degreeList]
    omega
  have zeros : descending (List.replicate m 0) = List.replicate m 0 :=
    List.mergeSort_eq_self _ ((List.sorted_replicate _ _).mpr (Or.inr (by decide)))
  have cut : hhTail m (List.replicate m 1) = List.replicate m 0 := by
    simp [hhTail,List.take_replicate,List.drop_replicate]
  change residueAux L.length L = m
  rw [len,residueAux,sort]
  change (if m = 0 then _ else residueAux m (hhTail m (List.replicate m 1))) = m
  rw [if_neg (by omega : m ≠ 0),cut]
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  rw [hk] at zeros ⊢
  rw [residueAux,zeros]
  simp [List.replicate_succ]

theorem star_annihilation {c : V} (h : StarAt G c) (ht : G.IsTree) (hn : 2 ≤ n) :
    CubicBridges1160.annihilation G = n-1 := by
  let m := n-1
  have hm : 1 ≤ m := by dsimp [m]; omega
  have ord : n = m+1 := by dsimp [m]; omega
  have bag : ((List.replicate m 1 ++ [m] : List ℕ) : Multiset ℕ) = univ.val.map (fun v => G.degree v) := by
    rw [degree_bag G h,← Multiset.coe_add,Multiset.coe_replicate,Multiset.coe_singleton]
    rw [Multiset.add_comm,Multiset.singleton_add]
  have sorted : CubicBridges1160.ascending G = List.replicate m 1 ++ [m] := by
    apply List.eq_of_perm_of_sorted (Multiset.coe_eq_coe.mp ?_)
      (Multiset.sort_sorted _ _)
    · change List.Pairwise _ (_ ++ _)
      rw [List.pairwise_append]
      refine ⟨(List.sorted_replicate _ _).mpr (Or.inr le_rfl),by simp,?_⟩
      intro a ha b hb
      obtain rfl := List.eq_of_mem_replicate ha
      simp at hb
      rwa [hb]
    · rw [Multiset.sort_eq,bag]
  unfold CubicBridges1160.annihilation
  rw [sorted,edge_size G ht]
  change ((range (n+1)).filter
    (fun t => ((List.replicate m 1 ++ [m]).take t).sum ≤ m)).sup id = m
  refine le_antisymm (Finset.sup_le fun t ht' => ?_) (Finset.le_sup (f := id) ?_)
  · change t ≤ m
    have bounds := mem_filter.mp ht'
    have tlt := mem_range.mp bounds.1
    by_contra big
    have mt : m < t := Nat.lt_of_not_ge big
    rw [ord] at tlt
    have eq : t = m+1 := by omega
    rw [eq,List.take_of_length_le (by simp only [List.length_append,List.length_replicate,
      List.length_singleton,le_refl])] at bounds
    simp [List.sum_append,List.sum_replicate_nat] at bounds
    omega
  · apply mem_filter.mpr
    refine ⟨mem_range.mpr (by omega),?_⟩
    rw [List.take_append_of_le_length (show m ≤ (List.replicate m 1).length by rw [List.length_replicate])]
    simp [List.take_replicate,List.sum_replicate_nat]

def CoversEdges (P : Finset G.edgeSet) : Prop :=
  ∀ x, ∃ e ∈ P, x ∈ e.val

noncomputable def edgeCoverNumber : ℕ :=
  sInf {k | ∃ P : Finset G.edgeSet, P.card = k ∧ CoversEdges G P}

theorem star_edge_cover {c : V} (h : StarAt G c) (ht : G.IsTree) (hn : 2 ≤ n) :
    edgeCoverNumber G = n-1 := by
  classical
  have allCover : CoversEdges G univ := by
    intro x
    by_cases xc : x = c
    · subst x
      obtain ⟨y,hy⟩ : ∃ y, G.Adj c y := by
        by_contra! none
        have z : G.neighborFinset c = ∅ := by ext y; simp [none y]
        have sz := degree_center G h
        change (G.neighborFinset c).card = _ at sz
        simp [z] at sz
        omega
      exact ⟨⟨s(c,y),hy⟩,mem_univ _,Sym2.mem_iff.mpr (Or.inl rfl)⟩
    · exact ⟨⟨s(x,c),(h x c).mpr (Or.inr ⟨rfl,xc⟩)⟩,mem_univ _,
        Sym2.mem_iff.mpr (Or.inl rfl)⟩
  have allCard : (univ : Finset G.edgeSet).card = n-1 := by
    rw [card_univ,← G.edgeFinset_card,edge_size G ht]
  have existsSize : ({k | ∃ P : Finset G.edgeSet, P.card = k ∧ CoversEdges G P} : Set ℕ).Nonempty :=
    ⟨_,univ,allCard,allCover⟩
  refine le_antisymm (Nat.sInf_le ⟨univ,allCard,allCover⟩) ?_
  obtain ⟨P,hp,hcov⟩ := Nat.sInf_mem existsSize
  change P.card = edgeCoverNumber G at hp
  rw [← hp,← allCard]
  apply card_le_card
  intro e _
  obtain ⟨⟨x,y⟩,rep⟩ := Quot.exists_rep e.val
  change s(x,y) = e.val at rep
  have xy : G.Adj x y := show s(x,y) ∈ G.edgeSet from rep ▸ e.property
  have unique (v : V) (hv : v ≠ c) (e' : G.edgeSet) (he' : v ∈ e'.val) :
      e'.val = s(v,c) := by
    obtain ⟨⟨a,b⟩,er⟩ := Quot.exists_rep e'.val
    change s(a,b) = e'.val at er
    have ab : G.Adj a b := show s(a,b) ∈ G.edgeSet from er ▸ e'.property
    rw [← er,Sym2.mem_iff] at he'
    rcases he' with ha|hb
    · subst a
      have bc : b = c := by simpa [hv] using (h v b).mp ab
      rw [← er,bc]
    · subst b
      have ac : a = c := by simpa [hv] using (h v a).mp ab.symm
      rw [← er,ac,Sym2.eq_swap]
  rcases (h x y).mp xy with ⟨xc,yc⟩|⟨yc,xc⟩
  · obtain ⟨p,hm,had⟩ := hcov y
    have same : p = e := Subtype.ext (by rw [unique y yc p had,← rep,xc,Sym2.eq_swap])
    exact same ▸ hm
  · obtain ⟨p,hm,had⟩ := hcov x
    have same : p = e := Subtype.ext (by rw [unique x xc p had,← rep,yc])
    exact same ▸ hm

#print axioms outer
#print axioms star_residue
#print axioms star_annihilation
#print axioms star_edge_cover
end CographTree

