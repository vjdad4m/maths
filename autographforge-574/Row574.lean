import Bound
import FamilyGraph

namespace EulerDom574
open Finset SimpleGraph TriangleMatching1078 AutoGraphForge378 Graffiti326
variable {n : ℕ}

/-- Each displayed core pair is an edge. Every graph edge touches cores
from only one pair, so it can dominate at most one displayed pair edge. -/
private def pairEdge (i : Key n) : (graph n).edgeSet :=
  ⟨s(Sum.inl (i,false),Sum.inl (i,true)),rfl⟩

private theorem same_group (e : (graph n).edgeSet) {x y : Core n}
    (hx : Sum.inl x ∈ e.val) (hy : Sum.inl y ∈ e.val) : x.1=y.1 := by
  by_contra diff
  have ne : (Sum.inl x : Vtx n) ≠ Sum.inl y := fun eq => diff (congrArg Prod.fst (Sum.inl.inj eq))
  have h := e.property
  rw [(Sym2.mem_and_mem_iff ne).mp ⟨hx,hy⟩] at h
  change y = mate x at h
  exact diff ((congrArg Prod.fst h).symm)

theorem line_lower : n+2 ≤ lineDomination (graph n) := by
  classical
  obtain ⟨D,sz,hD⟩ := line_attained (graph n)
  have chooseEdge (i : Key n) : ∃ e : ↥D, ∃ b : Bool, Sum.inl (i,b) ∈ e.val.val := by
    obtain ⟨e,mem,v,ve,vp⟩ := (dominates_iff _ D).mp hD (pairEdge i)
    rcases Sym2.mem_iff.mp vp with rfl|rfl
    · exact ⟨⟨e,mem⟩,false,ve⟩
    · exact ⟨⟨e,mem⟩,true,ve⟩
  choose pick side hit using chooseEdge
  have inj : Function.Injective pick := by
    intro i j eq
    exact same_group (pick i).val (hit i) (eq ▸ hit j)
  simpa [sz] using Fintype.card_le_of_injective pick inj

theorem paired : HasMaximalMatching (graph n) (n+2) := by
  let f : Key n × Bool ↪ Vtx n := ⟨Sum.inl,Sum.inl_injective⟩
  have mem (x : Core n) : Sum.inl x ∈ support f :=
    (Graffiti326.mem_support f).mpr ⟨x.1,x.2,rfl⟩
  refine ⟨f,fun _ => rfl,?_⟩
  rintro (x|o) hx (y|p) hy
  · exact (hx (mem x)).elim
  · exact (hx (mem x)).elim
  · exact (hy (mem y)).elim
  · exact id

theorem matching_values : lineDomination (graph n) = n+2 ∧ minMaximalMatching (graph n) = n+2 := by
  have upperM : minMaximalMatching (graph n) ≤ n+2 := Nat.sInf_le paired
  have cmp := lineDomination_le_matching (graph n)
  have lower := @line_lower n
  omega

/-- Omitting endpoints in distinct pairs forces the entire associated family
of subdivision vertices into a dominating set. -/
theorem domination_lower : 2*(n+2) - 1 ≤ domination (graph n) := by
  classical
  obtain ⟨S,sizeS,dom⟩ := attained (graph n)
  by_contra! small
  have omitted : ∃ x : Core n, Sum.inl x ∉ S := by
    by_contra! all
    let f (x : Core n) : ↥S := ⟨Sum.inl x,all x⟩
    have inj : Function.Injective f := fun a b eq => Sum.inl.inj (congrArg Subtype.val eq)
    have h := Fintype.card_le_of_injective f inj
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_coe] at h
    omega
  obtain ⟨x,hx⟩ := omitted
  have required (y : Core n) (neq : x.1≠y.1) : Sum.inl y ∈ S := by
    by_contra miss
    let p : Cross n := ⟨(x,y),neq⟩
    let vertex (t : Fin (2*(n+2))) : Vtx n := .inr (.inr (p,t))
    have must (t) : vertex t ∈ S := by
      rcases dom (vertex t) with mem|⟨w,hw,adjw⟩
      · exact mem
      · rcases w with c|o
        · rcases adjw with e|e
          · change c=x at e
            exact (hx (e ▸ hw)).elim
          · change c=y at e
            exact (miss (e ▸ hw)).elim
        · exact adjw.elim
    let f (t) : ↥S := ⟨vertex t,must t⟩
    have inj : Function.Injective f := by
      intro a b eq
      exact (Prod.mk.inj (Sum.inr.inj (Sum.inr.inj (congrArg Subtype.val eq)))).2
    have h := Fintype.card_le_of_injective f inj
    simp only [Fintype.card_fin,Fintype.card_coe] at h
    omega
  let T : Finset (Vtx n) := (((univ : Finset (Key n)).erase x.1) ×ˢ (univ : Finset Bool)).map
    ⟨Sum.inl, Sum.inl_injective⟩
  have sub : T ⊆ S := by
    intro v hv
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hv
    exact required y ((mem_erase.mp (mem_product.mp hy).1).1.symm)
  have count : T.card = 2*(n+2)-2 := by
    simp [T,card_erase_of_mem (mem_univ x.1)]
    omega
  have eq : T = S := eq_of_subset_of_card_le sub (by omega)
  obtain ⟨w,hw,adjw⟩ := (dom (Sum.inl x)).resolve_left hx
  rw [← eq] at hw
  obtain ⟨y,hy,rfl⟩ := mem_map.mp hw
  change y=mate x at adjw
  exact (mem_erase.mp (mem_product.mp hy).1).1 (show y.1 = (mate x).1 from congrArg Prod.fst adjw)

theorem min_degree (v : Vtx n) : 2 ≤ (graph n).degree v := by
  rcases v with x|o
  · obtain ⟨t,h⟩ := core_degree x
    omega
  · rw [outside_degree]

/-- Every k≥2 occurs, with domination 2k−1 and both edge optima k. -/
theorem family (n : ℕ) : 2 ≤ Fintype.card (Vtx n) ∧ (graph n).Connected ∧
    (∀ v, Even ((graph n).degree v)) ∧ TriangleFree (graph n) ∧
    domination (graph n) = 2*(n+2)-1 ∧ lineDomination (graph n) = n+2 ∧
    minMaximalMatching (graph n) = n+2 := by
  obtain ⟨src,matching⟩ := @matching_values n
  have upperBound := upper (graph n) min_degree
  have lower := @domination_lower n
  exact ⟨nontrivial,connected,all_even,triangle_free,by omega,src,matching⟩

theorem row574_false : ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    2 ≤ Fintype.card V → G.Connected → (∀ v, Even (G.degree v)) → TriangleFree G →
    domination G ≤ lineDomination G) := by
  intro claim
  obtain ⟨hn,hc,he,ht,hg,hs,_⟩ := family 0
  have h := claim _ _ hn hc he ht
  omega

/-- Every nontrivial connected Eulerian graph satisfies the replacement bound. -/
theorem eulerian_upper {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : 2 ≤ Fintype.card V) (conn : G.Connected) (even : ∀ v, Even (G.degree v)) :
    domination G + 1 ≤ 2 * lineDomination G := by
  letI : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp order
  apply upper
  intro v
  have pos : 0 < G.degree v := by
    apply (G.degree_pos_iff_exists_adj v).mpr
    obtain ⟨w,diff⟩ := exists_ne v
    obtain ⟨walk⟩ := conn.preconnected v w
    cases walk with
    | nil => exact (diff rfl).elim
    | cons e _ => exact ⟨_,e⟩
  obtain ⟨t,ht⟩ := even v
  omega

#print axioms eulerian_upper
#print axioms upper
#print axioms matching_values
#print axioms family
#print axioms row574_false
end EulerDom574
