import ShoreEquality28
import ShoreSplitBudget28
namespace Graffiti384b.Core28
open Finset SimpleGraph JointRank
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem side_min (p : ∀ v,0<trianglesAt G v) (fi : Function.Injective (trianglesAt G))
    {k : ℕ} (n : Fintype.card V=k) (big : 0<k) (ev : k%2=0) : 6≤k := by
  let B := Icc 1 ((k-1).choose 2)
  have incl : types G⊆B := by
    intro s sm
    obtain ⟨v,_,rfl⟩ := mem_image.mp sm
    have d := G.degree_lt_card_verts v
    exact mem_Icc.mpr ⟨p v,(Repair.triangles_le_choose G v).trans (Nat.choose_le_choose 2 (by omega))⟩
  have size := card_le_card incl
  have eq : (types G).card=k := (card_image_of_injective _ fi).trans (card_univ.trans n)
  have szB : B.card=(k-1).choose 2 := by simp [B]
  rw [eq,szB] at size
  have easy : ∀ a : Fin 6,0<a.val → a.val%2=0 → (a.val-1).choose 2<a.val := by decide
  by_contra! no
  exact (Nat.not_lt_of_ge size) (easy ⟨k,no⟩ big ev)

private theorem low_on_side (n : Fintype.card V≤28) (big : 0<Fintype.card V) (ev : Fintype.card V%2=0)
    (p : ∀ v,0<trianglesAt G v) (fi : Function.Injective (trianglesAt G)) (hf : Fintype.card V≤2*gamma G) :
    ∃ v,trianglesAt G v∈Icc 1 3 := by
  by_cases cf : G.CliqueFree 5
  · obtain ⟨v,lo⟩ := small_score G _ rfl (side_min G p fi rfl big ev) n ev cf fi hf
    exact ⟨v,mem_Icc.mpr ⟨p v,by omega⟩⟩
  · unfold SimpleGraph.CliqueFree at cf
    push_neg at cf
    obtain ⟨C,cl⟩ := cf
    obtain ⟨v,_,vs⟩ := mem_image.mp (clique_scores G p fi hf cl (show 1∈Icc 1 3 by decide))
    exact ⟨v,vs ▸ (by decide : 1∈Icc 1 3)⟩

private theorem no_small_side (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (half : Fintype.card V≤2*gamma G)
    (S : Finset V) (closed : OddQuota.TriangleClosed G S) (positive : 0<S.card) (small : S.card≤14) : False := by
  classical
  let T := Sᶜ
  have cs : T.card=28-S.card := by simp [T,card_compl,n]
  have both {U : Finset V} (cl : OddQuota.TriangleClosed G U) :
      (∀ v:U,trianglesAt (shore G U) v=trianglesAt G v.val) ∧
      (∀ v:U,0<trianglesAt (shore G U) v) ∧ Function.Injective (trianglesAt (shore G U)) ∧
      Fintype.card U≤2*gamma (shore G U) ∧ U.card%2=0 := by
    obtain ⟨sc,eq⟩ := shore_data G pos fi half U cl
    exact ⟨sc,fun v => (sc v) ▸ pos v.val,fun v w same => Subtype.ext (fi ((sc v).symm.trans (same.trans (sc w)))),
      (Fintype.card_coe _).le.trans eq.ge,by omega⟩
  obtain ⟨ss,sp,si,sh,se⟩ := both closed
  obtain ⟨ts,tp,ti,th,te⟩ := both (closed_compl G closed)
  change (∀ v:T,trianglesAt (shore G T) v=trianglesAt G v.val) at ts
  have lowS := low_on_side (V:=S) (shore G S) (by rw [Fintype.card_coe]; omega)
    (by simpa only [Fintype.card_coe] using positive) (by simpa only [Fintype.card_coe] using se) sp si sh
  have lowT := low_on_side (V:=T) (shore G T) (by rw [Fintype.card_coe]; omega)
    (by rw [Fintype.card_coe]; omega) (by simpa only [Fintype.card_coe] using te) tp ti th
  have separate (u : S) (v : T) : trianglesAt (shore G S) u≠trianglesAt (shore G T) v :=
    fun eq => mem_compl.mp v.property ((fi ((ss u).symm.trans (eq.trans (ts v)))) ▸ u.property)
  have sf : (shore G S).CliqueFree 5 := by
    intro C cl
    obtain ⟨w,wm⟩ := lowT
    obtain ⟨u,_,matchScore⟩ := mem_image.mp (clique_scores _ sp si sh cl wm)
    exact separate u w matchScore
  have tf : (shore G T).CliqueFree 5 := by
    intro C cl
    obtain ⟨w,wm⟩ := lowS
    obtain ⟨u,_,matchScore⟩ := mem_image.mp (clique_scores _ tp ti th cl wm)
    exact separate w u matchScore.symm
  let r := JointRank.rank (univ:Finset V) (trianglesAt G)
  have ri : Function.Injective r := fun v w same => rank_inj univ _ fi.injOn (mem_univ v) (mem_univ w) same
  have rlo (v : V) : 1+r v≤trianglesAt G v := rank_lower _ _ fi.injOn 1 (fun w _ => pos w) (mem_univ _)
  have rr : univ.image r=range 28 := (rank_range _ _ fi.injOn).trans (by rw [card_univ,n])
  have rh (v : V) : r v<28 := mem_range.mp (rr ▸ mem_image_of_mem r (mem_univ v))
  have pay {U : Finset V} (cl : OddQuota.TriangleClosed G U) (cf : (shore G U).CliqueFree 5) (b : ℕ) :
      U.card.choose b*(U.card/2-b) ≤ ∑ i∈U.image r,fee U.card b (1+i) := by
    obtain ⟨sc,_,_,hh,_⟩ := both cl
    have up := budget (shore G U) U.card b (Fintype.card_coe _) ((Fintype.card_coe U) ▸ hh) cf
      (fun v => 1+r v.val) (fun v => by change 0<1+r v.val; omega) (fun v => by change 1+r v.val<32; have := rh v.val; omega)
      (fun v => (rlo v.val).trans_eq (sc v).symm)
    rw [sum_image ri.injOn]
    exact up.trans_eq (sum_attach U (fun v => fee U.card b (1+r v)))
  have left := pay closed sf (leftDraw S.card)
  have right := pay (U:=T) (closed_compl G closed) tf (rightDraw S.card)
  rw [cs] at right
  apply no_two_budgets S.card (side_min _ sp si (Fintype.card_coe _) positive se) small se
    (card_image_of_injective _ ri) ?_ ?_ ?_ left right
  · exact disjoint_left.mpr (by
      intro i ia ib
      obtain ⟨a,am,ea⟩ := mem_image.mp ia
      obtain ⟨b,bm,eb⟩ := mem_image.mp ib
      exact mem_compl.mp bm ((ri (ea.trans eb.symm)) ▸ am))
  · rw [←image_union,show S∪T=univ from union_compl S,rr]
  · intro i im
    obtain ⟨v,vm,rfl⟩ := mem_image.mp im
    let w : S := ⟨v,vm⟩
    have f := degree_floor (shore G S) sf w (s:=1+r v) (by omega) (by have := rh v; omega)
      ((rlo v).trans_eq (ss w).symm)
    exact f.trans_lt (((shore G S).degree_lt_card_verts w).trans_eq (Fintype.card_coe _))

/-- All 28 vertices belong to one component of the graph formed by the
triangle edges whenever the distinct positive core attains half its order. -/
theorem no_proper_shore (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt G v)
    (fi : Function.Injective (trianglesAt G)) (half : Fintype.card V≤2*gamma G)
    (S : Finset V) (closed : OddQuota.TriangleClosed G S) : S=∅ ∨ S=univ := by
  classical
  by_contra! no
  have ls := card_pos.mpr (nonempty_iff_ne_empty.mpr no.1)
  have cs := card_compl S
  have lt : S.card<Fintype.card V := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,no.2⟩)
  by_cases le : S.card≤14
  · exact no_small_side G n pos fi half S closed ls le
  · exact no_small_side G n pos fi half Sᶜ (closed_compl G closed) (by omega) (by omega)

end Graffiti384b.Core28
#print axioms Graffiti384b.Core28.no_proper_shore
