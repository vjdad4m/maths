import CreditProfile31
namespace Graffiti384b.EarCredit
open SimpleGraph Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace Ledger
variable {e : V} {r : V→ℕ} (L : Ledger G e r)

include L in
private theorem line (v : V) (vm : v∈(pins G e)ᶜ) (seen : 0<nbr G v (pins G e)) :
    let p := (cubics G).card
    let d := G.degree v
    let g := credit G p (pins G e) r v
    (d≤6 → gap p<g) ∧ (p=0 → d≤7 → 2116296≤g) ∧ (p=0 → d≤9 → 739024≤g) ∧
    (p=1 → 218790≤g) ∧ (p=1 → d≤7 → 1007760≤g) ∧ (p=1 → r v<25 → 388960≤g) := by
  dsimp only
  have j := L.valid v vm; unfold m at j
  have f := L.few
  have b := ((table ⟨_,show (cubics G).card<2 by omega⟩).1 ⟨r v,by omega⟩
    ⟨min (G.degree v) 10,by omega⟩ (L.tests v vm).1 (L.tests v vm).2).2.2
  rw [credit,if_pos seen]
  exact ⟨fun h => b.1 (le_trans (min_le_left ..) h),fun p h => b.2.1 p (le_trans (min_le_left ..) h),
    fun p h => b.2.2.1 p (le_trans (min_le_left ..) h),b.2.2.2.1,
    fun p h => b.2.2.2.2.1 p (le_trans (min_le_left ..) h),b.2.2.2.2.2⟩

private theorem out {v : V} (de : G.degree e=2) (ev : G.Adj e v) :
    v∈(pins G e)ᶜ ∧ 0<nbr G v (pins G e) := by
  refine ⟨mem_compl.mpr (fun m => (mem_insert.mp m).elim ev.ne.symm (fun h => nonadjacent G de h ev.symm)),?_⟩
  exact card_pos.mpr ⟨e,mem_filter.mpr ⟨mem_insert_self ..,ev.symm⟩⟩

include L in
theorem degree_sum {a b : V} (de : G.degree e=2) (ea : G.Adj e a) (eb : G.Adj e b) (ab : a≠b) :
    7≤G.degree a ∧ 7≤G.degree b ∧ 16≤G.degree a+G.degree b := by
  classical
  let p := (cubics G).card
  let pay := credit G p (pins G e) r
  obtain ⟨am,ap⟩ := out de ea
  obtain ⟨bm,bp⟩ := out de eb
  have qa := L.line a am ap; have qb := L.line b bm bp
  dsimp only at qa qb
  have sub : ({a,b}:Finset V)⊆(pins G e)ᶜ := insert_subset am (singleton_subset_iff.mpr bm)
  have q := (sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le (pay _))).trans L.total
  change (∑ v∈({a,b}:Finset V),pay v)≤gap p at q
  rw [sum_pair ab] at q
  change credit G (cubics G).card (pins G e) r a+credit G (cubics G).card (pins G e) r b≤gap (cubics G).card at q
  have da : 7≤G.degree a := by by_contra! h; have := qa.1 (by omega); omega
  have db : 7≤G.degree b := by by_contra! h; have := qb.1 (by omega); omega
  refine ⟨da,db,?_⟩
  by_contra! low
  have f := L.few
  rcases (show (cubics G).card=0 ∨ (cubics G).card=1 by omega) with z|o
  · have qa7 := qa.2.1 z; have qb7 := qb.2.1 z
    have qa9 := qa.2.2.1 z (by omega); have qb9 := qb.2.2.1 z (by omega)
    rw [show gap (cubics G).card=2734013 by rw [z]; rfl] at q
    rcases (show G.degree a≤7 ∨ G.degree b≤7 by omega) with h|h
    · have := qa7 h; omega
    · have := qb7 h; omega
  · have qa7 := qa.2.2.2.2.1 o; have qb7 := qb.2.2.2.2.1 o
    have qa0 := qa.2.2.2.1 o; have qb0 := qb.2.2.2.1 o
    rw [show gap (cubics G).card=1193398 by rw [o]; rfl] at q
    rcases (show G.degree a≤7 ∨ G.degree b≤7 by omega) with h|h
    · have := qa7 h; omega
    · have := qb7 h; omega

include L in
/-- The five neighbor incidences of two disjoint simplicial centers
cannot be assigned to five distinct vertices within the credit budget. -/
theorem meets {s : V} (sm : s∈cubics G) (de : G.degree e=2) :
    ∃ v,G.Adj e v ∧ G.Adj s v := by
  classical
  let W := (pins G e)ᶜ
  let A := G.neighborFinset e ∪ G.neighborFinset s
  have po := card_pos.mpr ⟨s,sm⟩; have f := L.few
  have one : (cubics G).card=1 := by omega
  have ds := (mem_filter.mp sm).2.1
  by_contra! no
  have dis : Disjoint (G.neighborFinset e) (G.neighborFinset s) := disjoint_left.mpr
    (fun v a b => no v ((G.mem_neighborFinset ..).mp a) ((G.mem_neighborFinset ..).mp b))
  have size : A.card=5 := by rw [show A=_∪_ from rfl,card_union_of_disjoint dis,
    card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,de,ds]
  have ins : A⊆W := by
    intro v m; rcases mem_union.mp m with em|sn
    · exact (out de ((G.mem_neighborFinset ..).mp em)).1
    · have sv := (G.mem_neighborFinset ..).mp sn
      apply mem_compl.mpr; intro vm; rcases mem_insert.mp vm with ve|vl
      · exact nonadjacent G de sm (ve ▸ sv)
      · exact sv.ne (card_le_one.mp f s sm v vl)
  have seen (v : V) (vm : v∈A) : 0<nbr G v (pins G e) := by
    rcases mem_union.mp vm with em|sn
    · exact (out de ((G.mem_neighborFinset ..).mp em)).2
    · exact card_pos.mpr ⟨s,mem_filter.mpr ⟨mem_insert_of_mem sm,((G.mem_neighborFinset ..).mp sn).symm⟩⟩
  let B := A.filter (fun v => 25≤r v)
  have bs : B⊆A := filter_subset ..
  have image : B.image r⊆Icc 25 27 := by
    intro i im; obtain ⟨v,vm,rfl⟩ := mem_image.mp im
    have h := L.valid v (ins (bs vm)); rw [one] at h; change r v<28 at h
    exact mem_Icc.mpr ⟨(mem_filter.mp vm).2,by omega⟩
  have szB := card_le_card image
  rw [card_image_of_injOn (L.injective.mono (show (B:Set V)⊆W from bs.trans ins))] at szB
  change B.card≤3 at szB
  let pay := credit G (cubics G).card (pins G e) r
  have onB := sum_le_sum (s:=B) (f:=fun _ => 218790) (g:=pay) (fun v vm =>
    (L.line v (ins (bs vm)) (seen v (bs vm))).2.2.2.1 one)
  have rest := sum_le_sum (s:=A\B) (f:=fun _ => 388960) (g:=pay) (fun v vm => by
    obtain ⟨am,bm⟩ := mem_sdiff.mp vm
    exact (L.line v (ins am) (seen v am)).2.2.2.2.2 one (by
      by_contra! hi; exact bm (mem_filter.mpr ⟨am,hi⟩)))
  have up := (sum_le_sum_of_subset_of_nonneg ins (fun _ _ _ => Nat.zero_le (pay _))).trans L.total
  have part := sum_sdiff bs (f:=pay)
  rw [sum_const,nsmul_eq_mul,Nat.cast_id] at onB rest
  rw [card_sdiff bs,size] at rest
  change (∑ v∈A,pay v)≤gap (cubics G).card at up
  rw [one] at up; change (∑ v∈A,pay v)≤1193398 at up
  omega

end Ledger
end Graffiti384b.EarCredit
#print axioms Graffiti384b.EarCredit.Ledger.degree_sum
#print axioms Graffiti384b.EarCredit.Ledger.meets
