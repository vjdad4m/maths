import SmallSeparator189

namespace Graffiti189LongestPath
open SimpleGraph SimpleGraph.Walk Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem two_dist_mem (hc : G.Connected) {a b c : V}
    (ne : a ≠ c) (notAdjacent : ¬G.Adj a c) (ab : G.Adj a b) (bc : G.Adj b c) :
    c ∈ DistanceTwo G a := by
  classical
  have lo := hc.one_lt_dist_of_ne_of_not_adj ne notAdjacent
  have hi := G.dist_le (Walk.cons ab (Walk.cons bc .nil))
  simp only [length_cons,length_nil] at hi
  have eq : G.dist a c=2 := by omega
  simp [DistanceTwo,eq]

omit [DecidableRel G.Adj] in
private theorem off_slots (k : ℕ) {a b s : V} (p : G.Walk a b) (S : Finset V)
    (bound : (EvenFrom G s).card ≤ k+2)
    (pin_two : 2 ≤ ((DistanceTwo G s).filter (· ∈ p.support)).card)
    (outside : ∀ x ∈ S, x ∉ p.support) (two : S ⊆ DistanceTwo G s) :
    S.card ≤ k-1 := by
  let On := (DistanceTwo G s).filter (· ∈ p.support)
  have disj : Disjoint On S :=
    disjoint_left.mpr (fun v h1 h2 => outside v h2 (mem_filter.mp h1).2)
  have sub : On ∪ S ⊆ DistanceTwo G s :=
    union_subset (filter_subset _ _) two
  have sum := card_le_card sub
  rw [card_union_of_disjoint disj] at sum
  have cap := distanceTwo_le_of_even (k+1) s bound
  change 2 ≤ On.card at pin_two
  omega

/-- Count the remaining distance-two slots at the pins. A class with at
least two porters has a universal porter, and this forces all other classes
to be singletons whose degrees violate the second-degree premise. -/
theorem close_from_fat_porter (hc : G.Connected) (k : ℕ) (k₂ : 2 ≤ k)
    (bound : ∀ x, (EvenFrom G x).card ≤ k+2)
    (degree : ∀ u v : V, u ≠ v → k+1 ≤ G.degree u ∨ k+1 ≤ G.degree v)
    {a b : V} (p : G.Walk a b)
    (F H : Finset V) (Fsize : F.card=k) (Hsize : k+1 ≤ H.card)
    (hF : ∀ s, s ∈ F ↔ s ∈ p.support ∧ ∃ x, x ∉ p.support ∧ G.Adj x s)
    (hH : ∀ x, x ∈ H ↔ x ∉ p.support)
    (unique : ∀ x∈H, ∀ s∈F, ∀ t∈F, G.Adj x s → G.Adj x t → s=t)
    (all_active : ∀ x∈H, ∃ s∈F, G.Adj x s)
    (fat_universal : ∀ s∈F, (∃ x∈H, ∃ y∈H, x≠y ∧ G.Adj x s ∧ G.Adj y s) →
      ∀ v∈H, G.Adj v s → ∀ w∈H, v≠w → G.Adj v w)
    (pin_two : ∀ s∈F, 2 ≤ ((DistanceTwo G s).filter (· ∈ p.support)).card) : False := by
  classical
  let pin (x : H) : F :=
    ⟨Classical.choose (all_active x x.prop), (Classical.choose_spec (all_active x x.prop)).1⟩
  have pinAdj (x : H) : G.Adj (x : V) (pin x : V) :=
    (Classical.choose_spec (all_active x x.prop)).2
  have pin_eq (x : H) {q : V} (qF : q ∈ F) (adj : G.Adj (x : V) q) : (pin x : V) = q :=
    unique x x.prop (pin x) (pin x).prop q qF (pinAdj x) adj
  have noninj : ¬ Function.Injective pin := by
    intro inj
    have le := Fintype.card_le_of_injective pin inj
    rw [Fintype.card_coe,Fintype.card_coe] at le
    omega
  obtain ⟨x₁,x₂,peq,xne⟩ := Function.not_injective_iff.mp noninj
  let s : F := pin x₁
  have a₁ : G.Adj (x₁ : V) (s : V) := pinAdj x₁
  have a₂ : G.Adj (x₂ : V) (s : V) := by rw [show s=pin x₂ from peq]; exact pinAdj x₂
  have nes : (x₁ : V) ≠ (x₂ : V) := fun he => xne (Subtype.ext he)
  have universal := fat_universal s s.prop
    ⟨x₁,x₁.prop,x₂,x₂.prop,nes,a₁,a₂⟩
  let O := H.filter (fun z => ¬G.Adj z s)
  have om (v : V) : v ∈ O ↔ v ∈ H ∧ ¬G.Adj v s := by simp [O]
  have sP : (s : V) ∈ p.support := ((hF s).mp s.prop).1
  have Ocap : O.card ≤ k-1 := by
    apply off_slots k p O (bound s) (pin_two s s.prop)
      (fun y hy => (hH y).mp ((om y).mp hy).1)
    intro z hz
    obtain ⟨m,n⟩ := (om z).mp hz
    have hs : (s : V) ≠ z := fun he => (hH z).mp m (he ▸ sP)
    have hx : (x₁ : V) ≠ z := fun he => n (he ▸ a₁)
    exact two_dist_mem hc hs (fun h => n h.symm) a₁.symm (universal x₁ x₁.prop a₁ z m hx)
  let target := F.erase (s : V)
  let otherH (z : O) : H := ⟨z,((om z).mp z.prop).1⟩
  let op (z : O) : target := ⟨pin (otherH z),mem_erase.mpr ⟨
    (fun he => ((om z).mp z.prop).2 (he ▸ pinAdj (otherH z))), (pin (otherH z)).prop⟩⟩
  have opSurj : Function.Surjective op := by
    intro q
    obtain ⟨qne,qF⟩ := mem_erase.mp q.prop
    obtain ⟨_,z,zoff,zq⟩ := (hF q).mp qF
    have zH := (hH z).mpr zoff
    have zO : z ∈ O := (om z).mpr ⟨zH,fun e => qne (unique z zH q qF s s.prop zq e)⟩
    exact ⟨⟨z,zO⟩,Subtype.ext (pin_eq ⟨z,zH⟩ qF zq)⟩
  have tsize : target.card = k-1 := by
    change (F.erase (s : V)).card = k-1
    rw [card_erase_of_mem s.prop,Fsize]
  have rev := Fintype.card_le_of_surjective op opSurj
  rw [Fintype.card_coe,Fintype.card_coe,tsize] at rev
  have osize : O.card = k-1 := Nat.le_antisymm Ocap rev
  have oinj := ((Fintype.bijective_iff_surjective_and_card op).mpr
    ⟨opSurj,by rw [Fintype.card_coe,Fintype.card_coe,tsize,osize]⟩).1
  have singleton (x : O) {z : V} (zH : z ∈ H) (zq : G.Adj z (op x : V)) : z = (x : V) := by
    obtain ⟨qne,qF⟩ := mem_erase.mp (op x).prop
    have zO : z ∈ O := (om z).mpr ⟨zH,fun e => qne (unique z zH (op x) qF s s.prop zq e)⟩
    have matchPin : op (⟨z,zO⟩ : O) = op x := Subtype.ext (pin_eq ⟨z,zH⟩ qF zq)
    exact congrArg (fun o : O => (o : V)) (oinj matchPin)
  let N (x : O) := (G.neighborFinset (x : V)).filter (· ∈ H)
  have hN (x : O) : (N x).card ≤ k-1 := by
    let q := op x
    have xq : G.Adj (x : V) (q : V) := pinAdj (otherH x)
    have qF := (mem_erase.mp q.prop).2
    have qP := ((hF q).mp qF).1
    apply off_slots k p (N x) (bound q) (pin_two q qF)
      (fun z hz => (hH z).mp (mem_filter.mp hz).2)
    intro z hz
    obtain ⟨zx,zH⟩ := mem_filter.mp hz
    have xz := (G.mem_neighborFinset _ _).mp zx
    have qz : (q : V) ≠ z := fun he => (hH z).mp zH (he ▸ qP)
    exact two_dist_mem hc qz (fun e => xz.ne (singleton x zH e.symm).symm) xq.symm xz
  have low (x : O) : G.degree (x : V) ≤ k := by
    let q := op x
    have xH := ((om x).mp x.prop).1
    have qo := (mem_erase.mp q.prop).2
    have xe : G.Adj (x : V) (q : V) := pinAdj (otherH x)
    have subset : G.neighborFinset (x : V) ⊆ insert (q : V) (N x) := by
      intro z hz
      by_cases zH : z ∈ H
      · exact mem_insert_of_mem (mem_filter.mpr ⟨hz,zH⟩)
      · have zP : z ∈ p.support := by
          by_contra h; exact zH ((hH z).mpr h)
        have ez := (G.mem_neighborFinset _ _).mp hz
        have zF := (hF z).mpr ⟨zP,x,(hH x).mp xH,ez⟩
        have eql := unique x xH z zF q qo ez xe
        exact mem_insert.mpr (Or.inl eql)
    have le := card_le_card subset
    rw [card_neighborFinset_eq_degree] at le
    exact le.trans ((card_insert_le _ _).trans (by have w := hN x; omega))
  by_cases large : 3 ≤ k
  · obtain ⟨u,uh,v,vh,ne⟩ := one_lt_card.mp (show 1 < O.card by omega)
    have h := degree u v ne
    have l := low ⟨u,uh⟩
    have r := low ⟨v,vh⟩
    change G.degree u ≤ k at l
    change G.degree v ≤ k at r
    omega
  · obtain ⟨u,um⟩ := card_pos.mp (show 0 < O.card by omega)
    let x : O := ⟨u,um⟩
    have uh := ((om u).mp um).1
    have una := ((om u).mp um).2
    have n₁ : (x₁ : V) ≠ u := fun he => una (he ▸ a₁)
    have n₂ : (x₂ : V) ≠ u := fun he => una (he ▸ a₂)
    have e₁ := (universal x₁ x₁.prop a₁ u uh n₁).symm
    have e₂ := (universal x₂ x₂.prop a₂ u uh n₂).symm
    have sub : {(x₁ : V),(x₂ : V)} ⊆ N x := by
      simp only [insert_subset_iff,singleton_subset_iff,N,mem_filter,mem_neighborFinset,x]
      exact ⟨⟨e₁,x₁.prop⟩,⟨e₂,x₂.prop⟩⟩
    have cnt := card_le_card sub
    have pair : ({(x₁ : V),(x₂ : V)} : Finset V).card = 2 := by simp [nes]
    rw [pair] at cnt
    have cap := hN x
    omega

#print axioms close_from_fat_porter
end Graffiti189LongestPath
