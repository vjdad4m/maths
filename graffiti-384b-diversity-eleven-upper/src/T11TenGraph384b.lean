import T11TenMotif384b
import Mathlib.Tactic.FinCases
import Q10AnchorNormalize384b
import Proof384b

namespace Graffiti384b.T11TenNormalize
open SimpleGraph Finset
open private Graffiti384bQ10.join Graffiti384bQ10.joinL Graffiti384bQ10.joinR
  Graffiti384bQ10.enum Graffiti384bQ10.card_sub_pred Graffiti384bQ10.card_cut
  Graffiti384bQ10.sorted_two_preds from Q10AnchorNormalize384b
set_option maxHeartbeats 3000000

section
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

theorem full_neighbors {v : V} (d : H.degree v=3) (s : trianglesAt H v=3)
    {p q : V} (vp : H.Adj v p) (vq : H.Adj v q) (ne : p≠q) : H.Adj p q := by
  let S := (H.neighborFinset v).powersetCard 2
  let T := S.filter (fun k => ∀ x∈k,∀ y∈k,x≠y → H.Adj x y)
  have st : S.card=3 := by simp only [S,card_powersetCard,card_neighborFinset_eq_degree,d]; decide
  have tt : T.card=3 := s
  have eq : T=S := eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have pair : ({p,q} : Finset V)∈S := mem_powersetCard.mpr
    ⟨insert_subset ((H.mem_neighborFinset _ _).mpr vp) (singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr vq)),card_pair ne⟩
  have all := (mem_filter.mp (show ({p,q} : Finset V)∈T from eq ▸ pair)).2
  exact all p (mem_insert_self ..) q (mem_insert_of_mem (mem_singleton_self _)) ne

end

theorem label_clique (G : SimpleGraph Label) [DecidableRel G.Adj]
    (u v : Label) (uv : u≠v) (sep : ¬G.Adj u v) (dv : G.degree v=3) :
    ∃ p : Label ≃ Label, p 0=v ∧ p 4=u ∧
      ∀ i, G.Adj v (p i) ↔ i∈clique := by
  classical
  let anchor (w : Label) := w=v ∨ w=u
  let Z := {w // ¬anchor w}
  let P : Z → Prop := fun z => G.Adj v z.val
  have dz : Fintype.card Z=8 := by
    rw [Graffiti384bQ10.card_sub_pred]
    have eq : (univ.filter fun w => ¬anchor w) = ((univ : Finset Label).erase u).erase v := by
      ext i; simp [anchor]
    rw [eq]
    simp [Finset.card_erase_of_mem,uv.symm]
  have dP : Fintype.card {z // P z}=3 := by
    rw [Graffiti384bQ10.card_cut (fun w => ¬anchor w) (G.Adj v) (G.neighborFinset v)]
    · simpa using dv
    · intro w
      rw [G.mem_neighborFinset]
      exact ⟨fun h => ⟨by rintro (rfl|rfl); exact G.loopless _ h; exact sep h.symm,h⟩,And.right⟩
  obtain ⟨zEq, zs⟩ := Graffiti384bQ10.sorted_two_preds P (fun _ => True)
  let vv : Fin 2 → {w // anchor w} := fun i =>
    if i=0 then ⟨v,Or.inl rfl⟩ else ⟨u,Or.inr rfl⟩
  have bij : Function.Bijective vv := by
    refine ⟨?_,?_⟩
    · intro i j h
      fin_cases i <;> fin_cases j
      · rfl
      · exfalso; exact uv (congrArg Subtype.val h).symm
      · exfalso; exact uv (congrArg Subtype.val h)
      · rfl
    · intro w
      rcases w.property with h|h
      · exact ⟨0,Subtype.ext h.symm⟩
      · exact ⟨1,Subtype.ext h.symm⟩
  let l := Equiv.ofBijective vv bij
  let r := (finCongr dz.symm).trans zEq
  let q : Label ≃ Label := Graffiti384bQ10.join anchor l r
  have qv : q 0=v := by
    change Graffiti384bQ10.join anchor l r (Fin.castAdd 8 (0 : Fin 2))=v
    rw [Graffiti384bQ10.joinL]
    rfl
  have qu : q 1=u := by
    change Graffiti384bQ10.join anchor l r (Fin.castAdd 8 (1 : Fin 2))=u
    rw [Graffiti384bQ10.joinL]
    rfl
  have qr (j : Label) (hj : 2≤j.val) : G.Adj v (q j) ↔ j.val<5 := by
    let t : Fin 8 := ⟨j.val-2,by have := j.isLt; omega⟩
    have eq : Fin.natAdd 2 t = j := by apply Fin.ext; change 2+(j.val-2)=j.val; omega
    rw [← eq,show q (Fin.natAdd 2 t) = (r t).val from Graffiti384bQ10.joinR anchor l r t]
    have hs := (zs (finCongr dz.symm t)).1
    rw [dP] at hs
    exact hs.trans (by change j.val-2<3 ↔ 2+(j.val-2)<5; omega)
  let f : Label → Label := ![0,2,3,4,1,5,6,7,8,9]
  have fi : Function.Injective f := by decide
  let e := Equiv.ofBijective f (Finite.injective_iff_bijective.mp fi)
  refine ⟨e.trans q,qv,qu,?_⟩
  intro j
  change G.Adj v (q (f j)) ↔ j∈clique
  fin_cases j
  · change G.Adj v (q 0) ↔ (0:Label)∈clique
    rw [qv]; exact iff_of_false (G.loopless _) (by decide)
  · exact (qr 2 (by decide)).trans (by decide)
  · exact (qr 3 (by decide)).trans (by decide)
  · exact (qr 4 (by decide)).trans (by decide)
  · change G.Adj v (q 1) ↔ (4:Label)∈clique
    rw [qu]; exact iff_of_false (fun h => sep h.symm) (by decide)
  · exact (qr 5 (by decide)).trans (by decide)
  · exact (qr 6 (by decide)).trans (by decide)
  · exact (qr 7 (by decide)).trans (by decide)
  · exact (qr 8 (by decide)).trans (by decide)
  · exact (qr 9 (by decide)).trans (by decide)

private theorem pair_filter (G : SimpleGraph Label) (a b : Label) :
    (∀ x ∈ ({a,b} : Finset Label),∀ y ∈ ({a,b} : Finset Label),x≠y→G.Adj x y) ↔
      a=b ∨ G.Adj a b := by
  constructor
  · intro h
    by_cases ab : a=b
    · exact Or.inl ab
    exact Or.inr (h _ (mem_insert_self ..) _ (mem_insert_of_mem (mem_singleton_self _)) ab)
  · rintro (rfl|h) x hx y hy hxy
    · simp only [mem_insert,mem_singleton,or_self] at hx hy
      exact (hxy (hx.trans hy.symm)).elim
    · simp only [mem_insert,mem_singleton] at hx hy
      rcases hx with rfl|rfl <;> rcases hy with rfl|rfl
      · exact (hxy rfl).elim
      · exact h
      · exact h.symm
      · exact (hxy rfl).elim

private theorem score_pair_count (G : SimpleGraph Label) [DecidableRel G.Adj]
    (u a b c : Label) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (N : G.neighborFinset u = {a,b,c}) :
    trianglesAt G u =
      (if G.Adj a b then 1 else 0)+(if G.Adj a c then 1 else 0)+(if G.Adj b c then 1 else 0) := by
  let S : Finset (Finset Label) := {{a,b},{a,c},{b,c}}
  have sa : ({a,b} : Finset Label) ≠ {a,c} := by
    intro h
    have : b∈({a,c} : Finset Label) := h ▸ (by simp : b∈({a,b}:Finset Label))
    simp [ab.symm,bc] at this
  have sb : ({a,b} : Finset Label) ≠ {b,c} := by
    intro h
    have : a∈({b,c} : Finset Label) := h ▸ (by simp : a∈({a,b}:Finset Label))
    simp [ab,ac] at this
  have sc : ({a,c} : Finset Label) ≠ {b,c} := by
    intro h
    have : a∈({b,c} : Finset Label) := h ▸ (by simp : a∈({a,c}:Finset Label))
    simp [ab,ac] at this
  have pow : (G.neighborFinset u).powersetCard 2 = S := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      simp only [S,mem_insert,mem_singleton] at hp
      rw [N]
      rcases hp with rfl|rfl|rfl
      · exact mem_powersetCard.mpr ⟨by simp [Finset.insert_subset_iff],by simp [ab]⟩
      · exact mem_powersetCard.mpr ⟨by simp [Finset.insert_subset_iff],by simp [ac]⟩
      · exact mem_powersetCard.mpr ⟨by simp [Finset.insert_subset_iff],by simp [bc]⟩
    · rw [Finset.card_powersetCard,N]
      simp [S,ab,ac,bc,sa,sb,sc]
  unfold trianglesAt
  rw [pow]
  rcases (em (G.Adj a b)) with h1|h1 <;> rcases (em (G.Adj a c)) with h2|h2 <;>
    rcases (em (G.Adj b c)) with h3|h3 <;>
    simp only [S,Finset.filter_insert,Finset.filter_singleton,pair_filter,ab,ac,bc,false_or,h1,h2,h3,ite_true,ite_false] <;> simp [sa,sb,sc]

/-- A score-two cubic has a unique missing pair in its triple; label its
missing endpoints first and its remaining neighbor last. -/
theorem cubic_two_shape (G : SimpleGraph Label) [DecidableRel G.Adj]
    (u : Label) (du : G.degree u=3) (su : trianglesAt G u=2) :
    ∃ a b c : Label, a≠b ∧ a≠c ∧ b≠c ∧ G.neighborFinset u={a,b,c} ∧
      ¬G.Adj a b ∧ G.Adj a c ∧ G.Adj b c := by
  obtain ⟨a,b,c,ab,ac,bc,N⟩ := Finset.card_eq_three.mp
    ((G.card_neighborFinset_eq_degree u).trans du)
  have s := score_pair_count G u a b c ab ac bc N
  rw [su] at s
  rcases (em (G.Adj a b)) with h1|h1 <;> rcases (em (G.Adj a c)) with h2|h2 <;>
    rcases (em (G.Adj b c)) with h3|h3 <;>
    simp [h1,h2,h3] at s
  · exact ⟨b,c,a,bc,ab.symm,ac.symm,by rw [N]; ext i; simp only [mem_insert,mem_singleton]; tauto,
      h3,h1.symm,h2.symm⟩
  · exact ⟨a,c,b,ac,ab,bc.symm,by rw [N]; ext i; simp only [mem_insert,mem_singleton]; tauto,
      h2,h1,h3.symm⟩
  · exact ⟨a,b,c,ab,ac,bc,N,h1,h2,h3⟩

end Graffiti384b.T11TenNormalize

#print axioms Graffiti384b.T11TenNormalize.label_clique
#print axioms Graffiti384b.T11TenNormalize.cubic_two_shape
