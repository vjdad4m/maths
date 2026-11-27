import PinnedTools180
import BagCost180

set_option warningAsError true
namespace Minimal180.Substitution
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
open Classical
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B]
variable {H : SimpleGraph V} {G : SimpleGraph B} {f : V→B} {s : B→V} {r : V}

/-- An upper graph is obtained from the base by adjoining the new
root r as an adjacent true twin of its original representative. -/
structure TrueChart (H : SimpleGraph V) (G : SimpleGraph B) (f : V→B) (s : B→V) (r : V) : Prop where
  bags : Bags H G f
  sec : Function.LeftInverse f s
  out : ∀ i,s i≠r
  all : ∀ x,x=r ∨ ∃ i,s i=x
  edge : H.Adj r (s (f r))

omit [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B] in
theorem TrueChart.oldAdj (h : TrueChart H G f s r) {i j : B} : H.Adj (s i) (s j) ↔ G.Adj i j := by
  constructor
  · intro e
    have ne : f (s i)≠f (s j) := fun q => e.ne (congrArg s ((h.sec i).symm.trans (q.trans (h.sec j))))
    simpa only [h.sec _] using (h.bags.across ne).mp e
  · exact fun e => (h.bags.repHom s h.sec).map_adj e

omit [Fintype V] [DecidableEq V] [Fintype B] [DecidableEq B] in
theorem TrueChart.newAdj (h : TrueChart H G f s r) {i : B} : H.Adj r (s i) ↔ i=f r ∨ G.Adj (f r) i := by
  by_cases eq : i=f r
  · exact iff_of_true (eq ▸ h.edge) (Or.inl eq)
  · have ne : f r≠f (s i) := by rw [h.sec i]; exact fun e => eq e.symm
    simpa only [h.sec i,eq,false_or] using h.bags.across ne

theorem TrueChart.parityImage (h : TrueChart H G f s r) (gc : G.Connected) (hn : 1<Fintype.card B) :
    parity H r true=(insert (f r) (parity G (f r) true)).image s := by
  classical
  ext x
  rcases h.all x with ex|⟨i,ex⟩
  · subst x
    simp only [mem_parity,dist_self,Bool.toNat_true,Nat.zero_mod,zero_ne_one,false_iff,mem_image]
    exact fun ⟨a,_,eq⟩ => h.out a eq
  · subst x
    rw [h.sec.injective.mem_finset_image]
    by_cases eq : i=f r
    · subst i; simp [mem_parity,dist_eq_one_iff_adj.mpr h.edge.symm]
    · have d := h.bags.metric gc hn (s i) r
      simp only [h.sec i,eq,ne_eq,not_false_eq_true,if_true] at d
      simp [mem_parity,d,eq]

theorem TrueChart.marks (h : TrueChart H G f s r) (gc : G.Connected) (hn : 1<Fintype.card B)
    (I : Finset B) (ia : f r∈I) :
    let Q := parity G (f r) true
    let U := eligible I Q (f r)
    let A := I.image s
    let P := parity H r true
    A.card=I.card ∧ P.card=Q.card+1 ∧
      eligible A P r=(insert (f r) U).image s ∧
      A∩P=(insert (f r) (I∩Q)).image s := by
  classical
  intro Q U A P
  have off : f r∉Q := by simp [Q,mem_parity,dist_self]
  have pr : P=(insert (f r) Q).image s := h.parityImage gc hn
  have ra : r∉A := fun m => by obtain ⟨v,_,eq⟩ := mem_image.mp m; exact h.out v eq
  have rp : r∉P := by simp [P,mem_parity,dist_self]
  refine ⟨card_image_of_injective _ h.sec.injective,by rw [pr,card_image_of_injective _ h.sec.injective,card_insert_of_not_mem off],?_,?_⟩
  · ext x
    rcases h.all x with xr|⟨i,eq⟩
    · subst x
      simp only [eligible_iff,ra,rp,false_or,false_and,and_false,false_iff,mem_image]
      exact fun ⟨a,_,eq⟩ => h.out a eq
    · subst x
      simp only [A,pr,h.sec.injective.mem_finset_image,mem_insert,U,eligible_iff,h.out i,true_or,and_true]
      by_cases e : i=f r <;> simp [e,off,ia,h.out]
  · rw [pr]
    change I.image s∩(insert (f r) Q).image s=_
    rw [←image_inter _ _ h.sec.injective]
    apply congrArg (image s)
    ext i
    by_cases e : i=f r <;> simp [e,ia]

theorem TrueChart.full (h : TrueChart H G f s r) (U : Finset B) (off : f r∉U) :
    fullBags f ((insert (f r) U).image s)=U := by
  classical
  ext i
  rw [full_iff]
  constructor
  · intro all
    by_cases eq : i=f r
    · have rm := all r eq.symm
      obtain ⟨j,_,ex⟩ := mem_image.mp rm
      exact (h.out j ex).elim
    · exact (mem_insert.mp ((h.sec.injective.mem_finset_image).mp (all (s i) (h.sec i)))).resolve_left eq
  · intro im x ex
    rcases h.all x with xr|⟨j,eq⟩
    · exact (off (xr ▸ ex.symm ▸ im)).elim
    · subst x
      rw [h.sec j] at ex
      exact mem_image_of_mem s (mem_insert_of_mem (ex ▸ im))

#print axioms TrueChart.parityImage
#print axioms TrueChart.marks
#print axioms TrueChart.full
end Minimal180.Substitution
