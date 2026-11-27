import Book
import PowerBasis

namespace Book567
open SimpleGraph Finset AutoGraphPowerBurning

/-- A power-dominating seed must hit the closed neighborhood of every
pair of distinct vertices with the same open neighborhood. -/
theorem hit_twins {U : Type*} (G : SimpleGraph U) {a b : U} (ne : a ≠ b)
    (twins : ∀ w, G.Adj a w ↔ G.Adj b w) (S : Finset U) (observed : Observed G S a) :
    ∃ w ∈ S, w = a ∨ w = b ∨ G.Adj a w := by
  classical
  by_contra! missed
  have exclude {v} (h : Observed G S v) : v ≠ a ∧ v ≠ b := by
    induction h with
    | root hv => exact ⟨(missed _ hv).1,(missed _ hv).2.1⟩
    | neighbor hw e =>
      exact ⟨fun eq => (missed _ hw).2.2 (eq ▸ e),
        fun eq => (missed _ hw).2.2 ((twins _).mpr (eq ▸ e))⟩
    | @force v w e _ _ _ ih =>
      constructor
      · rintro rfl
        exact (ih b ((twins w).mp e).symm ne.symm).2 rfl
      · rintro rfl
        exact (ih a ((twins w).mpr e).symm ne).1 rfl
  exact (exclude observed).1 rfl

/-- The plain pages and the hubs form one region. Each support with its two
leaves forms another. These regions receive distinct compulsory seeds. -/
def region {n} : V n → Option (Fin n)
  | .inl _ => none
  | .inr (i,u) => if u = 0 then none else some i

theorem power_exact (n : ℕ) (hn : 2 ≤ n) : power (graph n) = n+1 := by
  classical
  let G := graph n
  let sizes := {k : ℕ | ∃ S : Finset (V n), k = S.card ∧ ∀ v, Observed G S v}
  have all : sizes.Nonempty := ⟨_,univ,rfl,fun v => .root (mem_univ v)⟩
  obtain ⟨S,cost,full⟩ := Nat.sInf_mem all
  change power G = S.card at cost
  have cover : S.image region = univ := by
    apply eq_univ_of_forall
    rintro (_|i)
    · let i : Fin n := ⟨0,by omega⟩
      let j : Fin n := ⟨1,by omega⟩
      have ne : site i 0 ≠ site j 0 := by simp [site,i,j,Fin.ext_iff]
      have twin (w : V n) : G.Adj (site i 0) w ↔ G.Adj (site j 0) w := by
        rcases w with b|⟨a,u⟩ <;> simp [G,graph,adjacent,inside,site]
      obtain ⟨w,hw,h⟩ := hit_twins G ne twin S (full _)
      refine mem_image.mpr ⟨w,hw,?_⟩
      rcases h with rfl|rfl|h
      · rfl
      · rfl
      · rcases w with b|⟨a,u⟩
        · rfl
        · simp [G,site,graph,adjacent,inside] at h
    · have ne : site i 2 ≠ site i 3 := by simp [site]
      have twin (w : V n) : G.Adj (site i 2) w ↔ G.Adj (site i 3) w :=
        (leaf_adj i (by decide : 2 ≤ (2 : Fin 4).val) w).trans
          (leaf_adj i (by decide : 2 ≤ (3 : Fin 4).val) w).symm
      obtain ⟨w,hw,h⟩ := hit_twins G ne twin S (full _)
      refine mem_image.mpr ⟨w,hw,?_⟩
      rcases h with rfl|rfl|h
      · rfl
      · rfl
      · rw [(leaf_adj i (by decide) w).mp h]
        rfl
  have lo := card_image_le (f := region) (s := S)
  rw [cover,card_univ,Fintype.card_option,Fintype.card_fin] at lo
  let emb : Fin n ↪ V n := ⟨fun i => site i 1,fun _ _ e => (Prod.mk.inj (Sum.inr.inj e)).1⟩
  let D := insert (hub false) (univ.map emb)
  have seeds (i : Fin n) : site i 1 ∈ D := mem_insert_of_mem (mem_map.mpr ⟨i,mem_univ _,rfl⟩)
  have good : ∀ v, Observed G D v := by
    rintro (b|⟨i,u⟩)
    · cases b
      · exact .root (mem_insert_self _ _)
      · exact .neighbor (mem_insert_self _ _) (show G.Adj (hub true) (hub false) from Bool.noConfusion)
    · by_cases hp : u.val < 2
      · exact .neighbor (mem_insert_self _ _) (show G.Adj (site i u) (hub false) from hp)
      · exact .neighbor (seeds i) ((leaf_adj i (Nat.le_of_not_gt hp) _).mpr rfl)
  have card : D.card = n+1 := by simp [D,emb,site,hub]
  have hi : power G ≤ D.card := Nat.sInf_le (s := sizes) ⟨D,rfl,good⟩
  change power G = n+1
  omega

/-- Row 567 has unbounded additive error at the minimum numerical sub-total
domination value for nontrivial simple graphs. -/
theorem family567 (n : ℕ) (hn : 2 ≤ n) :
    2 ≤ Fintype.card (V n) ∧ TriangleChain.Chordal (graph n) ∧ (graph n).Connected ∧
    subTotal? (graph n) = some 2 ∧ power (graph n) = n+1 ∧ ¬ power (graph n) ≤ 2 :=
  ⟨by rw [order]; omega,chordal n,connected n,subTotal_exact n,power_exact n hn,
    by rw [power_exact n hn]; omega⟩

#print axioms hit_twins
#print axioms subTotal_two_of_pair
#print axioms power_exact
#print axioms family567
end Book567
