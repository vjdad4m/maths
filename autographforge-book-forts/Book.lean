import Mathlib.Tactic.FinCases
import ChordalBasis
import DegreeBasis

namespace Book567
open Finset SimpleGraph
abbrev V (n : ℕ) := Bool ⊕ (Fin n × Fin 4)
abbrev hub {n : ℕ} (b : Bool) : V n := .inl b
abbrev site {n : ℕ} (i : Fin n) (u : Fin 4) : V n := .inr (i,u)

/-- Site 0 is a plain page, 1 a support page, and 2 and 3 its private leaves. -/
def inside (u v : Fin 4) := (u = 1 ∧ 2 ≤ v.val) ∨ (v = 1 ∧ 2 ≤ u.val)
def adjacent {n} : V n → V n → Prop
  | .inl a,.inl b => a ≠ b
  | .inl _,.inr (_,v) => v.val < 2
  | .inr (_,u),.inl _ => u.val < 2
  | .inr (i,u),.inr (j,v) => i = j ∧ inside u v

instance {n} : DecidableRel (@adjacent n) := by
  intro x y
  cases x <;> cases y <;> dsimp [adjacent,inside] <;> infer_instance

def graph (n : ℕ) : SimpleGraph (V n) where
  Adj := adjacent
  symm := by
    rintro (a|⟨i,u⟩) (b|⟨j,v⟩) h
    · exact Ne.symm h
    · exact h
    · exact h
    · exact ⟨h.1.symm,h.2.symm⟩
  loopless := by
    rintro (a|⟨i,u⟩) h
    · exact h rfl
    · exact (by unfold inside; decide : ∀ u : Fin 4, ¬ inside u u) u h.2

instance (n) : DecidableRel (graph n).Adj := inferInstanceAs (DecidableRel adjacent)

theorem order (n) : Fintype.card (V n) = 4*n+2 := by
  simp [V,Fintype.card_sum,Fintype.card_prod]; omega

theorem leaf_adj {n} (i : Fin n) {u : Fin 4} (hu : 2 ≤ u.val) (x : V n) :
    (graph n).Adj (site i u) x ↔ x = site i 1 := by
  rcases x with b|⟨j,v⟩
  · change u.val < 2 ↔ _
    simp [Nat.not_lt.mpr hu]
  · have ne : u ≠ 1 := by rintro rfl; contradiction
    simp [site,graph,adjacent,inside,ne,hu,eq_comm (a := i)]

theorem connected (n) : (graph n).Connected := by
  have reach (x : V n) : (graph n).Reachable x (hub false) := by
    rcases x with b|⟨i,u⟩
    · cases b
      · exact Reachable.rfl
      · exact (show (graph n).Adj (hub true) (hub false) from Bool.noConfusion).reachable
    · by_cases h : u.val < 2
      · exact (show (graph n).Adj (site i u) (hub false) from h).reachable
      · have e := (leaf_adj i (Nat.le_of_not_gt h) (site i 1)).mpr rfl
        exact e.reachable.trans (show (graph n).Adj (site i 1) (hub false) from (by decide : (1 : Fin 4).val < 2)).reachable
  exact ⟨fun x y => (reach x).trans (reach y).symm⟩

def rank {n} : V n → ℕ
  | .inl _ => 0
  | .inr (_,u) => if u.val < 2 then 1 else 2

theorem chordal (n) : TriangleChain.Chordal (graph n) := by
  apply TriangleChain.chordal_of_elimination _ rank
  intro x y z xy xz yz ry rz
  have hubs {a b : Bool} (ne : (hub a : V n) ≠ hub b) : (graph n).Adj (hub a) (hub b) :=
    fun e => ne (congrArg hub e)
  have top (w : V n) (h : rank w ≤ 0) : ∃ b, w = hub b := by
    rcases w with b|⟨i,u⟩
    · exact ⟨b,rfl⟩
    · simp [rank] at h; split at h <;> omega
  rcases x with b|⟨i,u⟩
  · obtain ⟨a,rfl⟩ := top y ry
    obtain ⟨c,rfl⟩ := top z rz
    exact hubs yz
  · by_cases low : u.val < 2
    · have earlier (w : V n) (adj : (graph n).Adj (site i u) w) (h : rank w ≤ rank (site i u)) :
          ∃ b, w = hub b := by
        rcases w with b|⟨j,v⟩
        · exact ⟨b,rfl⟩
        · have high : 2 ≤ v.val := adj.2.resolve_right (fun hv => (Nat.not_le.mpr low) hv.2) |>.2
          simp [rank,site,low,Nat.not_lt.mpr high] at h
      obtain ⟨a,rfl⟩ := earlier y xy ry
      obtain ⟨c,rfl⟩ := earlier z xz rz
      exact hubs yz
    · exact (yz (((leaf_adj i (Nat.le_of_not_gt low) y).mp xy).trans
        ((leaf_adj i (Nat.le_of_not_gt low) z).mp xz).symm)).elim

theorem hub_degree (n) (b : Bool) : (graph n).degree (hub b) = 2*n+1 := by
  classical
  let page : Fin n × Bool ↪ V n := ⟨fun p => site p.1 (if p.2 then 1 else 0),by
    rintro ⟨i,a⟩ ⟨j,c⟩ eq
    cases a <;> cases c <;> simp_all [site]⟩
  have nb : (graph n).neighborFinset (hub b) = insert (hub (!b)) (univ.map page) := by
    ext x
    rcases x with c|⟨i,u⟩
    · cases b <;> cases c <;> simp [graph,adjacent,hub,site,page]
    · fin_cases u <;> simp [graph,adjacent,hub,site,page,Prod.exists,Bool.exists_bool]
      decide
  have no : hub (!b) ∉ univ.map page := by simp [hub,site,page]
  change ((graph n).neighborFinset (hub b)).card = _
  rw [nb,card_insert_of_not_mem no,card_map,card_univ,Fintype.card_prod,Fintype.card_fin,
    Fintype.card_bool]
  omega

/-- In a nontrivial graph the first degree is too small. Two distinct
vertices whose degrees sum to the order already certify the second prefix. -/
theorem subTotal_two_of_pair {U : Type*} [Fintype U] (G : SimpleGraph U) [DecidableRel G.Adj]
    {u v : U} (uv : u ≠ v) (cap : Fintype.card U ≤ G.degree u + G.degree v) :
    subTotal? G = some 2 := by
  classical
  letI : Nontrivial U := ⟨u,v,uv⟩
  have hn : 2 ≤ Fintype.card U := Fintype.one_lt_card_iff_nontrivial.mpr inferInstance
  obtain ⟨x,b,l,seq,largest,rest⟩ := leaders G hn
  have h : Fintype.card U ≤ G.degree x + b := by
    by_cases eq : u = x
    · subst u; exact cap.trans (Nat.add_le_add_left (rest v uv.symm) _)
    · have := rest u eq
      have := largest v
      omega
  obtain ⟨k,hk⟩ := Nat.exists_eq_add_of_le hn
  have small := G.degree_lt_card_verts x
  unfold subTotal?
  rw [seq,hk,show 2+k+1 = 3+k by omega,List.range_add]
  simp [List.range_succ,List.find?_append,hk] at *
  omega

theorem subTotal_exact (n) : subTotal? (graph n) = some 2 := by
  apply subTotal_two_of_pair (graph n) (u := hub false) (v := hub true) (by simp [hub])
  rw [hub_degree,hub_degree,order]
  omega

end Book567
