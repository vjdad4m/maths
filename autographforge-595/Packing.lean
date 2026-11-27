import Blocks
import Mathlib.Logic.Equiv.Fin.Basic

namespace RegularHarmonic595
open Graffiti326 Finset

/-- Charge a matching edge to its hub if it has one, otherwise to its block. -/
def charge {n} : Vertex n → Vertex n → Hub n ⊕ Block n
  | .inl h, _ => .inl h
  | .inr _, .inl h => .inl h
  | .inr (p,_), .inr _ => .inr p

private theorem atHub {n} {x y : Vertex n} {h} (he : charge x y = .inl h) :
    x = .inl h ∨ y = .inl h := by
  cases x <;> cases y <;> simp_all [charge]

private theorem atBlock {n} {x y : Vertex n} {p} (ha : (graph n).Adj x y)
    (he : charge x y = .inr p) : (∃ a, x = .inr (p,a)) ∧ (∃ b, y = .inr (p,b)) := by
  rcases x with h | ⟨q,a⟩ <;> rcases y with j | ⟨r,b⟩ <;> simp_all [charge,graph,adjacent]

/-- Each hub can support only one pair. Each five-vertex block supports at most
two pairs entirely within it, even when other pairs meet a hub. -/
theorem matching_cap {n k} (hm : HasMatching (graph n) k) : k ≤ (n+1)*5 := by
  classical
  obtain ⟨f,hf⟩ := hm
  let c (i : Fin k) := charge (f (i,false)) (f (i,true))
  let fiber (z : Hub n ⊕ Block n) := {i : Fin k // c i = z}
  have count : k = ∑ z, Fintype.card (fiber z) := by
    simpa [fiber,Fintype.card_sigma] using (Fintype.card_congr (Equiv.sigmaFiberEquiv c)).symm
  have hubCap (h : Hub n) : Fintype.card (fiber (.inl h)) ≤ 1 := by
    have hit (i : fiber (.inl h)) : ∃ b, f (i.val,b) = .inl h := by
      rcases atHub i.property with e | e
      · exact ⟨false,e⟩
      · exact ⟨true,e⟩
    have hs : Subsingleton (fiber (.inl h)) := ⟨by
      intro i j
      obtain ⟨a,ea⟩ := hit i
      obtain ⟨b,eb⟩ := hit j
      exact Subtype.ext (Prod.mk.inj (f.injective (ea.trans eb.symm))).1⟩
    exact Fintype.card_le_one_iff_subsingleton.mpr hs
  have blockCap (p : Block n) : Fintype.card (fiber (.inr p)) ≤ 2 := by
    have hit (z : fiber (.inr p) × Bool) : ∃ j, f (z.1.val,z.2) = .inr (p,j) := by
      rcases z with ⟨i,b⟩
      obtain ⟨h₀,h₁⟩ := atBlock (hf i.val) i.property
      cases b
      · exact h₀
      · exact h₁
    let port (z : fiber (.inr p) × Bool) := (hit z).choose
    have inj : Function.Injective port := by
      rintro ⟨i,a⟩ ⟨j,b⟩ he
      have ep := congrArg (fun v : Fin 5 => (Sum.inr (p,v) : Vertex n)) he
      have e := f.injective (((hit (i,a)).choose_spec.trans ep).trans (hit (j,b)).choose_spec.symm)
      exact Prod.ext (Subtype.ext (Prod.mk.inj e).1) (Prod.mk.inj e).2
    have small := Fintype.card_le_of_injective port inj
    simp only [Fintype.card_prod,Fintype.card_bool,Fintype.card_fin] at small
    omega
  rw [count,Fintype.sum_sum_type]
  have left := sum_le_sum (s := (univ : Finset (Hub n))) (fun h _ => hubCap h)
  have right := sum_le_sum (s := (univ : Finset (Block n))) (fun p _ => blockCap p)
  simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin,
    smul_eq_mul, Nat.mul_one] at left right
  change (∑ h, Fintype.card (fiber (.inl h))) ≤ n+1 at left
  change (∑ p, Fintype.card (fiber (.inr p))) ≤ (n+1)*2*2 at right
  omega

abbrev LocalVertex := Unit ⊕ (Bool × Fin 5)
private def localEnd : Fin 5 → Bool → LocalVertex
  | 0, false => .inl ()
  | 0, true => .inr (false,0)
  | 1, false => .inr (false,1)
  | 1, true => .inr (false,2)
  | 2, false => .inr (false,3)
  | 2, true => .inr (false,4)
  | 3, false => .inr (true,0)
  | 3, true => .inr (true,2)
  | 4, false => .inr (true,1)
  | 4, true => .inr (true,3)

private def place {n} : Hub n × LocalVertex → Vertex n
  | (i,.inl _) => .inl i
  | (i,.inr (b,j)) => .inr ((i,b),j)

private theorem place_inj (n) : Function.Injective (@place n) := by
  rintro ⟨i, (u | ⟨b,j⟩)⟩ ⟨i', (u' | ⟨b',j'⟩)⟩ he <;> simp_all [place]

theorem matching_attain (n) : HasMatching (graph n) ((n+1)*5) := by
  let split : Fin ((n+1)*5) ≃ Hub n × Fin 5 := finProdFinEquiv.symm
  let endpoint (z : Fin ((n+1)*5) × Bool) :=
    place ((split z.1).1,localEnd (split z.1).2 z.2)
  have pairInj : ∀ i b j c, localEnd i b = localEnd j c → i=j ∧ b=c := by decide
  have inj : Function.Injective endpoint := by
    rintro ⟨i,b⟩ ⟨j,c⟩ he
    have ep := Prod.mk.inj (place_inj n he)
    have loc := pairInj _ _ _ _ ep.2
    exact Prod.ext (split.injective (Prod.ext ep.1 loc.1)) loc.2
  refine ⟨⟨endpoint,inj⟩,fun i => ?_⟩
  have edges (h : Hub n) (a : Fin 5) :
      (graph n).Adj (place (h,localEnd a false)) (place (h,localEnd a true)) := by
    fin_cases a <;> simp [graph,adjacent,attachment,inside,localEnd,place]
  exact edges (split i).1 (split i).2

theorem matching_exact (n) : matchingNumber (graph n) = (n+1)*5 :=
  le_antisymm (matching_cap (matchingNumber_attained _)) (matchingNumber_upper (matching_attain n))

end RegularHarmonic595
