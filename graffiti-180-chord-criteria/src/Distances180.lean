import Twin180
import Pendant180

set_option warningAsError true
namespace Converse180
open Finset SimpleGraph Graffiti177 Graffiti318 Rooted180
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

noncomputable def twinRoot (r : V) (odd : Bool) : Twin V := if odd then hub else copy false r
noncomputable def twinDepth (r : V) (odd : Bool) : Twin V → ℕ :=
  Sum.elim (Sum.elim (fun v => G.dist v r + (if odd then 1 else 0))
    (fun v => G.dist v r + (if odd then 1 else 2))) (fun _ => if odd then 0 else 1)

omit [Fintype V] [DecidableEq V] in
theorem twin_layers (hc : G.Connected) (r : V) (odd : Bool) :
    (twin G r).Connected ∧ ∀ v, (twin G r).dist v (twinRoot r odd) = twinDepth G r odd v := by
  have gd {a b : V} (e : G.Adj a b) : G.dist a r ≤ G.dist b r + 1 := by
    have t := hc.dist_triangle (u:=a) (v:=b) (w:=r)
    rw [dist_eq_one_iff_adj.mpr e] at t
    omega
  have self : G.dist r r = 0 := G.dist_self
  apply layers
  · cases odd <;> simp [twinDepth,twinRoot,hub,copy]
  · rintro ((a|a)|a) ((b|b)|b) e
    all_goals cases odd <;> simp_all [twinDepth,twin] <;> simp only [dist_self] <;> omega
  · rintro ((v|v)|v) ne
    · by_cases eq : v=r
      · subst v
        cases odd
        · exact (ne rfl).elim
        · exact ⟨hub,rfl,by simp [hub,twinDepth]⟩
      · obtain ⟨w,e,d⟩ := Graffiti169.exists_predecessor G hc r v eq
        exact ⟨copy false w,e,by cases odd <;> simp [copy,twinDepth,d]⟩
    · by_cases eq : v=r
      · subst v
        exact ⟨hub,rfl,by cases odd <;> simp [hub,twinDepth]⟩
      · obtain ⟨w,e,d⟩ := Graffiti169.exists_predecessor G hc r v eq
        exact ⟨copy true w,e,by cases odd <;> simp [copy,twinDepth,d]⟩
    · cases v
      cases odd
      · exact ⟨copy false r,rfl,by simp [copy,twinDepth]⟩
      · exact (ne rfl).elim

noncomputable def parity (r : V) (odd : Bool) : Finset V := by
  classical exact univ.filter (fun v => G.dist v r % 2 = odd.toNat)

omit [DecidableEq V] in
@[simp] theorem mem_parity (r v : V) (odd : Bool) :
    v ∈ parity G r odd ↔ G.dist v r % 2 = odd.toNat := by classical simp [parity]

omit [DecidableEq V] in
theorem twin_even (hc : G.Connected) (r : V) (odd : Bool) :
    evenCount (twin G r) (twinRoot r odd) = 2*(parity G r odd).card + odd.toNat := by
  classical
  have d := (twin_layers G hc r odd).2
  have eq : (univ.filter (fun v => (twin G r).dist (twinRoot r odd) v % 2 = 0)) =
      twinSet (parity G r odd) odd := by
    ext v
    rw [mem_filter,dist_comm (u:=twinRoot r odd),d v]
    rcases v with (v|v)|v <;> cases odd <;>
      simp [twinDepth,twinSet] <;> omega
  change (univ.filter _).card = _
  rw [eq,twinSet_card]

omit [DecidableEq V] in
theorem deco_parity (hc : G.Connected) (r : V) (odd : Bool) (D : Finset V)
    (miss : Disjoint (parity G r odd) D) :
    parity (decorate G D) (.inl r) odd = (parity G r odd).disjSum univ := by
  classical
  have d := (deco_layers G hc r D).2
  ext v
  rcases v with v|v
  · simp [d]
  · have out : v.val ∉ parity G r odd := fun h => disjoint_left.mp miss h v.property
    simp only [mem_parity] at out
    simp only [mem_parity,d,Sum.elim_inr,inr_mem_disjSum,mem_univ,iff_true]
    cases odd <;> simp_all <;> omega

#print axioms twin_layers
#print axioms twin_even
#print axioms deco_parity
end Converse180
