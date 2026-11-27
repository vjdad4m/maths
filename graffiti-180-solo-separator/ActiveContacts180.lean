import TwoActive180
import RelativeColor180

set_option warningAsError true
namespace Minimal180.PairRepair
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Substitution Transversals
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

def DropCheck (G : SimpleGraph V) (a b : V) (K S : Finset V) (c : V→Bool) (t : Bool) : Prop :=
  ∃ x∈S,x∉K ∧ RelativeCheck G (S.erase x) a b c t

/-- Check only reachability and contact color equality in the two
surviving active components. The same fixed coloring suffices throughout. -/
theorem active_contacts_iff (G : SimpleGraph V) (gc : G.Connected) (hn : 1<Fintype.card V)
    (r : V) (p : Bool) (A : Finset V) (ai : Indep G A) (a b : V) (ab : a≠b) (na : ¬G.Adj a b)
    (bi : TwoColor G (univ\{a,b})) (am : a∈A) (pm : a∈parity G r p) (deg : G.degree a=4)
    (two : allowance G r p A=2) (C D O : Finset V) (h : TwoRegions G a b C D O)
    (c : V→Bool) (cp : ProperOn G (univ\{a,b}) c) (lc : MixedAt G a C c) (rc : MixedAt G a D c) :
    Protected G r p A ↔ ∃ t : Bool,DropCheck G a b (A∩insert r (parity G r p)) C c t ∧
      DropCheck G a b (A∩insert r (parity G r p)) D c t := by
  classical
  let R := univ\({a,b}:Finset V)
  let K := A∩insert r (parity G r p)
  have ao : a∉R := fun m => (mem_sdiff.mp m).2 (mem_insert_self ..)
  have bo : b∉R := fun m => (mem_sdiff.mp m).2 (mem_insert_of_mem (mem_singleton_self _))
  have cs : C⊆R := by change C⊆univ\({a,b}:Finset V);rw [h.partition];exact subset_union_left.trans subset_union_left
  have ds : D⊆R := by change D⊆univ\({a,b}:Finset V);rw [h.partition];exact subset_union_right.trans subset_union_left
  have res (S : Finset V) (sub : S⊆R) : ProperOn G S c := fun x xm y ym => cp x (sub xm) y (sub ym)
  have rule (S : Finset V) (sub : S⊆R) (t : Bool) : DropColor G a b K S t ↔ DropCheck G a b K S c t := by
    have step (x : V) := terminal_iff_contacts G a b ab na (S.erase x)
      (fun m => ao (sub (mem_of_mem_erase m))) (fun m => bo (sub (mem_of_mem_erase m))) c
      (res _ ((erase_subset ..).trans sub)) t
    exact ⟨fun ⟨x,xm,xk,d⟩ => ⟨x,xm,xk,(step x).mp d⟩,fun ⟨x,xm,xk,d⟩ => ⟨x,xm,xk,(step x).mpr d⟩⟩
  rw [two_active_iff G gc hn r p A ai a b ab na bi am pm deg two C D O h
    ((mixed_iff G a C c (fun m => ao (cs m)) (res C cs)).mp lc)
    ((mixed_iff G a D c (fun m => ao (ds m)) (res D ds)).mp rc)]
  exact exists_congr (fun t => and_congr (rule C cs t) (rule D ds t))

#print axioms active_contacts_iff
end Minimal180.PairRepair
