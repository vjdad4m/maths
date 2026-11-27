import HighEarSwitch33

namespace Graffiti384b.HighEar
open Finset SimpleGraph OneEar CliquePivot33 EarOnClique33
open private Repair.isolate Repair.triangles_le_choose from Repair384b
open private CliquePivot33.isolated_degree from CliquePivot33
open private EarAnchor.sees_in_clique from CubicAnchor33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Remove all three edges of the ear triangle and isolate the chosen pivot. -/
def bypass (e a c x : V) : SimpleGraph V := Repair.isolate (opened H {e,a,c}) x

private theorem nonEar {t e : V} (de : H.degree e=2) (te : t≠e)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H)) : 3≤H.degree t := by
  apply Nat.le_of_not_gt; intro sm
  have rg : H.degree t=0 ∨ H.degree t=1 ∨ H.degree t=2 := by omega
  have cap := Repair.triangles_le_choose H t
  have ub : (H.degree t).choose 2≤1 := by rcases rg with h|h|h <;> rw [h] <;> decide
  have := pos t
  exact te (inj ((show trianglesAt H t=1 by omega).trans (ear_one H de pos).symm))

/-- Any clique pivot missing all uncredited cubics must leave an alternative
path between the ear endpoints. The path avoids the pivot and the ear edges. -/
theorem pivot_route {e a c x : V} (de : H.degree e=2) (da : 4≤H.degree a) (dc : 4≤H.degree c)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (both : ¬(a∈C ∧ c∈C))
    (xm : x∈C) (xa : x≠a) (xc : x≠c) (safe : ∀ t,H.degree t=3 → t∉R → ¬H.Adj t x) :
    (bypass H e a c x).Reachable a c := by
  classical
  let E : Finset V := {e,a,c}
  let F := opened H E
  let J := Repair.isolate F x
  let K := C.erase x
  have en : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have xe : x≠e := fun h => en (h ▸ xm)
  have es : H.neighborFinset e={a,c} := (eq_of_subset_of_card_le
    (insert_subset ((H.mem_neighborFinset _ _).mpr ea) (singleton_subset_iff.mpr ((H.mem_neighborFinset _ _).mpr ec)))
    (by rw [card_pair ac.ne,card_neighborFinset_eq_degree,de])).symm
  have cardE : E.card=3 := by simp [E,ea.ne,ec.ne,ac.ne]
  have ie (y : V) (edge : J.Adj e y) : False := by
    have m := (H.mem_neighborFinset _ _).mpr edge.1.1
    rw [es] at m
    exact edge.1.2 ⟨mem_insert_self ..,mem_insert_of_mem m⟩
  have adjK {i j : V} (ik : i∈K) (jk : j∈K) (ne : i≠j) : J.Adj i j := by
    obtain ⟨ix,im⟩ := mem_erase.mp ik
    obtain ⟨jx,jm⟩ := mem_erase.mp jk
    refine ⟨⟨cl.1 im jm ne,?_⟩,ix,jx⟩
    rintro ⟨iE,jE⟩
    have classify {t : V} (m : t∈E) (tc : t∈C) : t=a ∨ t=c :=
      (show t=e ∨ t=a ∨ t=c by simpa only [E,mem_insert,mem_singleton] using m).resolve_left (fun eq => en (eq ▸ tc))
    rcases classify iE im with h|h <;> rcases classify jE jm with g|g
    · exact ne (h.trans g.symm)
    · exact both ⟨h ▸ im,g ▸ jm⟩
    · exact both ⟨g ▸ jm,h ▸ im⟩
    · exact ne (h.trans g.symm)
  have rootpos {t : V} (tm : t∈E) (tx : t≠x) (four : 4≤H.degree t) : 0<J.degree t := by
    apply Nat.pos_of_ne_zero; intro zero
    have none : J.neighborFinset t=∅ := card_eq_zero.mp ((card_neighborFinset_eq_degree ..).trans zero)
    have sub : H.neighborFinset t⊆insert x (E.erase t) := by
      intro y ym; have ty := (H.mem_neighborFinset _ _).mp ym
      by_cases eq : y=x
      · exact eq ▸ mem_insert_self ..
      by_cases yE : y∈E
      · exact mem_insert_of_mem (mem_erase.mpr ⟨ty.ne.symm,yE⟩)
      have edge : J.Adj t y := ⟨⟨ty,fun h => yE h.2⟩,tx,eq⟩
      exact (Finset.not_mem_empty y (none ▸ (J.mem_neighborFinset _ _).mpr edge)).elim
    have low := card_le_card sub
    have hi := card_insert_le x (E.erase t)
    rw [card_neighborFinset_eq_degree] at low; rw [card_erase_of_mem tm,cardE] at hi; omega
  have regular (t : V) (te : t≠e) (ta : t≠a) (tc : t≠c) (tx : t≠x) :
      3≤J.degree t+2*(if t∈R then 1 else 0) := by
    have off : t∉E := by simp [E,te,ta,tc]
    have same : F.neighborFinset t=H.neighborFinset t := by ext y; simp [F,opened,off]
    have deg := nonEar H de te pos inj
    rw [show J.degree t=((F.neighborFinset t).erase x).card from CliquePivot33.isolated_degree F tx,same]
    by_cases edge : H.Adj t x
    · rw [card_erase_of_mem ((H.mem_neighborFinset _ _).mpr edge),card_neighborFinset_eq_degree]
      by_cases tr : t∈R
      · simp [tr]; omega
      · have ne : H.degree t≠3 := fun d => safe t d tr edge
        simp [tr]; omega
    · rw [erase_eq_of_not_mem (fun m => edge ((H.mem_neighborFinset _ _).mp m)),card_neighborFinset_eq_degree]; omega
  apply Classical.byContradiction; intro separated
  exact switch_cut H J ea ec ac.ne xe xa xc (fun _ _ h => h.1.1) ie (fun _ h => h.2.1 rfl) separated
    ⟨fun _ i _ j ne => adjK i j ne,by rw [show K=C.erase x from rfl,card_erase_of_mem xm,cl.2]⟩
    (fun m => en (erase_subset _ _ m)) (not_mem_erase x C)
    (fun y ym => cl.1 xm (erase_subset _ _ ym) (mem_erase.mp ym).1.symm)
    (rootpos (by simp [E]) xa.symm da) (rootpos (by simp [E]) xc.symm dc) regular tight

/-- With less than both cubic scores available, every five-clique contains
a pivot away from the endpoints which the alternative path can avoid. -/
theorem thin_route {e a c : V} (de : H.degree e=2) (da : 4≤H.degree a) (dc : 4≤H.degree c)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (lack : ¬Available H R) :
    additional H e a c=∅ ∧ ∃ x∈C,x≠a ∧ x≠c ∧ (∀ t,H.degree t=3 → t∉R → ¬H.Adj t x) ∧
      (bypass H e a c x).Reachable a c := by
  classical
  have empty : additional H e a c=∅ := eq_empty_of_forall_not_mem (by
    intro w m; obtain ⟨we,aw,cw⟩ := (additional_mem H).mp m
    exact lack (shared_requires_both H de ea ec ac aw cw we pos inj tight cl))
  have en : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have both : ¬(a∈C ∧ c∈C) := by
    rintro ⟨am,cm⟩
    obtain ⟨w,wm,off⟩ := exists_mem_not_mem_of_card_lt_card (show ({a,c} : Finset V).card<C.card by rw [card_pair ac.ne,cl.2]; decide)
    have ⟨wa,wc⟩ := (show w≠a ∧ w≠c by simpa [not_or] using off)
    have m : w∈additional H e a c := (additional_mem H).mpr ⟨fun h => en (h ▸ wm),cl.1 am wm wa.symm,cl.1 cm wm wc.symm⟩
    rw [empty] at m; exact Finset.not_mem_empty _ m
  let b := if a∈C then a else c
  let K := C.erase b
  have sz : 4≤K.card := by
    by_cases bc : b∈C
    · rw [show K=C.erase b from rfl,card_erase_of_mem bc,cl.2]
    · rw [show K=C.erase b from rfl,erase_eq_of_not_mem bc,cl.2]; decide
  have endpoints {x : V} (xm : x∈K) : x≠a ∧ x≠c := by
    obtain ⟨xb,mc⟩ := mem_erase.mp xm
    by_cases am : a∈C
    · rw [show b=a by simp [b,am]] at xb; exact ⟨xb,fun h => both ⟨am,h ▸ mc⟩⟩
    · rw [show b=c by simp [b,am]] at xb; exact ⟨fun h => am (h ▸ mc),xb⟩
  have need : ∃ x∈K,∀ t,H.degree t=3 → t∉R → ¬H.Adj t x := by
    by_cases any : ∃ u,H.degree u=3 ∧ u∉R
    · obtain ⟨u,du,ur⟩ := any
      obtain ⟨x,xm,xu⟩ := exists_mem_not_mem_of_card_lt_card
        (show (H.neighborFinset u).card<K.card by rw [card_neighborFinset_eq_degree,du]; omega)
      refine ⟨x,xm,?_⟩; intro t dt tr edge
      have tu : t≠u := fun h => xu ((H.mem_neighborFinset _ _).mpr (h ▸ edge))
      have diff : trianglesAt H t≠trianglesAt H u := fun h => tu (inj h)
      apply lack
      rcases cubic_scores H de du pos inj with us|us
      · exact ⟨u,t,du,us,ur,dt,by have := cubic_scores H de dt pos inj; omega,tr⟩
      · exact ⟨t,u,dt,by have := cubic_scores H de dt pos inj; omega,tr,du,us,ur⟩
    · obtain ⟨x,xm⟩ := card_pos.mp (show 0<K.card by omega)
      exact ⟨x,xm,fun t dt tr => (any ⟨t,dt,tr⟩).elim⟩
  obtain ⟨x,xk,safe⟩ := need
  have xc := erase_subset b C xk
  have h := endpoints xk
  exact ⟨empty,x,xc,h.1,h.2,safe,pivot_route H de da dc ea ec ac pos inj tight cl both xc h.1 h.2 safe⟩

end Graffiti384b.HighEar
#print axioms Graffiti384b.HighEar.pivot_route
#print axioms Graffiti384b.HighEar.thin_route
