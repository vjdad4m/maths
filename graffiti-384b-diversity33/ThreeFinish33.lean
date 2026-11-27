import ThreeBudget33
import ThreeGeometry33

namespace Graffiti384b.ThreeChoice
open Finset SimpleGraph
open private Repair.nbr_mono Repair.nbr_add from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

/-- Rotate the omitted anchor through the triangle, sample ten exterior
vertices, and add all the unselected vertices still deficient. -/
theorem core_bound {s : V} (n : Fintype.card V=32) (ds : H.degree s=3) (ss : trianglesAt H s=3)
    (pos : ∀ w,0<trianglesAt H w) (inj : Function.Injective (trianglesAt H))
    (meet : ∀ C,H.IsNClique 5 C → ∃ x∈C,H.Adj s x) : gamma H≤15 := by
  classical
  let A := H.neighborFinset s
  let W := pool H s
  have asize : A.card=3 := (card_neighborFinset_eq_degree ..).trans ds
  have ws : W.card=28 := by
    change (insert s A)ᶜ.card=28
    rw [Finset.card_compl,card_insert_of_not_mem (H.not_mem_neighborFinset_self _),asize,n]
  have dis : Disjoint A W := disjoint_left.mpr (fun w am wm => ((pool_mem H).mp wm).2 ((H.mem_neighborFinset ..).mp am))
  have skip (w : V) (wm : w∈A∪W) (eq : trianglesAt H w=3) : False := by
    obtain rfl := inj (eq.trans ss.symm)
    exact (mem_union.mp wm).elim (H.not_mem_neighborFinset_self _) (fun h => ((pool_mem H).mp h).1 rfl)
  obtain ⟨cap,localCap,anchorCap⟩ := scores H ds ss meet
  have lim := mass H dis asize ws pos inj skip cap localCap anchorCap
  let K := W.powersetCard 10
  let fail (x : V) (k : Finset V) := failures H W k (fun w => nbr H w (A.erase x))
  let hit (x w : V) := (K.filter (fun k => w∈fail x k)).card
  have per (w : V) (wm : w∈W) : (∑ x∈A,hit x w)≤weight (nbr H w W) (nbr H w A) 0 := by
    simpa only [hit,K,fail,Nat.zero_add] using three_fibers H asize ws wm (fun _ => 0)
  have one (x : V) : (∑ k∈K,(fail x k).card)=∑ w∈W,hit x w := by
    have sub (k : Finset V) : fail x k⊆W := (filter_subset ..).trans sdiff_subset
    calc _ = ∑ k∈K,∑ w∈W,if w∈fail x k then 1 else 0 := by
           apply sum_congr rfl; intro k _; simp [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (sub k)]
         _ = _ := by rw [sum_comm]; simp [hit,sum_boole]
  have total : (∑ x∈A,∑ k∈K,(fail x k).card)=∑ w∈W,∑ x∈A,hit x w := by
    calc _ = ∑ x∈A,∑ w∈W,hit x w := sum_congr rfl (fun x _ => one x)
         _ = _ := sum_comm
  have existsGood : ∃ x∈A,∃ k∈K,(fail x k).card≤3 := by
    apply Classical.byContradiction; intro no
    have lower (x : V) (xm : x∈A) (k : Finset V) (km : k∈K) : 4≤(fail x k).card := by
      by_contra! small; exact no ⟨x,xm,k,km,by omega⟩
    have lots : (∑ _x∈A,∑ _k∈K,4)≤∑ x∈A,∑ k∈K,(fail x k).card := sum_le_sum (fun x xm => sum_le_sum (lower x xm))
    have ks : K.card=(28:ℕ).choose 10 := by rw [show K=W.powersetCard 10 from rfl,card_powersetCard,ws]
    rw [total] at lots
    simp only [sum_const,nsmul_eq_mul,asize,ks,Nat.cast_id] at lots
    have bound := (lots.trans (sum_le_sum per)).trans_lt lim
    omega
  obtain ⟨x,xm,k,km,small⟩ := existsGood
  obtain ⟨kw,ks⟩ := mem_powersetCard.mp km
  let P := A.erase x
  let D := (P∪k)∪fail x k
  have front : P∪k⊆D := subset_union_left
  have pins : P⊆D := subset_union_left.trans front
  have ps : P.card=2 := by rw [show P=A.erase x from rfl,card_erase_of_mem xm,asize]
  have dom : TwoDominates H D := by
    intro w out
    by_cases wm : w∈W
    · have wk : w∉k := fun m => out (front (mem_union_right _ m))
      have good : 2≤nbr H w k+nbr H w P := by
        apply Nat.le_of_not_gt; intro low
        exact out (mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨wm,wk⟩,low⟩))
      have add := Repair.nbr_add H w (dis.mono (erase_subset x A) kw)
      exact (show 2≤nbr H w (P∪k) by rw [show nbr H w (P∪k)=nbr H w P+nbr H w k from add,Nat.add_comm]; exact good).trans (Repair.nbr_mono H w front)
    · have all (a : V) (am : a∈P) : H.Adj w a := by
        obtain ⟨_,aa⟩ := mem_erase.mp am
        have sa := (H.mem_neighborFinset ..).mp aa
        by_cases eq : w=s
        · exact eq ▸ sa
        · have sw := Classical.byContradiction (fun (h : ¬H.Adj s w) => wm ((pool_mem H).mpr ⟨eq,h⟩))
          exact EarAnchor.full_neighbors H ds ss sw sa (fun e => out (pins (e ▸ am)))
      have sub : P⊆D.filter (H.Adj w) := fun a am => mem_filter.mpr ⟨pins am,all a am⟩
      exact ps.ge.trans (card_le_card sub)
  have size := card_union_le (P∪k) (fail x k)
  have first := card_union_le P k
  have bound : gamma H≤D.card := Nat.sInf_le ⟨_,dom,rfl⟩
  change D.card≤_ at size
  omega

end Graffiti384b.ThreeChoice
#print axioms Graffiti384b.ThreeChoice.core_bound
