import RankStrata384b
import PairRepair
import BatchRepair

namespace Graffiti384b.Donor
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def deficient (s : Finset V) := univ.filter (fun x => x∉s ∧ nbr G x s<2)

/-- Exact repair cost contributed by a single vertex, summed over all b-subsets
of X. F is retained in every trial. Vertices outside both sets may need repair. -/
def loss (F X : Finset V) (b : ℕ) (x : V) :=
  let m := (X.erase x).card
  let d := nbr G x (X.erase x)
  let c := nbr G x F
  if x∈F ∨ 2≤c then 0 else (m-d).choose b +
    if c=0 then d*(m-d).choose (b-1) else 0

theorem loss_exact (F X : Finset V) (dis : Disjoint F X) {b : ℕ} (pos : 0<b) (x : V) :
    ((X.powersetCard b).filter (fun k => x∈deficient G (F∪k))).card=loss G F X b x := by
  classical
  let Y := X.erase x
  let A := Y.filter (G.Adj x)
  let c := nbr G x F
  have join {k : Finset V} (ks : k⊆X) : nbr G x (F∪k)=c+nbr G x k := by
    dsimp only [c,nbr]
    rw [filter_union,card_union_of_disjoint ((dis.mono_right ks).mono (filter_subset ..) (filter_subset ..))]
  by_cases stop : x∈F ∨ 2≤c
  · have nil : (X.powersetCard b).filter (fun k => x∈deficient G (F∪k))=∅ := by
      apply eq_empty_of_forall_not_mem; intro k km
      obtain ⟨kb,v⟩ := mem_filter.mp km
      obtain ⟨outside,low⟩ := (mem_filter.mp v).2
      rw [join (mem_powersetCard.mp kb).1] at low
      exact stop.elim (fun xf => outside (mem_union_left _ xf)) (fun _ => by omega)
    rw [nil,card_empty]
    simp only [loss,if_pos (show x∈F ∨ 2≤nbr G x F from stop)]
  push_neg at stop
  let fiber (i : ℕ) := (Y.powersetCard b).filter (fun k => (k∩A).card=i)
  have hit {k : Finset V} (ky : k⊆Y) : k∩A=k.filter (G.Adj x) := by
    ext z; simp only [A,mem_inter,mem_filter]; exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,ky h.1,h.2⟩⟩
  have equiv (k : Finset V) : k∈(X.powersetCard b).filter (fun k => x∈deficient G (F∪k)) ↔
      k∈fiber 0 ∨ c=0 ∧ k∈fiber 1 := by
    constructor
    · intro km
      obtain ⟨kb,h⟩ := mem_filter.mp km
      obtain ⟨ks,sz⟩ := mem_powersetCard.mp kb
      obtain ⟨out,low⟩ := (mem_filter.mp h).2
      have ky : k⊆Y := fun z zm => mem_erase.mpr ⟨fun eq => out (mem_union_right _ (eq ▸ zm)),ks zm⟩
      have yb := mem_powersetCard.mpr ⟨ky,sz⟩
      rw [join ks] at low
      have eq : (k∩A).card=nbr G x k := congrArg card (hit ky)
      by_cases z : nbr G x k=0
      · exact Or.inl (mem_filter.mpr ⟨yb,by omega⟩)
      · exact Or.inr ⟨by omega,mem_filter.mpr ⟨yb,by omega⟩⟩
    · intro h
      have make (i : ℕ) (km : k∈fiber i) (small : c+i<2) : k∈(X.powersetCard b).filter (fun k => x∈deficient G (F∪k)) := by
        obtain ⟨kb,ct⟩ := mem_filter.mp km
        obtain ⟨ky,sz⟩ := mem_powersetCard.mp kb
        have ks := ky.trans (erase_subset x X)
        have nx : x∉k := fun m => not_mem_erase _ _ (ky m)
        rw [hit ky] at ct
        exact mem_filter.mpr ⟨mem_powersetCard.mpr ⟨ks,sz⟩,mem_filter.mpr ⟨mem_univ _,
          fun m => (mem_union.mp m).elim stop.1 nx,by rw [join ks]; change c+(k.filter (G.Adj x)).card<2; omega⟩⟩
      exact h.elim (fun hz => make 0 hz (by omega)) (fun hz => make 1 hz.2 (by omega))
  have fc (i : ℕ) (ib : i≤b) : (fiber i).card=A.card.choose i*(Y.card-A.card).choose (b-i) :=
    RankStrata.hits Y A (filter_subset ..) ib
  have z := fc 0 (by omega)
  have one := fc 1 (by omega)
  have no : ¬(x∈F ∨ 2≤nbr G x F) := fun h => h.elim stop.1 (fun n => (not_lt_of_ge n) stop.2)
  simp only [loss,if_neg no]
  change _ = (Y.card-A.card).choose b + if c=0 then A.card*(Y.card-A.card).choose (b-1) else 0
  by_cases cz : c=0
  · have eq : (X.powersetCard b).filter (fun k => x∈deficient G (F∪k))=fiber 0∪fiber 1 := by ext k; simpa [cz] using equiv k
    have d : Disjoint (fiber 0) (fiber 1) := disjoint_left.mpr (fun k k0 k1 => by have h0 := (mem_filter.mp k0).2; have h1 := (mem_filter.mp k1).2; omega)
    rw [eq,card_union_of_disjoint d,z,one]; simp [cz]
  · have eq : (X.powersetCard b).filter (fun k => x∈deficient G (F∪k))=fiber 0 := by ext k; simpa [cz] using equiv k
    rw [eq,z]; simp [cz]

theorem total_loss (F X : Finset V) (dis : Disjoint F X) {b : ℕ} (pos : 0<b) :
    (∑ k∈X.powersetCard b,(deficient G (F∪k)).card)=∑ v,loss G F X b v := by
  calc
    _ = ∑ k∈X.powersetCard b,∑ v : V,if v∈deficient G (F∪k) then 1 else 0 := by simp
    _ = _ := by rw [sum_comm]; apply sum_congr rfl; intro v _; simpa using loss_exact G F X dis pos v

end Graffiti384b.Donor
#print axioms Graffiti384b.Donor.loss_exact
#print axioms Graffiti384b.Donor.total_loss
