import PrescribedEdge
namespace Graffiti384b.EarRooted
open Finset SimpleGraph Exterior
open private Repair.isolate Repair.nbr_mono Repair.full_nbr Repair.omit_set from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A vertex can count in both omission sets if it sees an always-retained neighbor
and two vertices on prescribed opposite shores of the graph with its incident edges removed. -/
theorem shared_omission {S : Finset V} {e z a b : V} (es : e∈S) (zs : z∉S)
    (ez : G.Adj e z) (ea : G.Adj e a) (eb : G.Adj e b) (az : a≠z) (bz : b≠z)
    {P Q : Finset V} (ap : a∈P) (bq : b∈Q) (pins : Protected (Repair.isolate G e) P Q)
    (free : ∀v∈S,v≠e → v∉P → v∉Q → 3≤(Repair.isolate G e).degree v) :
    gamma G≤Fintype.card V-(S.card+2)/2 := by
  classical
  let H := Repair.isolate G e
  obtain ⟨A,pa,qb,la,rb⟩ := PinnedColor34.cut H P Q pins.1
  let T := S.erase e
  have coversL (v : V) (vt : v∈T) (va : v∈A) : 2≤nbr H v Aᶜ := by
    by_cases vp : v∈P
    · exact (pins.2.1 v vp).trans (Repair.nbr_mono H v qb)
    have deg := free v (mem_erase.mp vt).2 (mem_erase.mp vt).1 vp (fun vq => mem_compl.mp (qb vq) va)
    have side := la v va vp
    have sum := Repair.full_nbr H v A
    change 3≤H.degree v at deg; omega
  have coversR (v : V) (vt : v∈T) (va : v∉A) : 2≤nbr H v A := by
    by_cases vq : v∈Q
    · exact (pins.2.2 v vq).trans (Repair.nbr_mono H v pa)
    have deg := free v (mem_erase.mp vt).2 (mem_erase.mp vt).1 (fun vp => va (pa vp)) vq
    have side := rb v (mem_compl.mpr va) vq
    have sum := Repair.full_nbr H v A
    change 3≤H.degree v at deg; omega
  have omitSide (C O : Finset V) {w : V} (os : O⊆T) (d : Disjoint C O) (wc : w∈C)
      (wz : w≠z) (ew : G.Adj e w) (ok : ∀v∈O,2≤nbr H v C) :
      gamma G≤Fintype.card V-(O.card+1) := by
    have en : e∉O := fun em => (mem_erase.mp (os em)).1 rfl
    have keepz : z∈(insert e O)ᶜ := mem_compl.mpr (fun m => (mem_insert.mp m).elim ez.ne.symm (fun zo => zs (mem_erase.mp (os zo)).2))
    have keepw : w∈(insert e O)ᶜ := mem_compl.mpr (fun m => (mem_insert.mp m).elim ew.ne.symm (disjoint_left.mp d wc))
    have le := Repair.omit_set G (insert e O) (by
      intro v vm
      rcases mem_insert.mp vm with rfl|vo
      · exact PinnedColor34.two G wz ew ez keepw keepz
      · apply (ok v vo).trans (card_le_card ?_)
        intro y ym
        obtain ⟨yc,vy⟩ := mem_filter.mp ym
        exact mem_filter.mpr ⟨mem_compl.mpr (fun m => (mem_insert.mp m).elim vy.2.2 (disjoint_left.mp d yc)),vy.1⟩)
    rwa [card_insert_of_not_mem en] at le
  have l := omitSide Aᶜ (T∩A) inter_subset_left
    (disjoint_compl_left.mono_right inter_subset_right) (qb bq) bz eb
    (fun v vm => coversL v (mem_inter.mp vm).1 (mem_inter.mp vm).2)
  have r := omitSide A (T\A) sdiff_subset (disjoint_left.mpr (fun _ va vr => (mem_sdiff.mp vr).2 va))
    (pa ap) az ea (fun v vm => coversR v (mem_sdiff.mp vm).1 (mem_sdiff.mp vm).2)
  have counts := card_sdiff_add_card_inter T A
  have tsize : T.card=S.card-1 := card_erase_of_mem es
  have cap := card_le_univ S
  have positive := card_pos.mpr ⟨e,es⟩
  omega

end Graffiti384b.EarRooted
#print axioms Graffiti384b.EarRooted.shared_omission
