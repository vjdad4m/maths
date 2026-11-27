import CenteredCapZ5
import RoutedK4Junction

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.CappedRegion
open Substitute CopyMimic FourRingCyclicEquivalence
universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {S : Finset V} {x : V}

/-- Given cyclic-four ordinary factors, one specified port of a 0-mod-6
cap can always take part in a centered width-(1,1,0) export. -/
theorem centered_export_at_port_z5 (A : CappedRegion G S x) (promise : CyclicUniversal.{u})
    (dvd : 6∣Fintype.card (↑(insert x S):Type u))
    {p : V} (port : A.rootAdj p) :
    ∃ b : V, p≠b ∧ A.rootAdj b ∧ Closed G (S\{p,b}) := by
  letI := A.dec
  let I := (↑(insert x S):Type u)
  let r : I := ⟨x,mem_insert_self _ _⟩
  have dom : CyclicDomain A.H := ⟨⟨A.cubic,A.conn,dvd⟩,A.small⟩
  obtain ⟨aS,ra⟩ := port
  let a : I := ⟨p,mem_insert_of_mem aS⟩
  have e : A.H.Adj r a := ra
  obtain ⟨b,ne,_,rb,⟨P,hP⟩⟩ := cyclic4_centered_pair_at_neighbor promise dom e
  have bS : b.val ∈ S := (mem_insert.mp b.property).resolve_left
    (fun h=> rb.ne (Subtype.ext h.symm))
  have mS {v : I} (hm : v ∈ univ\{r,a,b}) : v.val∈S :=
    (mem_insert.mp v.property).resolve_left (fun er=>
      (mem_sdiff.mp hm).2 (mem_insert.mpr (Or.inl (Subtype.ext er))))
  let e : I ↪ V := Function.Embedding.subtype (fun v : V => v∈insert x S)
  have hp := local_map e (fun u hu v hv adj=> A.keep u.val v.val (mS hu) (mS hv) adj) hP
  have eq : (univ\({r,a,b}:Finset I)).map e = S\{a.val,b.val} := by
    ext y
    constructor
    · intro hy
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hy
      refine mem_sdiff.mpr ⟨mS hv,?_⟩
      intro item
      rcases mem_insert.mp item with pa|pb
      · exact (mem_sdiff.mp hv).2 (mem_insert_of_mem (mem_insert.mpr (Or.inl (Subtype.ext pa))))
      · exact (mem_sdiff.mp hv).2
          (mem_insert_of_mem (mem_insert_of_mem (mem_singleton.mpr (Subtype.ext (mem_singleton.mp pb)))))
    · intro hy
      obtain ⟨sy,ny⟩ := mem_sdiff.mp hy
      refine mem_map.mpr ⟨⟨y,mem_insert_of_mem sy⟩,mem_sdiff.mpr ⟨mem_univ _,?_⟩,rfl⟩
      intro item
      simp only [mem_insert,mem_singleton] at item
      have diff : y ≠ x := fun h=>A.rootOut (h ▸ sy)
      rcases item with er|ea|eb
      · exact diff (congrArg Subtype.val er)
      · exact ny (mem_insert.mpr (Or.inl (congrArg Subtype.val ea)))
      · exact ny (mem_insert.mpr (Or.inr (mem_singleton.mpr (congrArg Subtype.val eb))))
  rw [eq] at hp
  exact ⟨b.val,fun h=>ne (Subtype.ext h),⟨bS,rb⟩,⟨_,hp⟩⟩

/-- A 0-mod-6 cyclic-four cap has a centered two-port export, without
any transitivity assumption or prescribed choice of both ports. -/
theorem centered_export_z5 (A : CappedRegion G S x) (promise : CyclicUniversal.{u})
    (dvd : 6∣Fintype.card (↑(insert x S):Type u)) :
    ∃ a b : V, a≠b ∧ A.rootAdj a ∧ A.rootAdj b ∧ Closed G (S\{a,b}) := by
  letI := A.dec
  let I := (↑(insert x S):Type u)
  let r : I := ⟨x,mem_insert_self _ _⟩
  have card : (A.H.neighborFinset r).card=3 :=
    (card_neighborFinset_eq_degree A.H r).trans (A.cubic r)
  obtain ⟨a,ha⟩ := card_pos.mp (by omega : 0<(A.H.neighborFinset r).card)
  have ra := (mem_neighborFinset A.H r a).mp ha
  have aS : a.val∈S := (mem_insert.mp a.property).resolve_left
    (fun eq=>ra.ne (Subtype.ext eq.symm))
  have pa : A.rootAdj a.val := ⟨aS,ra⟩
  obtain ⟨b,ne,pb,hb⟩ := A.centered_export_at_port_z5 promise dvd pa
  exact ⟨a.val,b,ne,pa,pb,hb⟩

#print axioms centered_export_at_port_z5
#print axioms centered_export_z5
end KelmansCactus.AtomicBridge.CappedRegion
