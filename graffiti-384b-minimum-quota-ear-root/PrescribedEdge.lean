import EdgeSpectrum
namespace Graffiti384b.EarRooted
open Finset SimpleGraph FiveChoice TriangleFrame SixFront Exterior PinnedColor34
open private Repair.support_sub Repair.edge_info from Repair384b
open private TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Positive triangle counts suffice; isolated vertices play no role. -/
private theorem support_positive {b x : V} (xs : x∈Repair.linkSupport G b) :
    0<trianglesAt G x := by
  obtain ⟨p,pm,xp⟩ := mem_biUnion.mp xs
  obtain ⟨sub,size,cl⟩ := Repair.edge_info G pm
  obtain ⟨y,yp,ne⟩ := exists_ne_of_one_lt_card (by omega : 1<p.card) x
  exact (TrianglePrune.triangle_iff G x).mpr ⟨b,y,((G.mem_neighborFinset ..).mp (sub xp)).symm,
    cl x xp y yp ne.symm,(G.mem_neighborFinset ..).mp (sub yp)⟩

private theorem oriented {a b : V} (ab : G.Adj a b) (pos : 0<trianglesAt G b)
    (order : trianglesAt G b<trianglesAt G a)
    (rich : ∀v,v≠a → v≠b → 0<trianglesAt G v → 2≤trianglesAt G v)
    (inj : ∀x y,x≠a → x≠b → y≠a → y≠b → 0<trianglesAt G x → 0<trianglesAt G y →
      trianglesAt G x=trianglesAt G y → x=y) :
    ∃L R : Finset V,a∈L ∧ b∈R ∧ Protected G L R := by
  classical
  have info {v : V} (vm : v∈(Repair.linkSupport G b).erase a) : v≠a ∧ v≠b ∧ 0<trianglesAt G v :=
    ⟨(mem_erase.mp vm).1,((G.mem_neighborFinset ..).mp (Repair.support_sub G b (mem_erase.mp vm).2)).ne.symm,
      support_positive G (mem_erase.mp vm).2⟩
  obtain ⟨x,xs,avoidX⟩ := other_escape G pos (fun v vm => rich v (info vm).1 (info vm).2.1 (info vm).2.2)
    (fun x xm y ym => inj x y (info xm).1 (info xm).2.1 (info ym).1 (info ym).2.1 (info xm).2.2 (info ym).2.2)
  have bx := (G.mem_neighborFinset ..).mp (Repair.support_sub G b (mem_erase.mp xs).2)
  have xa := (mem_erase.mp xs).1
  let W : Finset V := {a,x}
  let E : Finset V := {b}
  have aw : a∈W := mem_insert_self ..
  have xw : x∈W := mem_insert_of_mem (mem_singleton_self _)
  have dis : Disjoint W E := by simp [W,E,ab.ne,bx.ne.symm,ab.ne.symm,bx.ne]
  have ok (r : V) (re : r∈E) : 2≤nbr G r W := by
    obtain rfl := mem_singleton.mp re; exact two G xa.symm ab.symm bx aw xw
  have touch (r : V) (rw : r∈W) : ∃e∈E,G.Adj r e := by
    refine ⟨b,mem_singleton_self _,?_⟩
    rcases mem_insert.mp rw with rfl|rw
    · exact ab
    · obtain rfl := mem_singleton.mp rw; exact bx.symm
  have thin : NoThinPair G W E := by
    intro i j k jo _ ij ik jk
    exact Or.inl (rich j (fun eq => jo (mem_union_left _ (eq ▸ aw)))
      (fun eq => jo (mem_union_right _ (mem_singleton.mpr eq))) ((TrianglePrune.triangle_iff G j).mpr ⟨i,k,ij.symm,jk,ik⟩))
  obtain ⟨L,R,wl,er,pr⟩ := escaping_pins G dis ok touch thin (by
    intro r rw _
    have avoids : Avoids G r b := by
      rcases mem_insert.mp rw with rfl|rw
      · exact avoids_smaller G ab order
      · obtain rfl := mem_singleton.mp rw; exact avoidX
    obtain ⟨p,pm,pb⟩ := avoids
    refine ⟨p,pm,by simpa [E] using pb,?_⟩
    intro inc
    have size := (Repair.edge_info G pm).2.1
    have eq : p=W := eq_of_subset_of_card_le inc (by rw [size]; exact le_of_eq (card_pair xa.symm))
    have rr : r∈p := eq ▸ rw
    exact G.not_mem_neighborFinset_self r ((Repair.edge_info G pm).1 rr))
  exact ⟨L,R,wl aw,er (mem_singleton_self _),pr⟩

/-- A prescribed edge occurs in a protected bipartite subgraph. The endpoints have
distinct positive triangle counts; all remaining positive counts are distinct and at least two.
Coincidences across the two groups are allowed. -/
theorem prescribed_edge {a b : V} (ab : G.Adj a b) (pa : 0<trianglesAt G a) (pb : 0<trianglesAt G b)
    (ne : trianglesAt G a≠trianglesAt G b)
    (rich : ∀v,v≠a → v≠b → 0<trianglesAt G v → 2≤trianglesAt G v)
    (inj : ∀x y,x≠a → x≠b → y≠a → y≠b → 0<trianglesAt G x → 0<trianglesAt G y →
      trianglesAt G x=trianglesAt G y → x=y) :
    ∃L R : Finset V,a∈L ∧ b∈R ∧ Protected G L R := by
  rcases lt_or_gt_of_ne ne with lt|gt
  · obtain ⟨L,R,bl,ar,apart,left,right⟩ := oriented G ab.symm pa lt
      (fun v vb va => rich v va vb) (fun x y xb xa yb ya => inj x y xa xb ya yb)
    exact ⟨R,L,ar,bl,apart.symm,right,left⟩
  · exact oriented G ab pb gt rich inj

end Graffiti384b.EarRooted
#print axioms Graffiti384b.EarRooted.prescribed_edge
