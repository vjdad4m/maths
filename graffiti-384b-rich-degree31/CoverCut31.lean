import CreditFinish31

namespace Graffiti384b.Cover31
open Finset SimpleGraph
open private Repair.isolate Repair.iso_nbr Repair.full_nbr Repair.nbr_mono Repair.omit_set from Repair384b
open private CliquePivot33.isolated_degree from CliquePivot33
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem shared {x : V} (xh : x∈high G) {P Q : Finset V} (dis : Disjoint P Q)
    (xp : x∉P) (xq : x∉Q) (px : 2≤nbr G x P) (qx : 2≤nbr G x Q)
    (pinnedP : ∀ v∈P,2≤nbr G v Q) (pinnedQ : ∀ v∈Q,2≤nbr G v P)
    (free : ∀ v∈high G,v≠x → v∉P → v∉Q → 3≤(Repair.isolate G x).degree v)
    (t : (types G).card=31) (h : (high G).card=30) : gamma G≤bound G := by
  classical
  let J := Repair.isolate G x
  obtain ⟨A,pa,qb,la,rb⟩ := PinnedColor34.cut J P Q dis
  let L := (high G).filter (·∈A)
  let R := (high G).filter (·∉A)
  have left : Aᶜ.erase x⊆(insert x L)ᶜ := by
    intro w m
    obtain ⟨wx,wa⟩ := mem_erase.mp m
    exact mem_compl.mpr (fun z => (mem_insert.mp z).elim wx (fun l => mem_compl.mp wa (mem_filter.mp l).2))
  have right : A.erase x⊆(insert x R)ᶜ := by
    intro w m
    obtain ⟨wx,wa⟩ := mem_erase.mp m
    exact mem_compl.mpr (fun z => (mem_insert.mp z).elim wx (fun r => (mem_filter.mp r).2 wa))
  have pa' : P⊆A.erase x := fun v vp => mem_erase.mpr ⟨fun eq => xp (eq ▸ vp),pa vp⟩
  have qb' : Q⊆Aᶜ.erase x := fun v vq => mem_erase.mpr ⟨fun eq => xq (eq ▸ vq),qb vq⟩
  have lo := Repair.omit_set G (insert x L) (by
    intro v vm
    by_cases vx : v=x
    · subst v; exact qx.trans (Repair.nbr_mono G _ (qb'.trans left))
    obtain ⟨vh,va⟩ := mem_filter.mp (mem_of_mem_insert_of_ne vm vx : v∈L)
    by_cases vp : v∈P
    · exact (pinnedP _ vp).trans (Repair.nbr_mono G _ (qb'.trans left))
    have deg := free v vh vx vp (fun z => mem_compl.mp (qb z) va)
    have tot := Repair.full_nbr J v A
    have l := la v va vp
    apply le_trans _ (Repair.nbr_mono G _ left)
    rw [← Repair.iso_nbr G vx Aᶜ]
    change 3≤J.degree v at deg
    change 2≤nbr J v Aᶜ
    omega)
  have ro := Repair.omit_set G (insert x R) (by
    intro v vm
    by_cases vx : v=x
    · subst v; exact px.trans (Repair.nbr_mono G _ (pa'.trans right))
    obtain ⟨vh,va⟩ := mem_filter.mp (mem_of_mem_insert_of_ne vm vx : v∈R)
    by_cases vq : v∈Q
    · exact (pinnedQ _ vq).trans (Repair.nbr_mono G _ (pa'.trans right))
    have deg := free v vh vx (fun z => va (pa z)) vq
    have tot := Repair.full_nbr J v A
    have r := rb v (mem_compl.mpr va) vq
    apply le_trans _ (Repair.nbr_mono G _ right)
    rw [← Repair.iso_nbr G vx A]
    change 3≤J.degree v at deg
    change 2≤nbr J v A
    omega)
  have sum : L.card+R.card=(high G).card := filter_card_add_filter_neg_card_eq_card ..
  unfold bound; rw [t]
  by_cases xa : x∈A
  · rw [insert_eq_of_mem (show x∈L from mem_filter.mpr ⟨xh,xa⟩)] at lo
    rw [card_insert_of_not_mem (show x∉R from fun z => (mem_filter.mp z).2 xa)] at ro
    omega
  · rw [card_insert_of_not_mem (show x∉L from fun z => xa (mem_filter.mp z).2)] at lo
    rw [insert_eq_of_mem (show x∈R from mem_filter.mpr ⟨xh,xa⟩)] at ro
    omega

/-- Omit a clique pivot from both colors and retain every low-degree vertex in both.
Any exterior cubic adjacent to the pivot can be pinned opposite a common pair. -/
theorem paired (t : (types G).card=31) (h : (high G).card=30)
    {C P : Finset V} {x : V} (cl : G.IsNClique 5 C) (xc : x∈C)
    (pc : P⊆C.erase x) (two : P.card=2)
    (protect : ∀ v,v∉C → G.degree v=3 → G.Adj v x → 2≤nbr G v P) : gamma G≤bound G := by
  classical
  let Q := C.erase x\P
  let E := (univ : Finset V).filter (fun v => v∉C ∧ G.degree v=3 ∧ G.Adj v x)
  have qsize : Q.card=2 := by rw [show Q=C.erase x\P from rfl,card_sdiff pc,card_erase_of_mem xc,cl.2,two]
  have qc : Q⊆C.erase x := sdiff_subset
  have pC := pc.trans (erase_subset _ _)
  have qC := qc.trans (erase_subset _ _)
  have see {v : V} (vc : v∈C) {D : Finset V} (dc : D⊆C) (vd : v∉D) (dz : D.card=2) :
      2≤nbr G v D := by
    have eq : D.filter (G.Adj v)=D := filter_true_of_mem
      (fun w wm => cl.1 vc (dc wm) (fun e => vd (e ▸ wm)))
    simp only [nbr,eq,dz,le_rfl]
  have xp : x∉P := fun m => not_mem_erase _ _ (pc m)
  have xq : x∉Q := fun m => not_mem_erase _ _ (qc m)
  have xe : x∉E := fun m => (mem_filter.mp m).2.1 xc
  have dis : Disjoint P (Q∪E) := disjoint_left.mpr (by
    intro v vm m
    exact (mem_union.mp m).elim (fun z => (mem_sdiff.mp z).2 vm) (fun z => (mem_filter.mp z).2.1 (pC vm)))
  have ng : C.erase x⊆G.neighborFinset x := fun v vm => (G.mem_neighborFinset _ _).mpr
    (cl.1 xc (mem_erase.mp vm).2 (mem_erase.mp vm).1.symm)
  have deg := card_le_card ng
  rw [card_erase_of_mem xc,cl.2,card_neighborFinset_eq_degree] at deg
  apply shared G (mem_filter.mpr ⟨mem_univ _,by omega⟩) dis xp (fun m => (mem_union.mp m).elim xq xe)
    (see xc pC xp two) ((see xc qC xq qsize).trans (Repair.nbr_mono G _ subset_union_left)) _ _ _ t h
  · intro v vm
    exact (see (pC vm) qC (fun q => (mem_sdiff.mp q).2 vm) qsize).trans (Repair.nbr_mono G _ subset_union_left)
  · intro v vm
    rcases mem_union.mp vm with vq|ve
    · exact see (qC vq) pC (mem_sdiff.mp vq).2 two
    · obtain ⟨vc,d,a⟩ := (mem_filter.mp ve).2
      exact protect _ vc d a
  · intro v vh vx vp vq
    have vc : v∉C := fun m => vq (mem_union_left _ (mem_sdiff.mpr ⟨mem_erase.mpr ⟨vx,m⟩,vp⟩))
    rw [CliquePivot33.isolated_degree G vx]
    have min3 : 3≤G.degree v := (mem_filter.mp vh).2
    by_cases adj : G.Adj v x
    · rw [card_erase_of_mem ((G.mem_neighborFinset _ _).mpr adj),card_neighborFinset_eq_degree]
      have not3 : G.degree v≠3 := fun eq => vq (mem_union_right _ (mem_filter.mpr ⟨mem_univ _,vc,eq,adj⟩))
      omega
    · rwa [erase_eq_of_not_mem (fun m => adj ((G.mem_neighborFinset _ _).mp m)),card_neighborFinset_eq_degree]

end Graffiti384b.Cover31
#print axioms Graffiti384b.Cover31.paired
