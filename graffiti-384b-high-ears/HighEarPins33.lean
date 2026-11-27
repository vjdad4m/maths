import CubicSquareProfile33

namespace Graffiti384b.HighEar
open Finset SimpleGraph EarAnchor EarFrame33 CliquePivot33
open private Repair.nbr_mono Repair.isolate Repair.triangles_le_choose from Repair384b
open private CliquePivot33.isolated_degree from CliquePivot33
open private EarAnchor.sees_in_clique from CubicAnchor33
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

theorem ear_one {e : V} (de : H.degree e=2) (pos : ∀ v,0<trianglesAt H v) : trianglesAt H e=1 := by
  have cap := Repair.triangles_le_choose H e
  rw [de,Nat.choose_self] at cap; have := pos e; omega

private theorem outside_cubic {e x : V} {A B R : Finset V} (de : H.degree e=2)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    (eb : e∈B) (tight : Tight H R) (fr : Frame H A B) (xa : x∉A) (xb : x∉B)
    (xp : 2≤nbr H x A) (xq : 2≤nbr H x B) :
    ∃ u,u∉A ∧ u∉B ∧ u∉R ∧ H.degree u=3 ∧ H.Adj u x := by
  obtain ⟨u,ux,ua,ub,small,_,_⟩ := EarOnClique33.mixed_blocker H tight fr xa xb xp xq
  have ue : u≠e := fun eq => ub (eq ▸ eb)
  have one := ear_one H de pos
  have n1 := fun (h : trianglesAt H u=1) => ue (inj (h.trans one.symm))
  have lo : 3≤H.degree u := by
    by_contra! low
    have cap := Repair.triangles_le_choose H u
    have po := pos u
    have d : H.degree u=0 ∨ H.degree u=1 ∨ H.degree u=2 := by omega
    have upper : (H.degree u).choose 2≤1 := by rcases d with h|h|h <;> rw [h] <;> decide
    exact n1 (by omega)
  rw [CliquePivot33.isolated_degree H ux] at small
  by_cases adj : H.Adj u x
  · have m := (H.mem_neighborFinset _ _).mpr adj
    rw [card_erase_of_mem m,card_neighborFinset_eq_degree] at small
    by_cases ur : u∈R
    · simp [ur] at small; omega
    · simp [ur] at small
      exact ⟨u,ua,ub,ur,by omega,adj⟩
  · have m : x∉H.neighborFinset u := fun h => adj ((H.mem_neighborFinset _ _).mp h)
    rw [erase_eq_of_not_mem m,card_neighborFinset_eq_degree] at small
    omega


/-- The two–two clique coloring yields an uncredited cubic adjacent to each
of the three candidate pivots, with no score assumption on the square. -/
theorem first_pins {e a c w x : V} (de : H.degree e=2)
    (ea : H.Adj e a) (ec : H.Adj e c) (aw : H.Adj a w) (cw : H.Adj c w) (ew : e≠w) (ac : a≠c)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (an : a∉C) (cm : c∈C) (wm : w∈C)
    (xm : x∈C) (xc : x≠c) (xw : x≠w) :
    ∃ u,u∉R ∧ H.degree u=3 ∧ H.Adj u x := by
  classical
  have en : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  let K := C.erase x
  have ks : K.card=4 := by rw [show K=C.erase x from rfl,card_erase_of_mem xm,cl.2]
  have ck : c∈K := mem_erase.mpr ⟨xc.symm,cm⟩
  have wk : w∈K := mem_erase.mpr ⟨xw.symm,wm⟩
  obtain ⟨j,jk,jout⟩ := exists_mem_not_mem_of_card_lt_card
    (show ({c,w} : Finset V).card<K.card by rw [card_pair cw.ne,ks]; decide)
  have jc : j≠c ∧ j≠w := by simpa [not_or] using jout
  let P : Finset V := {c,j}
  let Q := K\P
  have pc : P⊆K := insert_subset ck (singleton_subset_iff.mpr jk)
  have qc : Q⊆K := sdiff_subset
  have ps : P.card=2 := card_pair jc.1.symm
  have qs : Q.card=2 := by rw [show Q=K\P from rfl,card_sdiff pc,ks,ps]
  have pC := pc.trans (erase_subset x C)
  have qC := qc.trans (erase_subset x C)
  have cp : c∈P := mem_insert_self ..
  have wq : w∈Q := mem_sdiff.mpr ⟨wk,by simp [P,cw.ne.symm,jc.2.symm]⟩
  have see {t : V} (tm : t∈C) {S : Finset V} (sub : S⊆C) (size : S.card=2) (off : t∉S) : 2≤nbr H t S := by
    have eq : S.filter (H.Adj t)=S := filter_true_of_mem (fun y ym => cl.1 tm (sub ym) (fun h => off (h ▸ ym)))
    simp [nbr,eq,size]
  let A := insert a P
  let B := insert e Q
  have dis : Disjoint A B := by
    apply disjoint_left.mpr; intro y ya yb
    rcases mem_insert.mp ya with rfl|yp <;> rcases mem_insert.mp yb with eq|yq
    · exact ea.ne eq.symm
    · exact an (qC yq)
    · exact en (eq ▸ pC yp)
    · exact (mem_sdiff.mp yq).2 yp
  have frame : Frame H A B := by
    refine ⟨dis,?_,?_⟩
    · intro y ya
      rcases mem_insert.mp ya with rfl|yp
      · exact PinnedColor34.two H ew ea.symm aw (mem_insert_self ..) (mem_insert_of_mem wq)
      · exact (see (pC yp) qC qs (fun m => (mem_sdiff.mp m).2 yp)).trans (Repair.nbr_mono H y (subset_insert ..))
    · intro y yb
      rcases mem_insert.mp yb with rfl|yq
      · exact PinnedColor34.two H ac ea ec (mem_insert_self ..) (mem_insert_of_mem cp)
      · exact (see (qC yq) pC ps (mem_sdiff.mp yq).2).trans (Repair.nbr_mono H y (subset_insert ..))
  have xp : x∉P := fun m => not_mem_erase x C (pc m)
  have xq : x∉Q := fun m => not_mem_erase x C (qc m)
  obtain ⟨u,_,_,ur,ud,ux⟩ := outside_cubic H de pos inj (show e∈B from mem_insert_self ..) tight frame
    (show x∉A from fun m => (mem_insert.mp m).elim (fun h => an (h ▸ xm)) xp)
    (show x∉B from fun m => (mem_insert.mp m).elim (fun h => en (h ▸ xm)) xq)
    ((see xm pC ps xp).trans (Repair.nbr_mono H x (subset_insert ..)))
    ((see xm qC qs xq).trans (Repair.nbr_mono H x (subset_insert ..)))
  exact ⟨u,ur,ud,ux⟩

/-- When one cubic covers the entire triple, the three–one coloring forces
a different uncredited cubic at each of the same pivots. -/
theorem second_pins {e a c w u x : V} (de : H.degree e=2) (du : H.degree u=3)
    (ea : H.Adj e a) (ec : H.Adj e c) (ac : H.Adj a c) (aw : H.Adj a w) (cw : H.Adj c w) (ew : e≠w)
    (pos : ∀ v,0<trianglesAt H v) (inj : Function.Injective (trianglesAt H))
    {R C : Finset V} (tight : Tight H R) (cl : H.IsNClique 5 C) (an : a∉C) (cc : c∈C) (wc : w∈C)
    (nsame : H.neighborFinset u=C\{c,w}) (xn : x∈H.neighborFinset u) :
    ∃ t,t≠u ∧ t∉R ∧ H.degree t=3 ∧ H.Adj t x := by
  classical
  let N := H.neighborFinset u
  have ns : N.card=3 := (card_neighborFinset_eq_degree ..).trans du
  have nc : N⊆C := by change H.neighborFinset u⊆C; rw [nsame]; exact sdiff_subset
  have en : e∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have un : u∉C := fun m => by have := EarAnchor.sees_in_clique H cl m; omega
  have uc : ¬H.Adj u c := fun h => (mem_sdiff.mp (show c∈C\{c,w} from nsame ▸ (H.mem_neighborFinset _ _).mpr h)).2 (mem_insert_self ..)
  have uw : ¬H.Adj u w := fun h => (mem_sdiff.mp (show w∈C\{c,w} from nsame ▸ (H.mem_neighborFinset _ _).mpr h)).2 (mem_insert_of_mem (mem_singleton_self _))
  have au : a≠u := fun h => uc (h ▸ ac)
  let K := N.erase x
  have ks : K.card=2 := by rw [show K=N.erase x from rfl,card_erase_of_mem xn,ns]
  have kn : K⊆N := erase_subset ..
  have kC := kn.trans nc
  have cN : c∉N := fun m => uc ((H.mem_neighborFinset _ _).mp m)
  have wN : w∉N := fun m => uw ((H.mem_neighborFinset _ _).mp m)
  let A := insert a (insert c K)
  let B : Finset V := {e,w,u}
  have aa : a∈A := mem_insert_self ..
  have ca : c∈A := mem_insert_of_mem (mem_insert_self ..)
  have ka : K⊆A := (subset_insert c K).trans (subset_insert ..)
  have eb : e∈B := mem_insert_self ..
  have wb : w∈B := mem_insert_of_mem (mem_insert_self ..)
  have ub : u∈B := mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _))
  have dis : Disjoint A B := by
    apply disjoint_left.mpr; intro t ma mb
    rcases (show t=e ∨ t=w ∨ t=u by simpa only [B,mem_insert,mem_singleton] using mb) with h|h|h <;> subst t
    · rcases (show e=a ∨ e=c ∨ e∈K by simpa only [A,mem_insert] using ma) with h|h|m
      · exact ea.ne h
      · exact ec.ne h
      · exact en (kC m)
    · rcases (show w=a ∨ w=c ∨ w∈K by simpa only [A,mem_insert] using ma) with h|h|m
      · exact aw.ne.symm h
      · exact cw.ne.symm h
      · exact wN (kn m)
    · rcases (show u=a ∨ u=c ∨ u∈K by simpa only [A,mem_insert] using ma) with h|h|m
      · exact au h.symm
      · exact un (h ▸ cc)
      · exact un (kC m)
  have ewu : w≠u := fun h => un (h ▸ wc)
  have ksupport (t : V) (allK : ∀ i∈K,H.Adj t i) : 2≤nbr H t A := by
    have f : K.filter (H.Adj t)=K := filter_true_of_mem allK
    have lo : 2≤nbr H t K := by simp [nbr,f,ks]
    exact lo.trans (Repair.nbr_mono H t ka)
  have frame : Frame H A B := by
    refine ⟨dis,?_,?_⟩
    · intro t m
      rcases (show t=a ∨ t=c ∨ t∈K by simpa only [A,mem_insert] using m) with rfl|rfl|tk
      · exact PinnedColor34.two H ew ea.symm aw eb wb
      · exact PinnedColor34.two H ew ec.symm cw eb wb
      · have tw : H.Adj t w := cl.1 (kC tk) wc (fun eq => wN (eq ▸ kn tk))
        exact PinnedColor34.two H ewu tw ((H.mem_neighborFinset _ _).mp (kn tk)).symm wb ub
    · intro t m
      rcases (show t=e ∨ t=w ∨ t=u by simpa only [B,mem_insert,mem_singleton] using m) with h|h|h <;> subst t
      · exact PinnedColor34.two H ac.ne ea ec aa ca
      · exact PinnedColor34.two H ac.ne aw.symm cw.symm aa ca
      · exact ksupport u (fun i m => (H.mem_neighborFinset _ _).mp (kn m))
  have xa : x∉A := by
    intro m
    rcases (show x=a ∨ x=c ∨ x∈K by simpa only [A,mem_insert] using m) with h|h|k
    · exact an (h ▸ nc xn)
    · exact cN (h ▸ xn)
    · exact not_mem_erase x N k
  have xb : x∉B := by
    intro m
    rcases (show x=e ∨ x=w ∨ x=u by simpa only [B,mem_insert,mem_singleton] using m) with h|h|h
    · exact en (h ▸ nc xn)
    · exact wN (h ▸ xn)
    · exact un (h ▸ nc xn)
  have xw := cl.1 (nc xn) wc (fun h => wN (h ▸ xn))
  obtain ⟨t,_,off,tr,dt,edge⟩ := outside_cubic H de pos inj eb tight frame xa xb
    (ksupport x (fun i im => cl.1 (nc xn) (kC im) (mem_erase.mp im).1.symm))
    (PinnedColor34.two H ewu xw ((H.mem_neighborFinset _ _).mp xn).symm wb ub)
  exact ⟨t,fun h => off (h ▸ ub),tr,dt,edge⟩

end Graffiti384b.HighEar
#print axioms Graffiti384b.HighEar.first_pins
#print axioms Graffiti384b.HighEar.second_pins
