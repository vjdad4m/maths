import SquareCapFactor

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteTinyEarCore
open SquareCap (FactorOn IsTile)
variable {V : Type*} [DecidableEq V]

private theorem tile_of_path {G : SimpleGraph V} {x y z : V}
    (xy : G.Adj x y) (yz : G.Adj y z) (xz : x≠z) : IsTile G ({x,y,z}:Finset V) := by
  refine ⟨by simp [xy.ne,yz.ne,xz], y,by simp,?_⟩
  intro w wm wy
  simp only [mem_insert,mem_singleton] at wm
  rcases wm with rfl|rfl|rfl
  · exact xy.symm
  · contradiction
  · exact yz

private theorem extend_tile {G : SimpleGraph V} {S T : Finset V}
    (base : FactorOn G S) (tile : IsTile G T) (d : Disjoint S T) :
    FactorOn G (S∪T) := by
  obtain ⟨P,pt,pd,pc⟩ := base
  have compat {A : Finset V} (hp : A∈P) : Disjoint A T :=
    disjoint_left.mpr fun v vm vt=>disjoint_left.mp d
      (pc ▸ mem_biUnion.mpr ⟨A,hp,vm⟩) vt
  refine ⟨insert T P,?_,?_,?_⟩
  · intro A am
    rcases mem_insert.mp am with rfl|hp
    · exact tile
    · exact pt A hp
  · intro A am B bm ab
    rcases mem_insert.mp am with rfl|hp <;> rcases mem_insert.mp bm with rfl|hq
    · contradiction
    · exact (compat hq).symm
    · exact compat hp
    · exact pd A hp B hq ab
  · ext v
    constructor
    · intro vm
      obtain ⟨A,am,av⟩ := mem_biUnion.mp vm
      rcases mem_insert.mp am with rfl|hp
      · exact mem_union_right _ av
      · exact mem_union_left _ (pc ▸ mem_biUnion.mpr ⟨A,hp,av⟩)
    · intro vm
      rcases mem_union.mp vm with hp|hq
      · obtain ⟨A,am,av⟩ := mem_biUnion.mp (pc.symm ▸ hp)
        exact mem_biUnion.mpr ⟨A,mem_insert_of_mem am,av⟩
      · exact mem_biUnion.mpr ⟨T,mem_insert_self _ _,hq⟩

private theorem lift_for_oriented_tile {G : SimpleGraph V} {S T : Finset V}
    (base : FactorOn G (S\T)) {a b z l c r : V}
    (tabz : T={a,b,z}) (ts : T⊆S) (ab : a≠b) (az : a≠z)
    (bz : G.Adj b z) (al : G.Adj a l) (lc : G.Adj l c)
    (cr : G.Adj c r) (rb : G.Adj r b) (lr : l≠r)
    (lo : l∉S) (co : c∉S) (ro : r∉S) :
    FactorOn G (S∪({l,c,r}:Finset V)) := by
  have ap : a∈S := ts (by simp [tabz])
  have bp : b∈S := ts (by simp [tabz])
  have zp : z∈S := ts (by simp [tabz])
  have aco : a≠c := fun e=>co (e ▸ ap)
  have rzo : r≠z := fun e=>ro (e.symm ▸ zp)
  let U : Finset V := {a,l,c}
  let W : Finset V := {r,b,z}
  have d1 : Disjoint (S\T) U := by
    rw [disjoint_left]
    intro v vm vu
    simp only [U,mem_insert,mem_singleton] at vu
    rcases vu with rfl|rfl|rfl
    · exact (mem_sdiff.mp vm).2 (by simp [tabz])
    · exact lo (mem_sdiff.mp vm).1
    · exact co (mem_sdiff.mp vm).1
  have d2 : Disjoint ((S\T)∪U) W := by
    rw [disjoint_left]
    intro v vm vw
    have nei : v∉S\T := by
      intro hv
      simp only [W,mem_insert,mem_singleton] at vw
      rcases vw with rfl|rfl|rfl
      · exact ro (mem_sdiff.mp hv).1
      · exact (mem_sdiff.mp hv).2 (by simp [tabz])
      · exact (mem_sdiff.mp hv).2 (by simp [tabz])
    have uv := (mem_union.mp vm).resolve_left nei
    simp only [U,W,mem_insert,mem_singleton] at uv vw
    rcases uv with rfl|rfl|rfl <;> rcases vw with e|e|e
    · exact ro (e ▸ ap)
    · exact ab e
    · exact az e
    · exact lr e
    · exact lo (e.symm ▸ bp)
    · exact lo (e.symm ▸ zp)
    · exact cr.ne e
    · exact co (e.symm ▸ bp)
    · exact co (e.symm ▸ zp)
  have h1 := extend_tile base (tile_of_path al lc aco) d1
  have h2 := extend_tile h1 (tile_of_path rb bz rzo) d2
  have cover : ((S\T)∪U)∪W=S∪({l,c,r}:Finset V) := by
    ext v
    simp only [U,W,tabz,mem_union,mem_sdiff,mem_insert,mem_singleton]
    constructor
    · intro h
      rcases h with ((h|e|e|e)|e|e|e)
      · exact Or.inl h.1
      · exact Or.inl (e.symm ▸ ap)
      · exact Or.inr (Or.inl e)
      · exact Or.inr (Or.inr (Or.inl e))
      · exact Or.inr (Or.inr (Or.inr e))
      · exact Or.inl (e.symm ▸ bp)
      · exact Or.inl (e.symm ▸ zp)
    · intro h
      rcases h with h|e|e|e
      · by_cases em : v=a∨v=b∨v=z
        · rcases em with ea|eb|ez
          · exact Or.inl (Or.inr (Or.inl ea))
          · exact Or.inr (Or.inr (Or.inl eb))
          · exact Or.inr (Or.inr (Or.inr ez))
        · exact Or.inl (Or.inl ⟨h,em⟩)
      · exact Or.inl (Or.inr (Or.inr (Or.inl e)))
      · exact Or.inl (Or.inr (Or.inr (Or.inr e)))
      · exact Or.inr (Or.inl e)
  rwa [cover] at h2

private theorem bad_tile_shape {G H : SimpleGraph V} {S T : Finset V} {a b : V}
    (ab : a≠b) (ts : T⊆S)
    (keep : ∀ x∈S,∀ y∈S,H.Adj x y →
      G.Adj x y ∨ (x=a∧y=b) ∨ (x=b∧y=a))
    (tile : IsTile H T) (bad : ¬IsTile G T) :
    ∃ z, z≠a∧z≠b∧T={a,b,z}∧(G.Adj a z ∨ G.Adj b z) := by
  obtain ⟨n,m,mm,star⟩ := tile
  have witness : ∃ k∈T,k≠m∧¬G.Adj m k := by
    by_contra! absent
    exact bad ⟨n,m,mm,absent⟩
  obtain ⟨k,km,kn,edge⟩ := witness
  have exc := (keep m (ts mm) k (ts km) (star k km kn)).resolve_left edge
  have am : a∈T := exc.elim (fun h=>h.1 ▸ mm) (fun h=>h.2 ▸ km)
  have bm : b∈T := exc.elim (fun h=>h.2 ▸ km) (fun h=>h.1 ▸ mm)
  have one : ((T.erase a).erase b).card=1 := by
    rw [card_erase_of_mem (mem_erase.mpr ⟨ab.symm,bm⟩),card_erase_of_mem am,n]
  obtain ⟨z,ze⟩ := card_eq_one.mp one
  have zm : z∈(T.erase a).erase b := by simp [ze]
  obtain ⟨zb,za,zt⟩ := by simpa only [mem_erase,and_assoc] using zm
  have shape : T={a,b,z} := by
    have inj : ({a,b,z}:Finset V)⊆T := by
      intro j jm
      simp only [mem_insert,mem_singleton] at jm
      rcases jm with rfl|rfl|rfl <;> assumption
    apply (Finset.eq_of_subset_of_card_le inj ?_).symm
    simp [n,ab,za.symm,zb.symm]
  refine ⟨z,za,zb,shape,?_⟩
  rcases exc with ⟨me,_⟩|⟨me,_⟩
  · subst m
    exact Or.inl ((keep a (ts am) z (ts zt) (star z zt za)).resolve_right
      (fun h=>h.elim (fun p=>zb p.2) (fun p=>za p.2)))
  · subst m
    exact Or.inr ((keep b (ts bm) z (ts zt) (star z zt zb)).resolve_right
      (fun h=>h.elim (fun p=>zb p.2) (fun p=>za p.2)))

/-- A potentially used repair edge is harmless when it is a shortcut
for a four-edge path through the three fresh vertices. A tile using
the shortcut is replaced by two; otherwise the fresh path is one
new tile. -/
theorem lift_live_ear {G H : SimpleGraph V} {S : Finset V} {a b l c r : V}
    (ab : a≠b) (al : G.Adj a l) (lc : G.Adj l c) (cr : G.Adj c r)
    (rb : G.Adj r b) (lr : l≠r) (lo : l∉S) (co : c∉S) (ro : r∉S)
    (keep : ∀ x∈S,∀ y∈S,H.Adj x y →
      G.Adj x y ∨ (x=a∧y=b) ∨ (x=b∧y=a))
    (fact : FactorOn H S) :
    FactorOn G (S∪({l,c,r}:Finset V)) := by
  obtain ⟨P,pt,pd,pc⟩ := fact
  have sub (T : Finset V) (tp : T∈P) : T⊆S :=
    fun _ t=>pc ▸ mem_biUnion.mpr ⟨T,tp,t⟩
  by_cases uses : ∃ T∈P,¬IsTile G T
  · obtain ⟨T,tp,bad⟩ := uses
    obtain ⟨z,za,zb,shape,wire⟩ := bad_tile_shape ab (sub T tp) keep (pt T tp) bad
    have compatible (A : Finset V) (ap : A∈P) (an : A≠T) : IsTile G A := by
      by_contra second
      obtain ⟨z',_,_,eq,_⟩ := bad_tile_shape ab (sub A ap) keep (pt A ap) second
      have ma : a∈A := by simp [eq]
      have mt : a∈T := by simp [shape]
      exact disjoint_left.mp (pd A ap T tp an) ma mt
    have rest : FactorOn G (S\T) := by
      refine ⟨P.erase T,?_ ,?_ ,?_⟩
      · intro A am
        exact compatible A (mem_erase.mp am).2 (mem_erase.mp am).1
      · intro A am B bm h
        exact pd A (mem_erase.mp am).2 B (mem_erase.mp bm).2 h
      · ext z
        constructor
        · intro zm
          obtain ⟨A,am,zm⟩ := mem_biUnion.mp zm
          obtain ⟨at',ap⟩ := mem_erase.mp am
          exact mem_sdiff.mpr ⟨sub A ap zm,fun zt=>disjoint_left.mp (pd A ap T tp at') zm zt⟩
        · intro zm
          obtain ⟨qs,qt⟩ := mem_sdiff.mp zm
          obtain ⟨A,am,av⟩ := mem_biUnion.mp (pc.symm ▸ qs)
          exact mem_biUnion.mpr ⟨A,mem_erase.mpr ⟨fun e=>qt (e ▸ av),am⟩,av⟩
    rcases wire with left|right
    · have swapped : T=({b,a,z}:Finset V) := by
        rw [shape]
        ext v
        simp [or_left_comm]
      have h := lift_for_oriented_tile rest swapped (sub T tp) ab.symm zb.symm
        left rb.symm cr.symm lc.symm al.symm lr.symm ro co lo
      have swap : ({r,c,l}:Finset V)={l,c,r} := by
        ext v
        simp
        tauto
      rwa [swap] at h
    · exact lift_for_oriented_tile rest shape (sub T tp) ab za.symm right al lc cr rb lr lo co ro
  · have orig : FactorOn G S := ⟨P,fun A am=>by_contra (fun h=>uses ⟨A,am,h⟩),pd,pc⟩
    apply extend_tile orig (tile_of_path lc cr lr)
    rw [disjoint_left]
    intro v vs vt
    simp only [mem_insert,mem_singleton] at vt
    rcases vt with rfl|rfl|rfl
    · exact lo vs
    · exact co vs
    · exact ro vs

#print axioms lift_live_ear
end KelmansCactus.AtomicBridge.RemoteTinyEarCore
