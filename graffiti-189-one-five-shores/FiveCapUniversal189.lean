import OreClosure189
import UniversalRouteSingletons189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset Graffiti189Ore
variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
set_option linter.unusedSectionVars false

/-- If at least two of the nonports are universal, five porters can
use the artificial cap to span. For exactly two nonports, one real
porter edge replaces the missing separator. -/
theorem traceable_cap_five_with_universal_nonports
    (P : Finset V) (p5 : P.card=5)
    (two : 2≤(univ\P).card)
    (universal : ∀ x∉P,∀ y,x≠y → J.Adj x y)
    (extra : (univ\P).card=2 → ∃ x∈P,∃ y∈P,J.Adj x y) :
    Graffiti189Ore.Traceable (cap J (fun u=>u∈P)) := by
  classical
  let K := (univ : Finset V)\P
  have twok : 2≤K.card := two
  have pos : K.Nonempty := card_pos.mp (by omega)
  obtain ⟨k,kk⟩ := pos
  have ku : k∉P := (mem_sdiff.mp kk).2
  have build {p q : V} (pp : p∈P) (qp : q∈P) (pq : p≠q)
      (route : ∃ t,RouteOn J (K∪((P.erase p).erase q)) k t) :
      Graffiti189Ore.Traceable (cap J (fun u=>u∈P)) := by
    obtain ⟨t,walk⟩ := route
    let R := (P.erase p).erase q
    have np : p∉K∪R := by
      intro h
      exact (mem_union.mp h).elim (fun m=>(mem_sdiff.mp m).2 pp)
        (fun m=>(mem_erase.mp (mem_of_mem_erase m)).1 rfl)
    have nq : q∉insert p (K∪R) := by
      intro h
      rcases mem_insert.mp h with e|h
      · exact pq e.symm
      exact (mem_union.mp h).elim (fun m=>(mem_sdiff.mp m).2 qp)
        (fun m=>(mem_erase.mp m).1 rfl)
    have pk := (universal k ku p (fun e=>ku (e.symm ▸ pp))).symm
    obtain ⟨path,pathP,pathS⟩ := walk.prefix pk np
    let H := cap J (fun u=>u∈P)
    let path' := path.map (liftCap J (fun u=>u∈P))
    have hs : path'.support=path.support.map some := support_map _ _
    have hPath : path'.IsPath := IsPath.mk' (hs ▸
      pathP.support_nodup.map (Option.some_injective V))
    have capP : H.Adj none (.some p) := pp
    have capQ : H.Adj (.some q) none := qp
    let out := Walk.cons capQ (Walk.cons capP path')
    have nNone : (none : Option V)∉path'.support := by simp [hs]
    have nQ : (.some q : Option V)∉(Walk.cons capP path').support := by
      intro h
      simp only [support_cons,List.mem_cons,Option.some_ne_none,false_or,hs] at h
      obtain ⟨w,wm,eq⟩ := List.mem_map.mp h
      exact nq ((pathS _).mp ((Option.some.inj eq) ▸ wm))
    have hp : out.IsPath := (hPath.cons nNone).cons nQ
    refine ⟨some q,some t,out,hp,?_⟩
    intro z
    cases z with
    | none => simp [out]
    | some z =>
      by_cases zq : z=q
      · simp [out,zq]
      have all : z∈insert p (K∪R) := by
        by_cases zp : z∈P
        · by_cases eq : z=p
          · simp [eq]
          exact mem_insert_of_mem (mem_union_right _ (mem_erase.mpr ⟨zq,mem_erase.mpr ⟨eq,zp⟩⟩))
        exact mem_insert_of_mem (mem_union_left _ (mem_sdiff.mpr ⟨mem_univ _,zp⟩))
      simp [out,hs,(pathS z).mpr all]
  have hjoin (x : V) (xK : x∈K) (y : V) (_ : y∈K∪P) (xy : x≠y) : J.Adj x y :=
    universal x (mem_sdiff.mp xK).2 y xy
  have route_for {p q : V} (pp : p∈P) (qp : q∈P) (pq : p≠q)
      (large : 3≤K.card) :
      Graffiti189Ore.Traceable (cap J (fun u=>u∈P)) := by
    apply build pp qp pq
    let R := (P.erase p).erase q
    have sub : R⊆P := fun z h=>mem_of_mem_erase (mem_of_mem_erase h)
    have r3 : R.card=3 := by
      change ((P.erase p).erase q).card=3
      rw [card_erase_of_mem (mem_erase.mpr ⟨pq.symm,qp⟩),card_erase_of_mem pp,p5]
    have d : Disjoint K R := disjoint_left.mpr fun z a b=>(mem_sdiff.mp a).2 (sub b)
    obtain ⟨t,w,_⟩ := universal_route_from_singletons K R kk d
      (fun x xK y ym xy=>hjoin x xK y (union_subset_union (Subset.rfl) sub ym) xy) (by omega)
    exact ⟨t,w⟩
  by_cases large : 3≤K.card
  · obtain ⟨p,pp,q,qp,pq⟩ := one_lt_card.mp (show 1<P.card by omega)
    exact route_for pp qp pq large
  have k2 : K.card=2 := by omega
  obtain ⟨x,xp,y,yp,xy⟩ := extra k2
  let E : Finset V := {x,y}
  have e2 : E.card=2 := by simp [E,xy.ne]
  have es : E⊆P := insert_subset_iff.mpr ⟨xp,singleton_subset_iff.mpr yp⟩
  have count := card_sdiff_add_card_eq_card es
  obtain ⟨p,pm,q,qm,pq⟩ := one_lt_card.mp (show 1<(P\E).card by omega)
  obtain ⟨pp,po⟩ := mem_sdiff.mp pm
  obtain ⟨qp,qo⟩ := mem_sdiff.mp qm
  apply build pp qp pq
  let R := (P.erase p).erase q
  have sub : R⊆P := fun z h=>mem_of_mem_erase (mem_of_mem_erase h)
  have r3 : R.card=3 := by
    change ((P.erase p).erase q).card=3
    rw [card_erase_of_mem (mem_erase.mpr ⟨pq.symm,qp⟩),card_erase_of_mem pp,p5]
  have er : E⊆R := by
    intro v ve
    exact mem_erase.mpr ⟨fun h=>qo (h ▸ ve),mem_erase.mpr ⟨fun h=>po (h ▸ ve),es ve⟩⟩
  have tally := card_sdiff_add_card_eq_card er
  have d : Disjoint K R := disjoint_left.mpr fun z a b=>(mem_sdiff.mp a).2 (sub b)
  obtain ⟨t,w,_⟩ := universal_route_with_one_block K R E kk
    (by simp [E]) (by simp [E]) d er (RouteOn.edge xy)
    (fun x xK y ym xy=>hjoin x xK y (union_subset_union (Subset.rfl) sub ym) xy) (by omega)
  exact ⟨t,w⟩

#print axioms traceable_cap_five_with_universal_nonports
end Graffiti189LongestPath.CrossSaturation
