import SingleFinish28
import HighEndpoint28
import SharedFrontier28

namespace Graffiti384b.HighSquare28
open Finset SimpleGraph HighEar Core28 Four28
open private Four28.core_data Four28.ear_one from FourFrontier28
variable {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj]

theorem fan_center_degree {T Y : Finset V} (fan : Fan H T Y) {z : V} (zt : z∈T) :
    4≤H.degree z := by
  have sub : (T.erase z)∪Y ⊆ H.neighborFinset z := by
    intro x xm
    apply (H.mem_neighborFinset ..).mpr
    exact (mem_union.mp xm).elim (fun m => fan.1.1 zt (mem_erase.mp m).2 (mem_erase.mp m).1.symm)
      (fan.2.2.2 z zt x)
  have sz := card_le_card sub
  rw [card_union_of_disjoint (fan.2.2.1.mono_left (erase_subset ..)),card_erase_of_mem zt,fan.1.2,
    fan.2.1,card_neighborFinset_eq_degree] at sz
  exact sz

/-- Any cubic tip and a different cubic adjacent to two central vertices
would share two neighbors. The two scores must be two and three. -/
theorem no_cubic_tip {e u s : V} {T Y : Finset V} (fan : Fan H T Y)
    (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt H v) (fi : Function.Injective (trianglesAt H))
    (half : 14≤gamma H) (free : H.CliqueFree 5) (de : H.degree e=2)
    (du : H.degree u=3) (uy : u∉Y) (st : s∈T) (covers : ∀ z∈T,z≠s → H.Adj u z) :
    ∀ v∈Y,H.degree v≠3 := by
  intro v vy dv
  have many : (T.erase s).card=2 := by rw [card_erase_of_mem st,fan.1.2]
  obtain ⟨p,q,pq,eq⟩ := card_eq_two.mp many
  have pm : p∈T.erase s := eq ▸ mem_insert_self ..
  have qm : q∈T.erase s := eq ▸ mem_insert_of_mem (mem_singleton_self _)
  obtain ⟨ps,pt⟩ := mem_erase.mp pm
  obtain ⟨qs,qt⟩ := mem_erase.mp qm
  have up := covers p pt ps
  have uq := covers q qt qs
  have vp := (fan.2.2.2 p pt v vy).symm
  have vq := (fan.2.2.2 q qt v vy).symm
  have away : trianglesAt H u≠trianglesAt H v := fun h => uy (fi h ▸ vy)
  have hit (C : Finset V) (cl : H.IsNClique 5 C) : p∈C ∨ q∈C := (free C cl).elim
  have su := cubic_scores H de du pos fi
  have sv := cubic_scores H de dv pos fi
  rcases su with hu|hu <;> rcases sv with hv|hv
  · exact away (hu.trans hv.symm)
  · have r := CorePair28.shared_saving H n du hu dv hv pq up uq vp vq pos fi hit
    omega
  · have r := CorePair28.shared_saving H n dv hv du hu pq vp vq up uq pos fi hit
    omega
  · exact away (hu.trans hv.symm)

theorem endpoint_at_least_four {e p q s : V} (n : Fintype.card V=28) (pos : ∀ v,0<trianglesAt H v)
    (fi : Function.Injective (trianglesAt H)) (free : H.CliqueFree 5) (half : 14≤gamma H)
    (pq : H.Adj p q) (en : H.neighborFinset e={p,q}) (sm : s∈additional H e p q) : 4≤H.degree p := by
  have ep : H.Adj e p := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_self ..)
  have eq' : H.Adj e q := (H.mem_neighborFinset ..).mp (en ▸ mem_insert_of_mem (mem_singleton_self _))
  obtain ⟨se,ps,qs⟩ := (additional_mem H).mp sm
  have lim := card_le_card (show ({e,q,s}:Finset V)⊆H.neighborFinset p from
    insert_subset ((H.mem_neighborFinset ..).mpr ep.symm)
      (insert_subset ((H.mem_neighborFinset ..).mpr pq) (singleton_subset_iff.mpr ((H.mem_neighborFinset ..).mpr ps))))
  rw [card_neighborFinset_eq_degree] at lim
  have sz : ({e,q,s}:Finset V).card=3 := by simp [eq'.ne,se.symm,qs.ne]
  rw [sz] at lim
  have no : H.degree p≠3 := fun d => (Nat.not_succ_le_self 13) (half.trans (cubic_endpoint H n pos fi free pq en sm d))
  omega

/-- A unique external cubic would force a single common neighbor at the
center of the fan and leave no other exterior cubic. The two-trial bound
then gives a thirteenth vertex for the core 2-dominating set. -/
theorem forced_pair (t : (types H).card=29) (q : (nonleaves H).card=28) (bad : bound H<gamma H) :
    let J := triangleEdges (H.induce (nonleaves H:Set V))
    J.CliqueFree 5 → ∀ e a b,J.Adj a b → J.neighborFinset e={a,b} →
      (additional J e a b).Nonempty ∧ 4≤J.degree a ∧ 4≤J.degree b ∧
      (∀ s∈additional J e a b,5≤J.degree s ∧ 4≤trianglesAt J s) ∧
      ∃ T Y,Fan J T Y ∧ Disjoint (T∪Y) {e,a,b} ∧ ∃ u v,
        u∉T∪Y∪{e,a,b} ∧ v∉T∪Y∪{e,a,b} ∧ J.degree u=3 ∧ J.degree v=3 ∧
        trianglesAt J u=2 ∧ trianglesAt J v=3 := by
  classical
  dsimp only
  intro free e a b ab en
  let J := triangleEdges (H.induce (nonleaves H:Set V))
  obtain ⟨n,pos,fi,half,_⟩ := Four28.core_data H t q bad
  obtain ⟨ne,hard,T,Y,fan,dis,_,alt⟩ := surviving_ear H t q bad free e a b ab en
  obtain ⟨s,sm⟩ := ne
  have swap : additional J e a b=additional J e b a := by simp [additional,inter_comm]
  have da := endpoint_at_least_four J n pos fi free half ab en sm
  have db := endpoint_at_least_four J n pos fi free half ab.symm (en.trans (pair_comm ..)) (swap ▸ sm)
  let C := univ.filter (fun u => u∉T∪Y∪{e,a,b} ∧ J.degree u=3)
  change ((∃ u∈C,trianglesAt J u=2) ∧ (∃ v∈C,trianglesAt J v=3) ∨ _) at alt
  rcases alt with both|⟨u,z,only,single,zt,_,covers⟩
  · obtain ⟨⟨u,um,su⟩,⟨v,vm,sv⟩⟩ := both
    obtain ⟨uo,du⟩ := (mem_filter.mp um).2
    obtain ⟨vo,dv⟩ := (mem_filter.mp vm).2
    refine ⟨⟨s,sm⟩,da,db,?_,T,Y,fan,dis,u,v,uo,vo,du,dv,su,sv⟩
    intro w wm
    obtain ⟨dw,sw⟩ := hard w wm
    have no : trianglesAt J w≠3 := by
      intro h; have eq := fi (h.trans sv.symm); rw [eq] at dw
      change 5≤J.degree v at dw; omega
    change 3≤trianglesAt J w at sw
    exact ⟨dw,show 4≤trianglesAt J w by omega⟩
  · change C={u} at only
    have um : u∈C := only ▸ mem_singleton_self _
    obtain ⟨uo,du⟩ := (mem_filter.mp um).2
    have off : u∉({e,a,b}:Finset _) := fun h => uo (mem_union_right _ h)
    have un : u∉Y := fun h => uo (mem_union_left _ (mem_union_right _ h))
    have de : J.degree e=2 := by rw [←card_neighborFinset_eq_degree,en,card_pair ab.ne]
    have notip := no_cubic_tip J fan n pos fi half free de du un zt covers
    have unique (v : _) (ve : v∉({e,a,b}:Finset _)) (dv : J.degree v=3) : v=u := by
      have out : v∉T∪Y := by
        intro m
        rcases mem_union.mp m with vt|vy
        · have deg := fan_center_degree J fan vt; omega
        · exact notip v vy dv
      have cm : v∈C := mem_filter.mpr ⟨mem_univ _,fun m => (mem_union.mp m).elim out ve,dv⟩
      exact mem_singleton.mp (only ▸ cm)
    have dz := (hard z (single ▸ mem_singleton_self _)).1
    have save := one_external_cubic J n pos fi free ab en single dz da db du off unique
    exact ((Nat.not_succ_le_self 13) (half.trans save)).elim

end Graffiti384b.HighSquare28
#print axioms Graffiti384b.HighSquare28.no_cubic_tip
#print axioms Graffiti384b.HighSquare28.endpoint_at_least_four
#print axioms Graffiti384b.HighSquare28.forced_pair
