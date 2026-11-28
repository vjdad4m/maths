import CycleHallSplice189
import StarConnectivity189
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.CycleHallSplice Graffiti189LongestPath.StarConnectivity
open Graffiti189LongestPath.MengerRoutable
open private Graffiti189LongestPath.Rigidity.mem_omittedStar from Rigidity189
set_option warningAsError true
set_option maxHeartbeats 3000000
namespace Graffiti189LongestPath.StarCycleClosure
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
/-- Compiling nested deletion in the root-deleted shore into one ambient deletion. -/
def erase_root_and_set_iso (A : Finset V) (x : V)
    (S : Finset ↥((A.erase x : Finset V) : Set V)) :
    G.induce ((↑(A \ insert x (S.map ⟨Subtype.val,Subtype.val_injective⟩))) : Set V) ≃g
      (G.induce ((A.erase x : Finset V) : Set V)).induce ((↑S : Set _)ᶜ) := by
  classical
  let val : ↥((A.erase x : Finset V) : Set V) ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let X := insert x (S.map val)
  let Y := A\X
  let Z := (↑S : Set ↥((A.erase x : Finset V) : Set V))ᶜ
  change G.induce (Y : Set V) ≃g (G.induce ((A.erase x : Finset V) : Set V)).induce Z
  let forward (v : ↥(Y:Set V)) : Z := by
    have va := (mem_sdiff.mp v.property).1
    have vx := (mem_sdiff.mp v.property).2
    have neq : v.val≠x := fun ex => vx (mem_insert.mpr (Or.inl ex))
    let w : ↥((A.erase x : Finset V) : Set V) := ⟨v.val,mem_erase.mpr ⟨neq,va⟩⟩
    refine ⟨w,?_⟩
    intro ws
    exact vx (mem_insert.mpr (Or.inr (mem_map.mpr ⟨w,ws,rfl⟩)))
  let inv (v : Z) : ↥(Y : Set V) := by
    have neq := (mem_erase.mp v.val.property).1
    have va := (mem_erase.mp v.val.property).2
    refine ⟨v.val.val,mem_sdiff.mpr ⟨va,?_⟩⟩
    intro hx
    rcases mem_insert.mp hx with e|h
    · exact neq e
    · obtain ⟨w,ws,eq⟩ := mem_map.mp h
      have he : w=v.val := Subtype.val_injective eq
      exact v.property (he ▸ ws)
  refine ⟨⟨forward,inv,?_,?_⟩,?_⟩
  · intro v; apply Subtype.ext; rfl
  · intro v; apply Subtype.ext; apply Subtype.ext; rfl
  · intro u v; rfl

omit [Fintype V] [DecidableRel G.Adj] in
theorem cycle_card_support {a : V} (c : G.Walk a a) (hc : c.IsCycle) :
    c.support.toFinset.card=c.length := by
  have no : ¬c.Nil := by simpa only [nil_iff_eq_nil] using hc.ne_nil
  have sup : c.support.toFinset=c.support.tail.toFinset := by
    ext z
    simp only [List.mem_toFinset,Walk.mem_support_iff]
    exact ⟨fun h => h.elim (fun z => z.symm ▸ end_mem_tail_support no) id,Or.inr⟩
  rw [sup,List.toFinset_card_of_nodup hc.support_nodup,List.length_tail,length_support]
  omega

/-- A sufficiently long cycle in the root-deleted star excludes even
the non-Hamilton-connected separated-double branch. The cycle is the
only extra geometric premise; all endpoint routes are built here. -/
theorem separated_double_no_long_shore_cycle (hc : G.Connected) (k : Nat) (hk : 6≤k)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ D : Finset V,D.card<k → (G.induce ((↑D : Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    (fail : ¬∃ (u v : V) (q : G.Walk u v),q.IsPath ∧ ∀ w,w∈q.support)
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    (hx : x∉p.support) (hy : y∉p.support) (xy : G.Adj x y)
    (high : k+2≤G.degree x)
    (double : (Pins p x).card=2) (sep : PairedPins p x=∅)
    (large : 10<(OmittedStar p x).card)
    (len : Nat)
    (long : k*(k+2)<(k+1)*(len+1)+
      2*(External G (OmittedStar p x)\p.support.toFinset).card)
    (cyc : ∃ z, ∃ c : (G.induce (((OmittedStar p x).erase x : Finset V) : Set V)).Walk z z,
      c.IsCycle ∧ max 2 len≤c.length) : False := by
  classical
  let A := OmittedStar p x
  let Z : Set V := ((A.erase x : Finset V) : Set V)
  let J := G.induce Z
  have sepConn (S : Finset Z) (sc : S.card<2) :
      (J.induce ((↑S : Set Z)ᶜ)).Connected := by
    let e : Z ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
    let X := insert x (S.map e)
    have xs : X⊆A := by
      intro v vx
      rcases mem_insert.mp vx with rfl|h
      · exact Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
      · obtain ⟨w,_,rfl⟩ := mem_map.mp h
        exact (mem_erase.mp w.property).2
    have xl := (card_insert_le x (S.map e)).trans (by rw [card_map])
    change X.card≤S.card+1 at xl
    have con := separated_double_star_stays_connected hc k hk cap conn deg fail hp
      hx hy xy double sep X xs (by omega)
    exact (erase_root_and_set_iso (G:=G) A x S).connected_iff.mp con
  let f : J →g G := ⟨Subtype.val, fun e => e⟩
  have fi : Function.Injective f := Subtype.val_injective
  have off (z : Z) : x≠f z := fun e => (mem_erase.mp z.property).1 e.symm
  have adj (z : Z) : G.Adj x (f z) := by
    have zz := (mem_erase.mp z.property).2
    exact (Graffiti189LongestPath.Rigidity.mem_omittedStar.mp zz).2.resolve_left (fun ne => off z ne.symm)
  obtain ⟨a,c,hc',cl⟩ := cyc
  have big : 2≤c.support.toFinset.card := by
    rw [cycle_card_support c hc']
    exact (le_max_left _ _).trans cl
  have L : len≤c.length := (le_max_right _ _).trans cl
  have route : ∀ u∈A,∀ v∈A,u≠v →
      ∃ q : G.Walk u v,q.IsPath ∧ (∀ z∈q.support,z∈A) ∧ len+1≤q.length+1 := by
    intro u ua v va uv
    have rA {z : V} (e : z=x ∨ ∃ w : Z,f w=z) : z∈A := by
      rcases e with rfl|⟨w,rfl⟩
      · exact Graffiti189LongestPath.Rigidity.mem_omittedStar.mpr ⟨hx,Or.inl rfl⟩
      · exact (mem_erase.mp w.property).2
    by_cases hu : u=x
    · subst u
      let t : Z := ⟨v,mem_erase.mpr ⟨uv.symm,va⟩⟩
      obtain ⟨q,qp,ql,qs⟩ := cycle_to_prescribed_root_route f fi off adj c hc'
        (t:=t) (fun s h => sepConn s (by omega))
      exact ⟨q,qp,fun z hz => rA (qs z hz),by omega⟩
    by_cases hv : v=x
    · subst v
      let t : Z := ⟨u,mem_erase.mpr ⟨hu,ua⟩⟩
      obtain ⟨q,qp,ql,qs⟩ := cycle_to_prescribed_root_route f fi off adj c hc'
        (t:=t) (fun s h => sepConn s (by omega))
      exact ⟨q.reverse,qp.reverse,fun z hz => rA (qs z (by
        simpa only [support_reverse,List.mem_reverse] using hz)),by simpa using (by omega : len+1≤q.length+1)⟩
    let s : Z := ⟨u,mem_erase.mpr ⟨hu,ua⟩⟩
    let t : Z := ⟨v,mem_erase.mpr ⟨hv,va⟩⟩
    have ne : s≠t := fun e => uv (congrArg Subtype.val e)
    obtain ⟨q,qp,ql,qs⟩ := cycle_to_prescribed_route f fi ne off adj c hc' big sepConn
    exact ⟨q,qp,fun z hz => rA (qs z hz),by omega⟩
  exact almost_routable_double_branch_impossible hc k hk cap conn hp hx hy xy high double sep
    (len+1) route long

#print axioms erase_root_and_set_iso
#print axioms separated_double_no_long_shore_cycle
end Graffiti189LongestPath.StarCycleClosure
