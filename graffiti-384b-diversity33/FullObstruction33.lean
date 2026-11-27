import CubicOverlap33

namespace Graffiti384b.ForcedCubics
open Finset SimpleGraph PositiveCore33 CliquePivot33
open private Repair.full_nbr from Repair384b
open private CliquePivot33.full_cubic from CliquePivot33
open private CubicShore.half_tight from CubicDiamondCut33
open private TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The forced cubics are nonadjacent, share at most one neighbor and
cover at least three vertices of every five-clique by their neighborhoods.
The three neighbors of the score-three cubic form a clique transversal. -/
theorem full_obstruction (n : Fintype.card V=33) (t : (types G).card=33) (conn : G.Connected)
    (bad : bound G<gamma G) {z : V} (zz : trianglesAt G z=0) :
    ∃ u v,trianglesAt G u=2 ∧ G.degree u=3 ∧ ¬G.Adj z u ∧
      trianglesAt G v=3 ∧ G.degree v=3 ∧ ¬G.Adj z v ∧ ¬G.Adj u v ∧
      (G.neighborFinset u∩G.neighborFinset v).card≤1 ∧
      ∀ C,G.IsNClique 5 C →
        3≤(C∩(G.neighborFinset u∪G.neighborFinset v)).card ∧ ∃ x∈C,G.Adj v x := by
  classical
  have inj := exact_counts_injective G n t
  obtain ⟨u,v,us,du,zu,vs,dv,zv⟩ := full_pair G n t conn bad zz
  have uz : u≠z := by intro h; subst u; omega
  have vz : v≠z := by intro h; subst v; omega
  have edge : ∃ b,G.Adj z b := by
    have re := conn z u
    obtain ⟨walk⟩ := re
    cases walk with
    | nil => exact (uz rfl).elim
    | cons ed _ => exact ⟨_,ed⟩
  obtain ⟨b,zb⟩ := edge
  let P := ({z}:Finset V)ᶜ
  let H := G.induce (P:Set V)
  let U : P := ⟨u,by simp [P,uz]⟩
  let Z : P := ⟨v,by simp [P,vz]⟩
  obtain ⟨sz,_,sc,pos,ij,g⟩ := extremal_core G n t conn bad inj zz zb
  have ord : Fintype.card P=32 := (Fintype.card_coe P).trans sz
  have degree (w : P) (off : ¬G.Adj z w.val) : H.degree w=G.degree w.val := by
    have no : ({z}:Finset V).filter (G.Adj w.val)=∅ := filter_eq_empty_iff.mpr (by
      intro y ym; obtain rfl := mem_singleton.mp ym; exact fun h => off h.symm)
    have total := Repair.full_nbr G w.val {z}
    change (({z}:Finset V).filter (G.Adj w.val)).card+_= _ at total
    rw [no,card_empty,Nat.zero_add] at total
    rw [EarAnchor.induced_degree]; exact total
  have dU := (degree U zu).trans du
  have dZ := (degree Z zv).trans dv
  have sU := (sc U).trans us
  have sZ := (sc Z).trans vs
  have few : (G.neighborFinset u∩G.neighborFinset v).card≤1 := by
    apply card_le_one.mpr
    intro p pm q qm
    apply Classical.byContradiction; intro pq
    obtain ⟨up,vp⟩ := mem_inter.mp pm
    obtain ⟨uq,vq⟩ := mem_inter.mp qm
    have inz (w : V) (m : w∈G.neighborFinset u) : w∈P := by
      apply mem_compl.mpr; intro eq; obtain rfl := mem_singleton.mp eq
      exact zu ((G.mem_neighborFinset ..).mp m).symm
    let x : P := ⟨p,inz p up⟩
    let y : P := ⟨q,inz q uq⟩
    have xy : x≠y := fun h => pq (congrArg Subtype.val h)
    have sol := core_saving H ord dU sU dZ sZ xy
      (show H.Adj U x from (G.mem_neighborFinset ..).mp up) (show H.Adj U y from (G.mem_neighborFinset ..).mp uq)
      (show H.Adj Z x from (G.mem_neighborFinset ..).mp vp) (show H.Adj Z y from (G.mem_neighborFinset ..).mp vq)
      pos ij
    change gamma H=16 at g; omega
  have sep : ¬G.Adj u v := by
    intro ed
    have sub : (G.neighborFinset v).erase u⊆G.neighborFinset u∩G.neighborFinset v := by
      intro x xm
      obtain ⟨xu,xv⟩ := mem_erase.mp xm
      exact mem_inter.mpr ⟨(G.mem_neighborFinset ..).mpr (EarAnchor.full_neighbors G dv vs ed.symm
        ((G.mem_neighborFinset ..).mp xv) xu.symm),xv⟩
    have cap := (card_le_card sub).trans few
    rw [card_erase_of_mem ((G.mem_neighborFinset ..).mpr ed.symm),card_neighborFinset_eq_degree,dv] at cap
    omega
  refine ⟨u,v,us,du,zu,vs,dv,zv,sep,few,?_⟩
  intro C cl
  have zc : z∉C := by
    intro m
    obtain ⟨a,am,c,cm,ac⟩ := one_lt_card.mp (by rw [card_erase_of_mem m,cl.2]; decide : 1<(C.erase z).card)
    have ⟨az,aa⟩ := mem_erase.mp am
    have ⟨cz,cc⟩ := mem_erase.mp cm
    have pos := (TrianglePrune.triangle_iff G z).mpr ⟨a,c,cl.1 m aa az.symm,cl.1 m cc cz.symm,cl.1 aa cc ac⟩
    omega
  have inP {w : V} (m : w∈C) : w∈P := mem_compl.mpr (fun eq => zc (mem_singleton.mp eq ▸ m))
  let K := C.subtype (fun w => w∈P)
  have lifted : K.map (Function.Embedding.subtype _)=C := subtype_map_of_mem (fun _ h => inP h)
  have kc : H.IsNClique 5 K := ⟨fun i im j jm ne => cl.1 (mem_subtype.mp im) (mem_subtype.mp jm)
    (fun eq => ne (Subtype.ext eq)),(card_map ..).symm.trans ((congrArg card lifted).trans cl.2)⟩
  have half : Fintype.card P≤2*gamma H := by rw [ord,show gamma H=16 from g]
  have tight := CubicShore.half_tight H half
  let B := H.neighborFinset U∪H.neighborFinset Z
  have rem : (K\B).card≤2 := clique_remainder H dU sU dZ sZ pos ij tight kc
  have count := (card_sdiff_add_card_inter K B).trans kc.2
  have sub : (K∩B).map (Function.Embedding.subtype _)⊆C∩(G.neighborFinset u∪G.neighborFinset v) := by
    intro w wm
    obtain ⟨x,xm,rfl⟩ := mem_map.mp wm
    obtain ⟨xk,xb⟩ := mem_inter.mp xm
    apply mem_inter.mpr ⟨mem_subtype.mp xk,?_⟩
    exact (mem_union.mp xb).elim (fun m => mem_union_left _ ((G.mem_neighborFinset ..).mpr ((H.mem_neighborFinset ..).mp m)))
      (fun m => mem_union_right _ ((G.mem_neighborFinset ..).mpr ((H.mem_neighborFinset ..).mp m)))
  have lift := card_le_card sub
  rw [card_map] at lift
  have three : 3≤(C∩(G.neighborFinset u∪G.neighborFinset v)).card := by omega
  refine ⟨three,?_⟩
  apply Classical.byContradiction; intro no
  have inc : C∩(G.neighborFinset u∪G.neighborFinset v)⊆C.filter (G.Adj u) := by
    intro w wm
    obtain ⟨wc,side⟩ := mem_inter.mp wm
    exact mem_filter.mpr ⟨wc,(G.mem_neighborFinset ..).mp ((mem_union.mp side).resolve_right
      (fun m => no ⟨w,wc,(G.mem_neighborFinset ..).mp m⟩))⟩
  have cu : 3≤nbr G u C := three.trans (card_le_card inc)
  have wrong := (CliquePivot33.full_cubic G cl du cu).2
  omega

end Graffiti384b.ForcedCubics
#print axioms Graffiti384b.ForcedCubics.full_obstruction
