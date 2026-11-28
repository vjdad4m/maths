import GapTwin189
import MultiPinRotation189
import Mathlib.Combinatorics.SimpleGraph.Finite
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open private Graffiti189LongestPath.splice_gap_two Graffiti189LongestPath.pin_data
  Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.no_endpoints from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.exclusive_gap_pin from OneSlack189
open private Graffiti189LongestPath.GapTwin.splice_gap_two_allow_midpoint
  Graffiti189LongestPath.GapTwin.edgeCount from GapTwin189
set_option linter.unusedSectionVars false
set_option warningAsError true
namespace Graffiti189LongestPath.GapStrong
variable {V : Type*} {G : SimpleGraph V}

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

open Graffiti189LongestPath.GapTwin Graffiti189LongestPath.Rigidity

/-- Two vertices swapped through a gap-two pair share a degree budget. If the
midpoint has an omitted neighbor, exact exhaustion would make the right flank
universal along the path, enabling a rotation to the midpoint and extension. -/
theorem sum_degree_gap_exchange (hc : G.Connected) (d : ℕ)
    (cap : ∀ w, (EvenFrom G w).card ≤ d+1)
    {a b : V} {p : G.Walk a b} (hMin : EdgeMin p)
    {x : V} (hx : x ∉ p.support)
    (i : ℕ) (hPins : Pins p x = {i,i+2}) :
    G.degree x + G.degree (p.getVert (i+1)) ≤ d+4 ∧
      (3 ≤ G.degree (p.getVert (i+1)) → G.degree x + G.degree (p.getVert (i+1)) ≤ d+3) := by
  classical
  have hp := hMin.1
  let l := p.getVert i
  let z := p.getVert (i+1)
  let r := p.getVert (i+2)
  have ip : i ∈ Pins p x := by simp [hPins]
  have jp : i+2 ∈ Pins p x := by simp [hPins]
  have hi := (Graffiti189LongestPath.pin_data jp).1
  have lx : G.Adj x l := (Graffiti189LongestPath.pin_data ip).2
  have rx : G.Adj x r := (Graffiti189LongestPath.pin_data jp).2
  have lz : G.Adj l z := p.adj_getVert_succ (i:=i) (by omega)
  have zr : G.Adj z r := p.adj_getVert_succ (i:=i+1) (by omega)
  have lr : l ≠ r := fun e => by
    have h := hp.1.getVert_injOn (show i ≤ p.length by omega)
      (show i+2 ≤ p.length by omega) e
    omega
  have zx : z ≠ x := fun he => hx (he ▸ p.getVert_mem_support (i+1))
  let S := p.support.toFinset.erase z
  let L : Finset V := {l,r}
  have lS : l ∈ S := mem_erase.mpr ⟨lz.ne,by simp [l]⟩
  have rS : r ∈ S := mem_erase.mpr ⟨zr.ne.symm,by simp [r]⟩
  have xS : x ∉ S := fun h => hx (List.mem_toFinset.mp (mem_erase.mp h).2)
  have zS : z ∉ S := by simp [S]
  have zOld : z ∈ p.support.toFinset := List.mem_toFinset.mpr (p.getVert_mem_support (i+1))
  have oldset : p.support.toFinset = insert z S := (insert_erase zOld).symm
  have x_on {w : V} (hw : w ∈ p.support) (ex : G.Adj x w) : w = l ∨ w = r := by
    obtain ⟨j,he,hj⟩ := mem_support_iff_exists_getVert.mp hw
    have hj' : j < p.length := by
      by_contra jn
      have e : j = p.length := by omega
      rw [e,getVert_length] at he
      exact (Graffiti189LongestPath.no_endpoints hp hx).2 (he.symm ▸ ex)
    have hm : j ∈ Pins p x := mem_filter.mpr ⟨mem_range.mpr hj',he.symm ▸ ex⟩
    rw [hPins] at hm
    rcases mem_insert.mp hm with eq | eq
    · exact Or.inl (he.symm.trans (congrArg p.getVert eq))
    · exact Or.inr (he.symm.trans (congrArg p.getVert (mem_singleton.mp eq)))
  have noxz : ¬ G.Adj x z := by
    intro h
    exact (x_on (p.getVert_mem_support (i+1)) h).elim lz.ne.symm zr.ne
  have xeq : G.neighborFinset x ∩ S = L := by
    ext w
    rw [mem_inter,G.mem_neighborFinset,mem_insert,mem_singleton]
    refine ⟨fun ⟨h,hS⟩ => x_on (List.mem_toFinset.mp (mem_erase.mp hS).2) h,?_⟩
    rintro (rfl | rfl)
    · exact ⟨lx,lS⟩
    · exact ⟨rx,rS⟩
  have zsub : L ⊆ G.neighborFinset z ∩ S := by
    intro u hu
    rcases mem_insert.mp hu with rfl | hu
    · exact mem_inter.mpr ⟨(G.mem_neighborFinset z l).mpr lz.symm,lS⟩
    · obtain rfl := mem_singleton.mp hu
      exact mem_inter.mpr ⟨(G.mem_neighborFinset z r).mpr zr,rS⟩
  obtain ⟨q,hq,hLen,hSupp⟩ :=
    Graffiti189LongestPath.splice_gap_two p hp.1 (Walk.nil : G.Walk x x) IsPath.nil
      (by simpa using hx) i (by omega) lx.symm rx
  have len : q.length = p.length := by simpa using hLen
  have qLongest : IsLongest q := ⟨hq,fun a b w hw => len.symm ▸ hp.2 a b w hw⟩
  have qset : q.support.toFinset = insert x S := by
    ext w
    simp only [List.mem_toFinset, hSupp, support_nil, List.mem_singleton, mem_insert, S, mem_erase]
    tauto
  have cn := hMin.2 a b q qLongest
  rw [oldset,qset,Graffiti189LongestPath.GapTwin.edgeCount zS,Graffiti189LongestPath.GapTwin.edgeCount xS,xeq] at cn
  have zeq : G.neighborFinset z ∩ S = L :=
    (eq_of_subset_of_card_le zsub (by omega)).symm
  let X := G.neighborFinset x \ L
  let Z := G.neighborFinset z \ L
  have xOff {w : V} (hw : w ∈ X) : w ∉ p.support :=
    fun h => (mem_sdiff.mp hw).2
      (by simpa [L] using x_on h ((G.mem_neighborFinset x w).mp (mem_sdiff.mp hw).1))
  have zOff {w : V} (hw : w ∈ Z) : w ∉ p.support := by
    intro hh
    have ew := (G.mem_neighborFinset z w).mp (mem_sdiff.mp hw).1
    have hS : w ∈ S := mem_erase.mpr ⟨ew.ne.symm,List.mem_toFinset.mpr hh⟩
    exact (mem_sdiff.mp hw).2 (zeq ▸ mem_inter.mpr ⟨(mem_sdiff.mp hw).1,hS⟩)
  have noflankX {w : V} (hw : w ∈ X) : ¬G.Adj w r := by
    intro h
    have ed := (G.mem_neighborFinset x w).mp (mem_sdiff.mp hw).1
    obtain ⟨q,hq,hLen,_⟩ := Graffiti189LongestPath.splice_gap_two p hp.1 ed.toWalk
      (IsPath.of_adj _)
      (by simp [xOff hw,hx]) i (by omega) lx.symm h
    have hL := hp.2 a b q hq
    simp at hLen
    omega
  have noflankZ {w : V} (hw : w ∈ Z) : ¬G.Adj w r := by
    intro h
    have ed := (G.mem_neighborFinset z w).mp (mem_sdiff.mp hw).1
    obtain ⟨q,hq,hLen,_⟩ := Graffiti189LongestPath.GapTwin.splice_gap_two_allow_midpoint p hp.1 ed.toWalk
      (IsPath.of_adj _) i (by
        intro t ht tp
        have h' : t = z ∨ t = w := by simpa using ht
        exact h'.elim id (fun h => (zOff hw (h ▸ tp)).elim))
      (by omega) lz h
    have hL := hp.2 a b q hq
    simp at hLen
    omega
  have dis : Disjoint X Z := disjoint_left.mpr (by
    intro w hX hZ
    have xw := (G.mem_neighborFinset x w).mp (mem_sdiff.mp hX).1
    have wz := (G.mem_neighborFinset z w).mp (mem_sdiff.mp hZ).1 |>.symm
    let t : G.Walk x z := Walk.cons xw (Walk.cons wz Walk.nil)
    have hW : t.IsPath := ((IsPath.of_adj wz).cons (by simp [xw.ne,zx.symm]))
    obtain ⟨q,hq,hLen,_⟩ := Graffiti189LongestPath.GapTwin.splice_gap_two_allow_midpoint p hp.1 t hW i (by
      intro u hu hp'
      have hh : u = x ∨ u = w ∨ u = z := by simpa [t] using hu
      exact hh.elim (fun h => (hx (h ▸ hp')).elim)
        (fun h => h.elim (fun he => (xOff hX (he ▸ hp')).elim) id))
      (by omega) lx.symm zr
    have hL := hp.2 a b q hq
    simp [t] at hLen
    omega)
  have sub : X ∪ Z ⊆ DistanceTwo G r := by
    intro w hw
    have lmem := p.getVert_mem_support (i+2)
    apply Graffiti189LongestPath.mem_distanceTwo.mpr
    rcases mem_union.mp hw with h | h
    · exact Graffiti189LongestPath.dist_two hc (fun e => xOff h (e ▸ lmem))
        (fun e => noflankX h e.symm) rx.symm
        ((G.mem_neighborFinset x w).mp (mem_sdiff.mp h).1)
    · exact Graffiti189LongestPath.dist_two hc (fun e => zOff h (e ▸ lmem))
        (fun e => noflankZ h e.symm) zr.symm
        ((G.mem_neighborFinset z w).mp (mem_sdiff.mp h).1)
  have cu := card_le_card sub
  rw [card_union_of_disjoint dis] at cu
  have xsub : L ⊆ G.neighborFinset x :=
    fun w hw => (mem_inter.mp (xeq.symm ▸ hw)).1
  have zsub' : L ⊆ G.neighborFinset z :=
    fun w hw => (mem_inter.mp (zsub hw)).1
  have cx := card_sdiff_add_card_eq_card xsub
  have cz := card_sdiff_add_card_eq_card zsub'
  rw [G.card_neighborFinset_eq_degree] at cx cz
  have lC : L.card = 2 := by simp [L,lr]
  have bd := distanceTwo_le_of_even d r (cap r)
  change X.card + L.card = G.degree x at cx
  change Z.card + L.card = G.degree z at cz
  change G.degree x + G.degree z ≤ d+4 ∧
    (3 ≤ G.degree z → G.degree x + G.degree z ≤ d+3)
  refine ⟨by omega,fun hz => ?_⟩
  by_contra! h
  have ce : (X ∪ Z).card = (DistanceTwo G r).card := by
    rw [card_union_of_disjoint dis]
    omega
  have eq := eq_of_subset_of_card_le sub ce.ge
  have noPdistance {v : V} (hv : v ∈ p.support) : v ∉ DistanceTwo G r := by
    intro h
    rw [← eq] at h
    exact (mem_union.mp h).elim (fun h => xOff h hv) (fun h => zOff h hv)
  let near (v : V) := v=r ∨ G.Adj r v
  have step {v w : V} (hn : near v) (ew : G.Adj v w) (hw : w ∈ p.support) : near w := by
    rcases hn with hn|hn
    · exact Or.inr (hn ▸ ew)
    · by_cases h : w=r
      · exact Or.inl h
      · by_cases hw' : G.Adj r w
        · exact Or.inr hw'
        · exact (noPdistance hw (Graffiti189LongestPath.mem_distanceTwo.mpr
            (Graffiti189LongestPath.dist_two hc (fun e => h e.symm) hw' hn ew))).elim
  have propagate {u v : V} (q : G.Walk u v) (hs : ∀ t∈q.support,t∈p.support)
      (hu : near u) : near v := by
    induction q with
    | nil => exact hu
    | @cons u w v e q ih =>
      exact ih (fun t ht => hs t (by simp [ht]))
        (step hu e (hs w (by simp)))
  have ar : near a := by
    let er := p.getVert_mem_support (i+2)
    apply propagate ((p.takeUntil r er).reverse) _ (Or.inl rfl)
    intro t ht
    rw [support_reverse,List.mem_reverse] at ht
    exact p.support_takeUntil_subset er ht
  have na : a ≠ r :=
    fun e => (Graffiti189LongestPath.no_endpoints hp hx).1 (e.symm ▸ rx)
  have jump : G.Adj a r := (ar.resolve_left na).symm
  obtain ⟨w,hw,hs,_,_,_⟩ := rotate_start hp (i+1) (by omega) jump
  have Zpos : Z.Nonempty := card_pos.mp (by omega)
  obtain ⟨v,hv⟩ := Zpos
  have ev := (G.mem_neighborFinset z v).mp (mem_sdiff.mp hv).1
  exact (Graffiti189LongestPath.no_endpoints hw (fun h => zOff hv ((hs v).mpr h))).1 ev.symm

#print axioms sum_degree_gap_exchange
end Graffiti189LongestPath.GapStrong
