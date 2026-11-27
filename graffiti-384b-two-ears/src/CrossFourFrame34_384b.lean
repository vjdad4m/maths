import CrossFourRanks34_384b
import CrossFourLoss34_384b
import TwoEdgeTrial34_384b
import TwoEdgeLoss34_384b

namespace Graffiti384b.CrossFour34
open Finset SimpleGraph CliqueChoice LowSample
open private LowSample.anchors LowSample.two_degree from LowSample384b
open private FiniteRange.bad from FiniteRange384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem finish_frame (n : Fintype.card V=34) (t : (types G).card=33) (h : (high G).card=31)
    {e z w b : V} (et : e∈twos G) (zt : z∈twos G) (ez : e≠z)
    (highs : G.neighborFinset e∪G.neighborFinset z⊆high G)
    (sep : Disjoint (G.neighborFinset e) (G.neighborFinset z))
    (ear : G.neighborFinset e={w,b}) (wb : G.Adj w b) (priv : G.neighborFinset w∩G.neighborFinset b={e})
    (score : 2*trianglesAt G w≤G.degree w) : gamma G≤bound G := by
  classical
  by_contra! fail
  letI : Nonempty V := ⟨w⟩
  let W : Finset V := {w,b}
  have we : w∈G.neighborFinset e := ear ▸ mem_insert_self ..
  have be : b∈G.neighborFinset e := ear ▸ mem_insert_of_mem (mem_singleton_self _)
  have ew := (G.mem_neighborFinset _ _).mp we
  have eb := (G.mem_neighborFinset _ _).mp be
  let B := 1+(G.degree b-2).choose 2
  have ab : trianglesAt G b≤B := TwoEdge34.fellow_score G wb ew eb ear priv
  obtain ⟨p,ch⟩ := choose_from G Boundary.levels (fun _ hd => (mem_Icc.mp hd).1)
  let f := p.image (G.degree ·)
  let flag := decide (3∈f)
  let s := (high G\p)\W
  let m := 29-f.card
  let R := refund m
  have fp : f.card=p.card := card_image_of_injOn ch.unique
  have ex (v : V) (vlow : v∈twos G) (near : G.neighborFinset v⊆high G) : G.neighborFinset v⊆high G\p := by
    intro a va
    have highA := near va
    exact mem_sdiff.mpr ⟨highA,fun ap => (mem_sdiff.mp vlow).2
      (mem_sdiff.mp (neighbors_in_pool G ch ap ((G.mem_neighborFinset _ _).mpr ((G.mem_neighborFinset _ _).mp va).symm))).1⟩
  have eh := ex e et (subset_union_left.trans highs)
  have zh := ex z zt (subset_union_right.trans highs)
  have pins : W⊆high G\p := by simpa only [W,ear] using eh
  have zpool : G.neighborFinset z⊆s := fun a az => mem_sdiff.mpr ⟨zh az,
    fun aw => disjoint_left.mp sep (ear ▸ aw) az⟩
  have eqA (v : V) (near : G.neighborFinset v⊆high G\p) : LowSample.anchors G v=G.neighborFinset v := by
    ext a
    exact ⟨fun m => (G.mem_neighborFinset _ _).mpr (mem_filter.mp m).2,
      fun m => mem_filter.mpr ⟨(mem_sdiff.mp (near m)).1,(G.mem_neighborFinset _ _).mp m⟩⟩
  obtain ⟨fc,room,strict⟩ := budget f (mem_powerset.mpr ch.levels)
  have wc : W.card=2 := card_pair wb.ne
  have sz : s.card=m := by
    dsimp only [s,m]
    rw [card_sdiff pins,card_sdiff ch.high_sub,h,wc,fp]; omega
  have count := TwoEdge34.conditional_trial G ch pins et zt ez (show LowSample.anchors G e⊆W by rw [eqA e eh,ear])
    (eqA z zh ▸ zpool) (by rw [eqA e eh,card_neighborFinset_eq_degree,LowSample.two_degree G et])
    (by rw [eqA z zh,card_neighborFinset_eq_degree,LowSample.two_degree G zt]) t fail 10 (by decide) (sz ▸ room.le)
  change (s.card-10+1)*s.card.choose 10+(s.card-2).choose 8+(∑ d∈f,CliqueSample.bonus s.card 10 d)≤
    16*s.card.choose 10 + ∑ k∈s.powersetCard 10,(FiniteRange.bad G s k).card at count
  rw [sz] at count
  have wout : w∉s := fun ws => (mem_sdiff.mp ws).2 (mem_insert_self ..)
  have bout : b∉s := fun bs => (mem_sdiff.mp bs).2 (mem_insert_of_mem (mem_singleton_self _))
  have zout : z∉s := fun zs => (mem_sdiff.mp zt).2 (mem_sdiff.mp (mem_sdiff.mp zs).1).1
  have bc := marked G n priv
    (fun wz => disjoint_left.mp sep we ((G.mem_neighborFinset _ _).mpr wz.symm))
    (fun bz => disjoint_left.mp sep be ((G.mem_neighborFinset _ _).mpr bz.symm))
    wout bout zout (show s.card+f.card=29 by rw [sz]; dsimp [m]; omega)
  have pay := loss G s (fun _ vs => (mem_sdiff.mp (mem_sdiff.mp vs).1).1) ⟨f.card,by omega⟩ sz (sz ▸ room) n
  change (∑ k∈s.powersetCard 10,(FiniteRange.bad G s k).card)+(s.filter (fun v => ∃ x∉s,G.Adj v x)).card*R ≤ charge m (fun j => (s.filter (fun v => G.degree v≤j)).card) at pay
  have wr := ranks G ch wb.ne pins (show trianglesAt G w≤G.degree w/2 by omega) ab h t m
  have deg (v : V) : G.degree v<34 := n ▸ G.degree_lt_card_verts v
  have ww := (mem_sdiff.mp (pins (mem_insert_self ..))).1
  have bb := (mem_sdiff.mp (pins (mem_insert_of_mem (mem_singleton_self b)))).1
  have pos := (Repair.maximal_diversity G (by omega)).2.1
  have floor : 2≤G.degree w/2 := by have := pos w ww; omega
  have other : 2≤B := (pos b bb).trans ab
  have wp := (rates ⟨f.card,by omega⟩ flag ⟨G.degree w,deg w⟩ (mem_filter.mp ww).2).1 floor
  have bp := (rates ⟨f.card,by omega⟩ flag ⟨G.degree b,deg b⟩ (mem_filter.mp bb).2).2.1 other
  change firstPay m flag≤rank m flag (G.degree w/2)+G.degree w*R at wp
  change secondPay m flag≤rank m flag B+G.degree b*R at bp
  change charge m (fun j => (s.filter (fun v => G.degree v≤j)).card) +
    rank m flag (G.degree w/2)+rank m flag B≤charge m (SharedRanks34.limit f) at wr
  change 16*m.choose 10+charge m (SharedRanks34.limit f)+(5+f.card)*R<
    (m-10+1)*m.choose 10+(m-2).choose 8+(∑ d∈f,CliqueSample.bonus m 10 d)+firstPay m flag+secondPay m flag at strict
  have mult := Nat.mul_le_mul_right R bc
  simp only [Nat.add_mul,Nat.one_mul] at mult strict count
  dsimp only [R] at mult strict wp bp pay
  omega

end Graffiti384b.CrossFour34
#print axioms Graffiti384b.CrossFour34.finish_frame


