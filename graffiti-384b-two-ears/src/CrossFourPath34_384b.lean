import CrossFourTriangle34_384b
import SharedExact34_384b
import TwoEdgeLink34_384b
import CrossFourFrame34_384b

namespace Graffiti384b.CrossFour34
open Finset SimpleGraph CliqueChoice LowSample
open private LowSample.anchors LowSample.two_degree from LowSample384b
open private Repair.nbr_mono from Repair384b
open private TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

theorem at_endpoint {y z w : V} (ears : twos G={y,z})
    (pos : ∀ e∈twos G,0<trianglesAt G e) (sep : Disjoint (G.neighborFinset y) (G.neighborFinset z))
    (free : triangleFreeOn G ((twos G).biUnion (G.neighborFinset ·)))
    (ww : w∈(twos G).biUnion (G.neighborFinset ·))
    (blind : ∀ x∈ForkGuard34.candidates G ((twos G).biUnion (G.neighborFinset ·)),¬G.Adj w x)
    (small : ∀ x∈ForkGuard34.row G ((twos G).biUnion (G.neighborFinset ·)) w,
      nbr G x (ForkGuard34.row G ((twos G).biUnion (G.neighborFinset ·)) w)≤1) :
    let W := (twos G).biUnion (G.neighborFinset ·)
    ∃ e∈({y,z} : Finset V),∃ b∈W,G.neighborFinset e={w,b} ∧ G.Adj w b ∧
      G.Adj e w ∧ G.Adj e b ∧ G.neighborFinset w∩G.neighborFinset b={e} ∧
      (∀ x∈G.neighborFinset w,nbr G x (G.neighborFinset w)≤1) := by
  let W := (twos G).biUnion (G.neighborFinset ·)
  obtain ⟨e,et,we⟩ := mem_biUnion.mp ww
  have ew := (G.mem_neighborFinset _ _).mp we
  have only (v : V) (vt : v∈twos G) (wv : G.Adj w v) : v=e := by
    by_contra ne
    have ec := (show e∈({y,z} : Finset V) from ears ▸ et)
    have vc := (show v∈({y,z} : Finset V) from ears ▸ vt)
    have vm := (G.mem_neighborFinset _ _).mpr wv.symm
    simp only [mem_insert,mem_singleton] at ec vc
    rcases ec with ey|ez <;> rcases vc with vy|vz
    · exact ne (vy.trans ey.symm)
    · exact disjoint_left.mp sep (ey ▸ we) (vz ▸ vm)
    · exact disjoint_left.mp sep (vy ▸ vm) (ez ▸ we)
    · exact ne (vz.trans ez.symm)
  have ec : e∈({y,z} : Finset V) := ears ▸ et
  have all (v : V) (vt : v∈twos G) : G.neighborFinset v⊆W := fun _ m => mem_biUnion.mpr ⟨v,vt,m⟩
  obtain ⟨i,j,eq,ei,ej,ij⟩ := SharedExact34.ear_pair G (LowSample.two_degree G et) (pos e et)
  have pair : ∃ b∈W,G.neighborFinset e={w,b} ∧ G.Adj w b ∧ G.Adj e b := by
    rw [eq,mem_insert,mem_singleton] at we
    rcases we with rfl|rfl
    · exact ⟨j,all e et ((G.mem_neighborFinset _ _).mpr ej),eq,ij,ej⟩
    · exact ⟨i,all e et ((G.mem_neighborFinset _ _).mpr ei),eq.trans (pair_comm ..),ij.symm,ei⟩
  obtain ⟨b,bw,ear,wb,eb⟩ := pair
  have supported {x j : V} (xw : x∈W) (wx : G.Adj w x) (wj : G.Adj w j) (xj : G.Adj x j) : x=b := by
    by_cases jw : j∈W
    · exact (free w ww x xw j jw wx wj xj).elim
    by_cases jh : j∈high G
    · exact (blind j (mem_filter.mpr ⟨mem_sdiff.mpr ⟨jh,jw⟩,
        PinnedColor34.two G wx.ne wj.symm xj.symm ww xw⟩) wj).elim
    have sub := insert_subset ((G.mem_neighborFinset _ _).mpr wj.symm)
      (singleton_subset_iff.mpr ((G.mem_neighborFinset _ _).mpr xj.symm))
    have le := card_le_card sub
    rw [card_pair wx.ne,card_neighborFinset_eq_degree] at le
    have je := only j (mem_sdiff.mpr ⟨mem_filter.mpr ⟨mem_univ _,le⟩,jh⟩) wj
    have xm := (G.mem_neighborFinset _ _).mpr (je ▸ xj.symm)
    rw [ear,mem_insert,mem_singleton] at xm
    exact xm.resolve_left wx.ne.symm
  let P : Finset V := {w,b}
  have pw : P⊆W := insert_subset ww (singleton_subset_iff.mpr bw)
  have single (x : V) (xp : x∈P) (wx : G.Adj w x) : x=b := (mem_insert.mp xp).elim
    (fun eq => (wx.ne eq.symm).elim) mem_singleton.mp
  have blindP (x : V) (xm : x∈ForkGuard34.candidates G P) (wx : G.Adj w x) : False := by
    obtain ⟨hh,hit⟩ := mem_filter.mp xm
    have hitW := hit.trans (Repair.nbr_mono G x pw)
    by_cases xw : x∈W
    · have inc : P⊆P.filter (G.Adj x) := by
        rw [eq_of_subset_of_card_le (filter_subset (G.Adj x) P)
          (show P.card≤nbr G x P by rw [show P.card=2 from card_pair wb.ne]; exact hit)]
      have xb := (mem_filter.mp (inc (mem_insert_of_mem (mem_singleton_self b)))).2
      exact xb.ne (supported xw wx wb xb)
    · exact blind x (mem_filter.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp hh).1,xw⟩,hitW⟩) wx
  have matchP (x : V) (xr : x∈ForkGuard34.row G P w) : nbr G x (ForkGuard34.row G P w)≤1 := by
    obtain ⟨xh,wx⟩ := mem_filter.mp xr
    by_cases non : ((ForkGuard34.row G P w).filter (G.Adj x)).Nonempty
    · obtain ⟨j,jm⟩ := non
      obtain ⟨jr,xj⟩ := mem_filter.mp jm
      have xw : x∉W := fun xw => (mem_sdiff.mp xh).2 (mem_insert_of_mem
        (mem_singleton.mpr (supported xw wx (mem_filter.mp jr).2 xj)))
      have inc : (ForkGuard34.row G P w).filter (G.Adj x)⊆(ForkGuard34.row G W w).filter (G.Adj x) := by
        intro i im
        obtain ⟨ir,xi⟩ := mem_filter.mp im
        obtain ⟨ih,wi⟩ := mem_filter.mp ir
        have iw : i∉W := fun iw => (mem_sdiff.mp ih).2 (mem_insert_of_mem
          (mem_singleton.mpr (supported iw wi wx xi.symm)))
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp ih).1,iw⟩,wi⟩,xi⟩
      exact (card_le_card inc).trans (small x (mem_filter.mpr ⟨mem_sdiff.mpr ⟨(mem_sdiff.mp xh).1,xw⟩,wx⟩))
    · exact (card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp non)).le.trans (Nat.zero_le 1)
  obtain ⟨priv,thin⟩ := TwoEdge34.link G (show w∈P from mem_insert_self ..)
    (show b∈P from mem_insert_of_mem (mem_singleton_self _)) wb ew eb ear single only blindP matchP
  exact ⟨e,ec,b,bw,ear,wb,ew,eb,priv,thin⟩

/-- This includes the four-vertex anchor path. -/
theorem path (n : Fintype.card V=34) (t : (types G).card=33) {y z : V} (yz : y≠z)
    (dy : G.degree y=2) (dz : G.degree z=2) (py : 0<trianglesAt G y) (pz : 0<trianglesAt G z)
    (free : triangleFreeOn G ((twos G).biUnion (G.neighborFinset ·))) :
    gamma G≤bound G := by
  classical
  by_contra! fail
  obtain ⟨q,h,ears,_,hi⟩ := SharedExact34.failure_profile G t yz dy dz py pz fail
  have sep := SharedExact34.separate G n t yz dy dz py pz fail
  have yt : y∈twos G := ears ▸ mem_insert_self .. 
  have zt : z∈twos G := ears ▸ mem_insert_of_mem (mem_singleton_self _)
  let W := (twos G).biUnion (G.neighborFinset ·)
  have wh : W⊆high G := by
    intro w wm
    obtain ⟨e,et,em⟩ := mem_biUnion.mp wm
    rw [ears,mem_insert,mem_singleton] at et
    exact hi (et.elim (fun val => mem_union_left _ (val ▸ em)) (fun val => mem_union_right _ (val ▸ em)))
  have all (v : V) (vt : v∈twos G) : G.neighborFinset v⊆W := fun _ m => mem_biUnion.mpr ⟨v,vt,m⟩
  have anchor (w : V) (wm : w∈W) : ∃ e∈twos G,G.Adj w e := by
    obtain ⟨e,et,em⟩ := mem_biUnion.mp wm
    exact ⟨e,et,((G.mem_neighborFinset _ _).mp em).symm⟩
  have pos (e : V) (et : e∈twos G) : 0<trianglesAt G e := by
    rw [ears,mem_insert,mem_singleton] at et
    exact et.elim (fun val => val ▸ py) (fun val => val ▸ pz)
  obtain ⟨w,ww,blind,small⟩ := ForkGuard34.matching G wh all anchor (by omega) fail
  obtain ⟨e,ec,b,_,ear,wb,_,_,priv,thin⟩ := at_endpoint G ears pos sep free ww blind small
  have score := TwoEdge34.half_degree G thin
  rcases mem_insert.mp ec with ey|m
  · subst e
    exact (not_lt_of_ge (finish_frame G n t h yt zt yz hi sep ear wb priv score)) fail
  · obtain rfl := mem_singleton.mp m
    exact (not_lt_of_ge (finish_frame G n t h zt yt yz.symm (by rw [union_comm]; exact hi) sep.symm ear wb priv score)) fail

end Graffiti384b.CrossFour34
#print axioms Graffiti384b.CrossFour34.at_endpoint
#print axioms Graffiti384b.CrossFour34.path


