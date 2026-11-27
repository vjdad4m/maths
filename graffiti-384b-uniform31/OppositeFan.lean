import TenGap
import FlexibleTip
namespace Graffiti384b.TenPins
open Finset SimpleGraph EarFrame33 EightPins SparsePairs
open private Squares29.pair_at from SquareTriple29
open private CubicShore.square_frame from CubicDiamondCut33
open private Repair.nbr_mono from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
private theorem plug {P Q L R : Finset V} {b : V} (tip : Tip G P Q b) (fr : Frame G L R)
    (bl : b∈L) (pr : Disjoint P R) (lq : Disjoint L Q) : Frame G (P∪L) (Q∪R) := by
  refine ⟨by simp only [disjoint_union_left,disjoint_union_right]; exact ⟨⟨tip.dis,lq⟩,pr,fr.1⟩,?_,?_⟩
  · intro v vm; rcases mem_union.mp vm with vp|vl
    · by_cases vb : v=b
      · exact (fr.2.1 v (vb ▸ bl)).trans (Repair.nbr_mono G _ subset_union_right)
      · exact (tip.left v vp vb).trans (Repair.nbr_mono G _ subset_union_left)
    · exact (fr.2.1 v vl).trans (Repair.nbr_mono G _ subset_union_right)
  · intro v vm; rcases mem_union.mp vm with vq|vr
    · exact (tip.right v vq).trans (Repair.nbr_mono G _ subset_union_left)
    · exact (fr.2.2 v vr).trans (Repair.nbr_mono G _ subset_union_right)

/-- If the other three anchors form a triangle, putting the ears on opposite
sides leaves only their fourth anchor b pending. A cross edge, a vertex shared
with its mate, or a private fork completes it. -/
theorem missing_pin {e f b : V} (ef : e≠f) (de : G.degree e=2) (df : G.degree f=2)
    (bad : bound G<gamma G) (A : Finset V) (ae : G.neighborFinset e∪G.neighborFinset f=A)
    (data : AnchorData G A) (dis : Disjoint (G.neighborFinset e) (G.neighborFinset f))
    (bn : b∈G.neighborFinset e) (gap : 10≤trianglesAt G b)
    (cl : ∀x∈A.erase b,∀y∈A.erase b,x≠y → G.Adj x y) : False := by
  classical
  let X := high G\A
  let R := X.filter (G.Adj b)
  obtain ⟨h,bh,en⟩ := Squares29.pair_at ((card_neighborFinset_eq_degree ..).trans de) bn
  obtain ⟨c,d,cd,fn'⟩ := card_eq_two.mp ((card_neighborFinset_eq_degree ..).trans df)
  have hn : h∈G.neighborFinset e := en ▸ mem_insert_of_mem (mem_singleton_self _)
  have cn : c∈G.neighborFinset f := fn' ▸ mem_insert_self ..
  have dn : d∈G.neighborFinset f := fn' ▸ mem_insert_of_mem (mem_singleton_self _)
  have apart {u v : V} (ue : u∈G.neighborFinset e) (vf : v∈G.neighborFinset f) : u≠v :=
    fun z => disjoint_left.mp dis ue (z ▸ vf)
  have ba : b∈A := ae ▸ mem_union_left _ bn
  have ha : h∈A := ae ▸ mem_union_left _ hn
  have ca : c∈A := ae ▸ mem_union_right _ cn
  have da : d∈A := ae ▸ mem_union_right _ dn
  have be := ((G.mem_neighborFinset ..).mp bn).symm
  have eh := (G.mem_neighborFinset ..).mp hn
  have fc := (G.mem_neighborFinset ..).mp cn
  have fd := (G.mem_neighborFinset ..).mp dn
  have hc := cl h (mem_erase.mpr ⟨bh.symm,ha⟩) c (mem_erase.mpr ⟨(apart bn cn).symm,ca⟩) (apart hn cn)
  have hd := cl h (mem_erase.mpr ⟨bh.symm,ha⟩) d (mem_erase.mpr ⟨(apart bn dn).symm,da⟩) (apart hn dn)
  have off {v z : V} (vh : v∈high G) (dz : G.degree z=2) : v≠z := by
    rintro rfl; have l := (mem_filter.mp vh).2; omega
  let P : Finset V := {f,b,h}
  let Q : Finset V := {e,c,d}
  have sep : Disjoint P Q := by
    simp [P,Q,disjoint_left,ef.symm,(off (data.highPins ca) df).symm,(off (data.highPins da) df).symm,
      off (data.highPins ba) de,off (data.highPins ha) de,apart bn cn,apart bn dn,apart hn cn,apart hn dn]
  have tip : Tip G P Q b := by
    refine ⟨sep,by simp [P],⟨e,by simp [Q],be⟩,?_,?_⟩
    · intro a am ab; simp only [P,mem_insert,mem_singleton] at am
      rcases am with rfl|rfl|rfl
      · exact PinnedColor34.two G cd fc fd (by simp [Q]) (by simp [Q])
      · exact (ab rfl).elim
      · exact PinnedColor34.two G cd hc hd (by simp [Q]) (by simp [Q])
    · intro a am; simp only [Q,mem_insert,mem_singleton] at am
      rcases am with rfl|rfl|rfl
      · exact PinnedColor34.two G bh be.symm eh (by simp [P]) (by simp [P])
      · exact PinnedColor34.two G (off (data.highPins ha) df).symm fc.symm hc.symm (by simp [P]) (by simp [P])
      · exact PinnedColor34.two G (off (data.highPins ha) df).symm fd.symm hd.symm (by simp [P]) (by simp [P])
  have stop {U W : Finset V} (pu : P⊆U) (qw : Q⊆W) (fr : Frame G U W) : False :=
    ef (Squares29.sparse G bad _ _ fr e (mem_union_right _ (qw (by simp [Q]))) f (mem_union_left _ (pu (by simp [P]))) de df)
  have noCross {a : V} (af : a∈G.neighborFinset f) : ¬G.Adj b a := by
    intro ab; have aq : a∈Q := mem_insert_of_mem (fn' ▸ af)
    have good := PinnedColor34.two G (off (data.highPins (ae ▸ mem_union_right _ af)) de).symm be ab (show e∈Q by simp [Q]) aq
    apply stop Subset.rfl Subset.rfl
    exact ⟨tip.dis,fun v vm => by by_cases eq : v=b; exact eq ▸ good; exact tip.left v vm eq,tip.right⟩
  have free {z : V} (zx : z∈X) : z∉P ∧ z∉Q := by
    obtain ⟨zh,za⟩ := mem_sdiff.mp zx
    have n (v : V) (va : v∈A) : z≠v := fun eq => za (eq ▸ va)
    simp [P,Q,off zh df,off zh de,n b ba,n h ha,n c ca,n d da]
  have noShared {z : V} (zr : z∈R) : ¬G.Adj h z := by
    intro hz; have zx := (mem_filter.mp zr).1; have bz := (mem_filter.mp zr).2
    have sq := CubicShore.square_frame G be bz eh hz.symm bh (off (mem_sdiff.mp zx).1 de).symm
    have pr : Disjoint P {e,z} := disjoint_left.mpr (by
      intro v vp vm; rcases mem_insert.mp vm with rfl|hit
      · exact disjoint_left.mp sep vp (by simp [Q])
      · exact (free zx).1 (mem_singleton.mp hit ▸ vp))
    have lq : Disjoint ({b,h}:Finset V) Q := sep.mono_left (by dsimp [P]; exact subset_insert ..)
    exact stop subset_union_left subset_union_left (plug G tip sq (mem_insert_self ..) pr lq)
  have matching (v : V) (vr : v∈R) : nbr G v R≤1 := by
    by_contra! many
    obtain ⟨l,lm,r,rm,lr⟩ := one_lt_card.mp (show 1<(R.filter (G.Adj v)).card from many)
    obtain ⟨lR,vl⟩ := mem_filter.mp lm; obtain ⟨rR,vR⟩ := mem_filter.mp rm
    have adj {a : V} (ar : a∈R) := (mem_filter.mp ar).2
    have sq := CubicShore.square_frame G (adj lR) (adj rR) vl.symm vR.symm (adj vr).ne lr
    have pr : Disjoint P {l,r} := disjoint_left.mpr (by
      intro z zp zm; rcases mem_insert.mp zm with rfl|h'
      · exact (free (mem_filter.mp lR).1).1 zp
      · exact (free (mem_filter.mp rR).1).1 (mem_singleton.mp h' ▸ zp))
    have lq : Disjoint ({b,v}:Finset V) Q := disjoint_left.mpr (by
      intro z zm zq; rcases mem_insert.mp zm with rfl|h'
      · exact disjoint_left.mp sep tip.onSide zq
      · exact (free (mem_filter.mp vr).1).2 (mem_singleton.mp h' ▸ zq))
    exact stop subset_union_left subset_union_left (plug G tip sq (mem_insert_self ..) pr lq)
  have mix : ∀i∈X,∀j∈A,G.Adj b i → G.Adj b j → ¬G.Adj i j := by
    intro i ix j ja bi bj ij; rw [←ae] at ja
    rcases mem_union.mp ja with je|jf
    · rw [en,mem_insert,mem_singleton] at je
      exact je.elim (fun z => bj.ne z.symm) (fun z => noShared (mem_filter.mpr ⟨ix,bi⟩) (z ▸ ij.symm))
    · exact noCross jf bj
  obtain ⟨p,pa,pd⟩ := data.sparsePin
  have cap := link_budget G A data.four ba pa pd (data.singleEar b ba) false true (fun _ => matching) (fun _ => mix)
  have sz := data.rowSize b ba
  simp only [Bool.false_eq_true,if_false,if_true,Nat.add_zero] at cap
  split at cap <;> omega

end Graffiti384b.TenPins
#print axioms Graffiti384b.TenPins.missing_pin
