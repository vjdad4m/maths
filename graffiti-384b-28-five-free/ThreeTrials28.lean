import FrameLinks28
import WeightedRows28

namespace Graffiti384b.Sparse28
open Finset SimpleGraph Thin28 HighSquare28 EarFrame33 JointRank
open private Repair.nbr_mono Repair.nbr_add Repair.full_nbr from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

def payment (W P R : Finset V) (s x : V) :=
  6*hit G W P 8 x+4*hit G W (P∪{s}) 7 x+hit G W R 9 x

/-- All vertices of the frame are protected in each of the three trials. -/
theorem total_needed {P R : Finset V} {s : V} (fr : Frame G P R) (ps : P.card=2)
    (rs : R.card=2) (sr : s∈R) (ws : (P∪R)ᶜ.card=24) (large : 14≤gamma G) :
    27111480≤∑ x∈(P∪R)ᶜ,payment G (P∪R)ᶜ P R s x := by
  classical
  let W := (P∪R)ᶜ
  have st : Disjoint P ({s}:Finset V) := disjoint_singleton_right.mpr (fun h => disjoint_left.mp fr.1 h sr)
  have size : (P∪{s}).card=3 := by rw [card_union_of_disjoint st,ps,card_singleton]
  have zero (x : V) (xo : x∉W) : payment G W P R s x=0 := by
    have mem : x∈P∪R := Classical.byContradiction (fun h => xo (mem_compl.mpr h))
    rcases mem_union.mp mem with xp|xr
    · simp [payment,kept G xp,kept G (mem_union_left ({s}:Finset V) xp),
        supported_zero G 9 (fr.2.1 x xp)]
    · have cover := fr.2.2 x xr
      have more := cover.trans (Repair.nbr_mono G x (show P⊆P∪{s} from subset_union_left))
      simp [payment,kept G xr,supported_zero G 8 cover,supported_zero G 7 more]
  have all : (∑ x∈W,payment G W P R s x)=∑ x,payment G W P R s x :=
    sum_subset (subset_univ _) (fun x _ => zero x)
  change 27111480≤∑ x∈W,payment G W P R s x
  rw [all]; simp only [payment,sum_add_distrib,←mul_sum]
  have t1 := budget G W P 8
  have t2 := budget G W (P∪{s}) 7
  have t3 := budget G W R 9
  change W.card=24 at ws
  rw [ws,ps] at t1; rw [ws,size] at t2; rw [ws,rs] at t3
  have a := (Nat.mul_le_mul_left ((24:ℕ).choose 8) (by omega : 4≤gamma G-2-8)).trans t1
  have b := (Nat.mul_le_mul_left ((24:ℕ).choose 7) (by omega : 4≤gamma G-3-7)).trans t2
  have c := (Nat.mul_le_mul_left ((24:ℕ).choose 9) (by omega : 3≤gamma G-2-9)).trans t3
  change 2941884≤_ at a
  change 1384416≤_ at b
  change 3922512≤_ at c
  omega

/-- At most six vertices are neighbors of the two cubics. All other
eligible exterior vertices receive the four-cycle-free rank bound. -/
theorem total_allowed {P R : Finset V} {e s u v : V} (fr : Frame G P R)
    (ps : P.card=2) (sr : s∈R) (ws : (P∪R)ᶜ.card=24) (em : e∈P∪R)
    (pos : ∀ w,0<trianglesAt G w) (fi : Function.Injective (trianglesAt G))
    (ear : trianglesAt G e=1) (two : trianglesAt G u=2) (three : trianglesAt G v=3)
    (du : G.degree u=3) (dv : G.degree v=3) (free : G.CliqueFree 5) (half : Fintype.card V≤2*gamma G)
    (contact : ∀ x∈(P∪R)ᶜ,nbr G x R=nbr G x {s}) :
    (∑ x∈(P∪R)ᶜ,payment G (P∪R)ᶜ P R s x)≤26398538 := by
  classical
  let W := (P∪R)ᶜ
  let E := G.neighborFinset u∪G.neighborFinset v
  let rk := rank W (trianglesAt G)
  change W.card=24 at ws
  have ec : E.card≤6 := by
    have z := card_union_le (G.neighborFinset u) (G.neighborFinset v)
    rwa [card_neighborFinset_eq_degree,card_neighborFinset_eq_degree,du,dv] at z
  have st : Disjoint P ({s}:Finset V) := disjoint_singleton_right.mpr (fun h => disjoint_left.mp fr.1 h sr)
  have pw : Disjoint P W := disjoint_left.mpr (fun x px wx => mem_compl.mp wx (mem_union_left R px))
  have rw' : Disjoint R W := disjoint_left.mpr (fun x rx wx => mem_compl.mp wx (mem_union_right P rx))
  have sw : Disjoint (P∪{s}) W := disjoint_union_left.mpr ⟨pw,rw'.mono_left (singleton_subset_iff.mpr sr)⟩
  have scores (z : V) (zm : z∈W) : 2≤trianglesAt G z := by
    have diff : trianglesAt G z≠1 := fun h => mem_compl.mp zm ((fi (h.trans ear.symm)) ▸ em)
    have h := pos z; omega
  have per (x : V) (xm : x∈W) : payment G W P R s x≤price (rk x)+(if x∈E then 636922 else 0) := by
    have ri := mem_image_of_mem (rank W (trianglesAt G)) xm
    rw [rank_range _ _ fi.injOn,ws,mem_range] at ri
    have lb : rk x+2≤trianglesAt G x := by simpa [rk,Nat.add_comm] using rank_lower W (trianglesAt G) fi.injOn 2 scores xm
    let d := nbr G x W
    let p := nbr G x P
    let c := nbr G x {s}
    have dd : d<24 := (pool_degree G xm).trans_le ws.le
    have pp : p≤2 := (card_filter_le ..).trans ps.le
    have cc : c≤1 := (card_filter_le ..).trans (card_singleton s).le
    have frame : nbr G x (P∪R)=p+c := by rw [Repair.nbr_add G x fr.1,contact x xm]
    have joined : nbr G x (P∪{s})=p+c := Repair.nbr_add G x st
    have dg := Repair.full_nbr G x W
    rw [show Wᶜ=P∪R from compl_compl _,frame] at dg
    have size : d+p+c=G.degree x := by simpa [d,Nat.add_assoc] using dg
    have cap := (local_cap G free x).imp_left lb.trans
    have table := rows ⟨rk x,ri⟩ ⟨d,dd⟩ ⟨p,by omega⟩ ⟨c,by omega⟩ (by change rk x+2≤RankTable.cap (d+p+c) 3 ∨ 10≤d+p+c; rwa [size])
    dsimp only at table
    have cover : payment G W P R s x≤Sparse28.mass d p c := by
      have a := bill_bound G pw xm 8
      have b := bill_bound G sw xm 7
      have z := bill_bound G rw' xm 9
      rw [ws] at a; rw [ws,joined] at b; rw [ws,contact x xm] at z
      exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left 6 a) (Nat.mul_le_mul_left 4 b)) z
    apply cover.trans
    by_cases ex : x∈E
    · rw [if_pos ex]; exact table.1
    · rw [if_neg ex,Nat.add_zero]
      apply table.2
      intro small short
      have ux : ¬G.Adj u x := fun h => ex (mem_union_left _ ((G.mem_neighborFinset ..).mpr h))
      have vx : ¬G.Adj v x := fun h => ex (mem_union_right _ ((G.mem_neighborFinset ..).mpr h))
      have sparse := sparse_link G fr em pos fi ear two three half (mem_compl.mp xm) ux vx (frame ▸ small)
      have cert := square_bound G (G.neighborFinset x) (by rw [card_neighborFinset_eq_degree,←size]; exact short) sparse
      rw [card_neighborFinset_eq_degree,←size] at cert
      exact lb.trans cert
  have bound := sum_le_sum per
  rw [sum_add_distrib] at bound
  have rc := sum_by_rank W (trianglesAt G) fi.injOn price
  rw [ws,totals.1] at rc
  change (∑ x∈W,price (rk x))=22577006 at rc
  have count : (∑ x∈W,if x∈E then 636922 else 0)≤6*636922 := by
    rw [←sum_filter, sum_const,nsmul_eq_mul,filter_mem_eq_inter]
    exact Nat.mul_le_mul_right _ ((card_le_card inter_subset_right).trans ec)
  change (∑ x∈W,payment G W P R s x)≤26398538
  omega

end Graffiti384b.Sparse28
#print axioms Graffiti384b.Sparse28.total_needed
#print axioms Graffiti384b.Sparse28.total_allowed
