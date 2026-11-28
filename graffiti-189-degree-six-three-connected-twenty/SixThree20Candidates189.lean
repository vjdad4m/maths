import SixThree20ThirteenDouble189

namespace Graffiti189LongestPath.SixThreeTwenty
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open Graffiti189LongestPath.Rigidity Graffiti189LongestPath.OneSlack
open Graffiti189LongestPath.SixThreeEighteen (LM RM high_filter_card left_right_disjoint)
open Graffiti189LongestPath.SixThreeNineteen (holes_card_le_one missed_start_hole missed_end_hole)
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.reverse_longest Graffiti189LongestPath.Rigidity.pin_pos
  Graffiti189LongestPath.Rigidity.card_leftMarks Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem from OneSlack189
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def CandL {a b : V} (p : G.Walk a b) := (LM p).image p.getVert
def CandR {a b : V} (p : G.Walk a b) := (RM p).image (fun i=>p.getVert (i+1))
def CandHigh {a b : V} (p : G.Walk a b) :=
  (CandL p∪CandR p).filter (fun v=>6≤G.degree v)

theorem cand_left_card {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    (CandL p).card=G.degree a := by
  have eq : (CandL p).card=(LM p).card :=
    card_image_iff.mpr (fun j jm k km e=>hp.1.getVert_injOn
      (mem_range.mp (mem_filter.mp jm).1).le (mem_range.mp (mem_filter.mp km).1).le e)
  exact eq.trans (Graffiti189LongestPath.Rigidity.card_leftMarks hp)

theorem cand_right_card {a b : V} {p : G.Walk a b} (hp : IsLongest p) :
    (CandR p).card=G.degree b := by
  have eq : (CandR p).card=(RM p).card := card_image_iff.mpr (fun j jm k km e=>by
    have jl := mem_range.mp (mem_filter.mp jm).1
    have kl := mem_range.mp (mem_filter.mp km).1
    have t := hp.1.getVert_injOn (by omega : j+1≤p.length) (by omega : k+1≤p.length) e
    omega)
  exact eq.trans (Graffiti189LongestPath.Rigidity.card_rightMarks hp)

theorem orig_cand {a b : V} {p : G.Walk a b} (hp : IsLongest p) (pos : 0<p.length) :
    a∈CandL p ∧ a∉CandR p ∧ b∈CandR p ∧ b∉CandL p := by
  have aL : a∈CandL p := by
    have e := p.adj_getVert_succ (i:=0) pos
    exact mem_image.mpr ⟨0,mem_filter.mpr ⟨mem_range.mpr pos,by simpa using e⟩,p.getVert_zero⟩
  have aR : a∉CandR p := by
    intro h
    obtain ⟨i,im,e⟩ := mem_image.mp h
    have il := mem_range.mp (mem_filter.mp im).1
    have t := hp.1.getVert_injOn (by omega : i+1≤p.length) (Nat.zero_le _) (e.trans p.getVert_zero.symm)
    omega
  have bR : b∈CandR p := by
    have il : p.length-1<p.length := by omega
    have e := p.adj_getVert_succ il
    have h : p.length-1+1=p.length := by omega
    rw [h,getVert_length] at e
    exact mem_image.mpr ⟨p.length-1,mem_filter.mpr ⟨mem_range.mpr il,e.symm⟩,
      by rw [h,getVert_length]⟩
  have bL : b∉CandL p := by
    intro h
    obtain ⟨i,im,e⟩ := mem_image.mp h
    have il := mem_range.mp (mem_filter.mp im).1
    have t := hp.1.getVert_injOn il.le (show p.length ≤ p.length from le_rfl) (e.trans p.getVert_length.symm)
    omega
  exact ⟨aL,aR,bR,bL⟩

theorem cand_high_ge_six {a b : V} {p : G.Walk a b} (hp : IsLongest p) (pos : 0<p.length)
    (da : 6≤G.degree a) (_db : 6≤G.degree b)
    (degree : ∀ u v : V,u≠v → 6≤G.degree u ∨ 6≤G.degree v) : 6≤(CandHigh p).card := by
  have bOut := (orig_cand hp pos).2.2.2
  have bIn := (orig_cand hp pos).2.2.1
  have lc := cand_left_card hp
  have e := card_le_card (show insert b (CandL p)⊆CandL p∪CandR p from
    fun u h=>(mem_insert.mp h).elim (fun eq=>mem_union_right _ (eq.symm ▸ bIn)) (mem_union_left _))
  rw [card_insert_of_not_mem bOut] at e
  have d := high_filter_card degree (CandL p∪CandR p)
  change (CandL p∪CandR p).card≤(CandHigh p).card+1 at d
  omega

theorem cand_rotated_path {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {u : V} (um : u∈CandL p∪CandR p) :
    ∃ v, ∃ q : G.Walk u v, IsLongest q ∧ (∀ w,w∈p.support ↔ w∈q.support) ∧ q.length=p.length ∧ (v=a ∨ v=b) := by
  rcases mem_union.mp um with l|r
  · obtain ⟨j,jm,rfl⟩ := mem_image.mp l
    obtain ⟨q,hq,same,ql,_,_⟩ := rotate_start hp j (mem_range.mp (mem_filter.mp jm).1) (mem_filter.mp jm).2
    exact ⟨b,q,hq,same,ql,.inr rfl⟩
  obtain ⟨j,jm,rfl⟩ := mem_image.mp r
  let t := p.length-(j+1)
  have jl := mem_range.mp (mem_filter.mp jm).1
  have eq : p.reverse.getVert t=p.getVert (j+1) := by rw [getVert_reverse]; congr 1; dsimp only [t]; omega
  have e : p.reverse.getVert (t+1)=p.getVert j := by rw [getVert_reverse]; congr 1; dsimp only [t]; omega
  have tl : t<p.reverse.length := by rw [length_reverse]; dsimp only [t]; omega
  obtain ⟨q,hq,same,ql,_,_⟩ := rotate_start (Graffiti189LongestPath.Rigidity.reverse_longest hp) t tl
    (by rw [e]; exact (mem_filter.mp jm).2)
  let q' := q.copy eq rfl
  have sm : q'.support=q.support := by simp [q']
  have ln : q'.length=q.length := by simp [q']
  have hq' : IsLongest q' := ⟨IsPath.mk' (sm.symm ▸ hq.1.support_nodup),fun x y r rp=>ln.symm ▸ hq.2 x y r rp⟩
  exact ⟨a,q',hq',fun w=>by rw [sm,←same]; simp, (ln.trans ql).trans (length_reverse _),.inl rfl⟩

theorem cand_no_omitted_edge {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    {u x : V} (um : u∈CandL p∪CandR p) (xo : x∉p.support) : ¬G.Adj x u := by
  obtain ⟨v,q,hq,same,ql,ve⟩ := cand_rotated_path hp um
  exact (Graffiti189LongestPath.no_endpoints hq (fun h=>xo ((same x).mpr h))).1

theorem high_candidate_cannot_miss_two_at_thirteen {a b : V} {p : G.Walk a b}
    (hp : IsLongest p) (len : p.length≤13) (da : 6≤G.degree a) (db : 6≤G.degree b)
    {v x y r s : V} (vm : v∈CandHigh p) (xo : x∉p.support) (yo : y∉p.support)
    (ro : r∈p.support) (so : s∈p.support) (xr : G.Adj x r) (ys : G.Adj y s) (rs : r≠s) :
    G.Adj v r ∨ G.Adj v s := by
  classical
  by_contra no
  obtain ⟨inE,dv⟩ := mem_filter.mp vm
  obtain ⟨u,q,hq,same,ql,ue⟩ := cand_rotated_path hp inE
  have du : 6≤G.degree u := ue.elim (fun e=>e.symm ▸ da) (fun e=>e.symm ▸ db)
  have xq : x∉q.support := fun h=>xo ((same x).mpr h)
  have yq : y∉q.support := fun h=>yo ((same y).mpr h)
  obtain ⟨i,ip,ie⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hq xq ((same r).mp ro) xr
  obtain ⟨j,jp,je⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hq yq ((same s).mp so) ys
  have h := holes_card_le_one hq (ql ▸ len) dv du xq ip
  have iHole := missed_start_hole hq xq ip (by rw [ie]; exact fun e=>no (.inl e))
  have jHole := missed_start_hole hq yq jp (by rw [je]; exact fun e=>no (.inr e))
  have eq := card_le_one.mp h (i-1) iHole (j-1) jHole
  have i0 := Graffiti189LongestPath.Rigidity.pin_pos hq xq ip
  have j0 := Graffiti189LongestPath.Rigidity.pin_pos hq yq jp
  have ij : i=j := by omega
  exact rs (ie.symm.trans (ij ▸ je))

#print axioms cand_rotated_path
#print axioms high_candidate_cannot_miss_two_at_thirteen
end Graffiti189LongestPath.SixThreeTwenty
