import OneSlack189
import Mathlib.Combinatorics.SimpleGraph.Finite
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath
open private Graffiti189LongestPath.splice_gap_two Graffiti189LongestPath.pin_data
  Graffiti189LongestPath.mem_distanceTwo Graffiti189LongestPath.dist_two
  Graffiti189LongestPath.no_endpoints from SmallSeparator189
open private Graffiti189LongestPath.OneSlack.exclusive_gap_pin from OneSlack189
set_option linter.unusedSectionVars false
set_option warningAsError true
namespace Graffiti189LongestPath.GapTwin
variable {V : Type*} {G : SimpleGraph V}

private theorem splice_gap_two_allow_midpoint {x y a b : V} (p : G.Walk a b) (hp : p.IsPath)
    (q : G.Walk x y) (hq : q.IsPath)
    (i : ℕ) (hd : ∀ w ∈ q.support, w ∈ p.support → w = p.getVert (i+1)) (hi : i+1 < p.length)
    (h₀ : G.Adj (p.getVert i) x) (h₁ : G.Adj y (p.getVert (i + 2))) :
    ∃ r : G.Walk a b, r.IsPath ∧ r.length = p.length + q.length ∧
      ∀ w : V, w ∈ r.support ↔ w ∈ q.support ∨ (w ∈ p.support ∧ w ≠ p.getVert (i+1)) := by
  induction p generalizing i with
  | nil => simp at hi
  | @cons a u b hau p ih =>
    cases i with
    | zero =>
      cases p with
      | nil => simp at hi
      | @cons u v b huv p =>
        have hax : G.Adj a x := h₀
        have hyv : G.Adj y v := by simpa using h₁
        have ha : a ∉ (cons huv p).support := (cons_isPath_iff _ _).1 hp |>.2
        have hu : u ∉ p.support := (cons_isPath_iff _ _).1 hp.of_cons |>.2
        have hqapp : (q.append (.cons hyv p)).IsPath := by
          rw [isPath_def, support_append, List.nodup_append]
          refine ⟨hq.support_nodup, ?_, ?_⟩
          · simpa only [support_cons, List.tail_cons] using hp.of_cons.of_cons.support_nodup
          · intro t ht ht'
            have hx' : t ∈ p.support := by simpa only [support_cons, List.tail_cons] using ht'
            have eu : t = u := by simpa using hd t ht (by simp [hx'])
            exact hu (eu ▸ hx')
        refine ⟨.cons hax _, hqapp.cons ?_, by simp; omega, ?_⟩
        · rw [mem_support_append_iff]
          intro hh
          rcases hh with hh | hh
          · have e : a = u := by simpa using hd a hh (by simp)
            exact hau.ne e
          · simp only [support_cons, List.mem_cons] at hh
            exact hh.elim (fun e => by
              have h : a = u := by simpa using hd a (e.symm ▸ q.end_mem_support) (by simp)
              exact hau.ne h)
              (fun h => ha (by simp [h]))
        · intro w
          change w ∈ (cons hax _).support ↔ w ∈ q.support ∨
            (w ∈ (cons hau (cons huv p)).support ∧ w ≠ u)
          simp only [support_cons,List.mem_cons,mem_support_append_iff]
          have e : w = y → w ∈ q.support := fun h => h.symm ▸ q.end_mem_support
          have f : w = a → w ≠ u := fun h => h.symm ▸ hau.ne
          have k : w ∈ p.support → w ≠ u := fun h e => hu (e ▸ h)
          constructor
          · rintro (ha' | h | h | h)
            · exact Or.inr ⟨Or.inl ha', f ha'⟩
            · exact Or.inl h
            · exact Or.inl (e h)
            · exact Or.inr ⟨Or.inr (Or.inr h),k h⟩
          · rintro (h | ⟨(h | h | h),hn⟩)
            · exact Or.inr (Or.inl h)
            · exact Or.inl h
            · exact (hn h).elim
            · exact Or.inr (Or.inr (Or.inr h))
    | succ i =>
      have hi' : i+1 < p.length := by simp at hi; omega
      obtain ⟨r,hr,hlen,hsup⟩ := ih hp.of_cons
        i (fun t ht hs => hd t ht (by simp [hs])) hi' h₀ h₁
      refine ⟨.cons hau r,hr.cons ?_,by simp [hlen]; omega,?_⟩
      · rw [hsup]
        intro h
        exact h.elim (fun e => by
          have he : a = p.getVert (i+1) := hd a e (by simp)
          exact ((cons_isPath_iff _ _).1 hp |>.2) (he.symm ▸ p.getVert_mem_support (i+1)))
          (fun e => ((cons_isPath_iff _ _).1 hp |>.2) e.1)
      · intro w
        change w ∈ (cons hau r).support ↔
          w ∈ q.support ∨ (w ∈ (cons hau p).support ∧ w ≠ p.getVert (i+1))
        simp only [support_cons,List.mem_cons,hsup]
        have e : w = a → w ≠ p.getVert (i+1) := by
          intro h h'
          have ht := p.getVert_mem_support (i+1)
          rw [←h',h] at ht
          exact (cons_isPath_iff _ _).1 hp |>.2 ht
        constructor
        · rintro (h | h | ⟨h,h'⟩)
          · exact Or.inr ⟨Or.inl h,e h⟩
          · exact Or.inl h
          · exact Or.inr ⟨Or.inr h,h'⟩
        · rintro (h | ⟨(h | h),h'⟩)
          · exact Or.inr (Or.inl h)
          · exact Or.inl h
          · exact Or.inr (Or.inr ⟨h,h'⟩)


variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

noncomputable def edgesIn (G : SimpleGraph V) (S : Finset V) : Finset (Sym2 V) := by
  classical
  exact G.edgeFinset.filter (fun e => ∀ v ∈ e, v ∈ S)

private lemma edgeMem {S : Finset V} {u v : V} :
    s(u,v) ∈ edgesIn G S ↔ G.Adj u v ∧ u ∈ S ∧ v ∈ S := by
  simp [edgesIn,Sym2.forall_mem_pair]

private lemma edgeCount {S : Finset V} {w : V} (hw : w ∉ S) :
    (edgesIn G (insert w S)).card =
      (edgesIn G S).card + (G.neighborFinset w ∩ S).card := by
  classical
  let T := (G.neighborFinset w ∩ S).image (fun v => s(w,v))
  have e : edgesIn G (insert w S) = edgesIn G S ∪ T := by
    ext z
    refine Sym2.inductionOn z (fun u v => ?_)
    rw [edgeMem,mem_union,edgeMem]
    constructor
    · rintro ⟨ed,hu,hv⟩
      rcases mem_insert.mp hu with hU | hU <;> rcases mem_insert.mp hv with hV | hV
      · exact False.elim (ed.ne (hU.trans hV.symm))
      · subst u
        exact Or.inr (mem_image.mpr ⟨v,mem_inter.mpr ⟨(G.mem_neighborFinset w v).mpr ed,hV⟩,rfl⟩)
      · subst v
        exact Or.inr (mem_image.mpr ⟨u,mem_inter.mpr ⟨(G.mem_neighborFinset w u).mpr ed.symm,hU⟩,Sym2.eq_swap⟩)
      · exact Or.inl ⟨ed,hU,hV⟩
    · rintro (⟨ed,hu,hv⟩ | ht)
      · exact ⟨ed, mem_insert_of_mem hu,mem_insert_of_mem hv⟩
      · obtain ⟨q,hq,he⟩ := mem_image.mp ht
        have hN := (G.mem_neighborFinset w q).mp (mem_inter.mp hq).1
        have hS : q ∈ insert w S := Finset.mem_insert.mpr (Or.inr (mem_inter.mp hq).2)
        rcases Sym2.eq_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact ⟨hN,mem_insert_self _ _,hS⟩
        · exact ⟨hN.symm,hS,mem_insert_self _ _⟩
  have hd : Disjoint (edgesIn G S) T := disjoint_left.mpr (by
    intro z hz h
    obtain ⟨v,_,rfl⟩ := mem_image.mp h
    exact hw (edgeMem.mp hz).2.1)
  have hT : T.card = (G.neighborFinset w ∩ S).card := by
    apply card_image_of_injective
    intro u v e
    rcases Sym2.eq_iff.mp e with ⟨_,he⟩ | ⟨he,hf⟩
    · exact he
    · exact hf.trans he
  rw [e,card_union_of_disjoint hd,hT]

def EdgeMin {a b : V} (p : G.Walk a b) : Prop :=
  IsLongest p ∧ ∀ u v (q : G.Walk u v), IsLongest q →
    (edgesIn G p.support.toFinset).card ≤ (edgesIn G q.support.toFinset).card

/-- A two-pin porter straddling one path vertex forces the latter to have
degree at most four when the longest path minimizes internal edges. -/
theorem gap_two_midpoint_small (hc : G.Connected) (d : ℕ)
    (cap : ∀ w, (EvenFrom G w).card ≤ d+1)
    {a b : V} {p : G.Walk a b} (hMin : EdgeMin p)
    {x : V} (hx : x ∉ p.support) (hd : d ≤ G.degree x)
    (i : ℕ) (hPins : Pins p x = {i,i+2}) :
    ∃ (q : G.Walk a b), EdgeMin q ∧ p.getVert (i+1) ∉ q.support ∧
      G.degree (p.getVert (i+1)) ≤ 4 := by
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
  rw [oldset,qset,edgeCount zS,edgeCount xS,xeq] at cn
  have zeq : G.neighborFinset z ∩ S = L :=
    (eq_of_subset_of_card_le zsub (by omega)).symm
  have hqMin : EdgeMin q := by
    refine ⟨qLongest,fun c w t ht => ?_⟩
    have he := hMin.2 c w t ht
    rw [oldset,edgeCount zS,zeq] at he
    rw [qset,edgeCount xS,xeq]
    exact he
  have znq : z ∉ q.support := by
    intro hh
    have zz : z ∈ insert x S := qset ▸ List.mem_toFinset.mpr hh
    exact (mem_insert.mp zz).elim zx zS
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
  have noflankX {w : V} (hw : w ∈ X) : ¬G.Adj w l := by
    intro h
    have ed := (G.mem_neighborFinset x w).mp (mem_sdiff.mp hw).1
    obtain ⟨q,hq,hLen,_⟩ := Graffiti189LongestPath.splice_gap_two p hp.1 ed.symm.toWalk
      (IsPath.of_adj _)
      (by simp [xOff hw,hx]) i (by omega) h.symm rx
    have hL := hp.2 a b q hq
    simp at hLen
    omega
  have noflankZ {w : V} (hw : w ∈ Z) : ¬G.Adj w l := by
    intro h
    have ed := (G.mem_neighborFinset z w).mp (mem_sdiff.mp hw).1
    -- Avoid the old midpoint only: the replacement can finish at that midpoint.
    obtain ⟨q,hq,hLen,_⟩ := splice_gap_two_allow_midpoint p hp.1 ed.symm.toWalk
      (IsPath.of_adj _) i (by
        intro t ht tp
        have h' : t = w ∨ t = z := by simpa using ht
        exact h'.elim (fun h => (zOff hw (h ▸ tp)).elim) id)
      (by omega) h.symm zr
    have hL := hp.2 a b q hq
    simp at hLen
    omega
  have dis : Disjoint X Z := disjoint_left.mpr (by
    intro w hX hZ
    have xw := (G.mem_neighborFinset x w).mp (mem_sdiff.mp hX).1
    have wz := (G.mem_neighborFinset z w).mp (mem_sdiff.mp hZ).1 |>.symm
    let t : G.Walk x z := Walk.cons xw (Walk.cons wz Walk.nil)
    have hW : t.IsPath := ((IsPath.of_adj wz).cons (by simp [xw.ne,zx.symm]))
    obtain ⟨q,hq,hLen,_⟩ := splice_gap_two_allow_midpoint p hp.1 t hW i (by
      intro u hu hp'
      have hh : u = x ∨ u = w ∨ u = z := by simpa [t] using hu
      exact hh.elim (fun h => (hx (h ▸ hp')).elim)
        (fun h => h.elim (fun he => (xOff hX (he ▸ hp')).elim) id))
      (by omega) lx.symm zr
    have hL := hp.2 a b q hq
    simp [t] at hLen
    omega)
  have sub : X ∪ Z ⊆ DistanceTwo G l := by
    intro w hw
    have lmem := p.getVert_mem_support i
    apply Graffiti189LongestPath.mem_distanceTwo.mpr
    rcases mem_union.mp hw with h | h
    · exact Graffiti189LongestPath.dist_two hc (fun e => xOff h (e ▸ lmem))
        (fun e => noflankX h e.symm) lx.symm
        ((G.mem_neighborFinset x w).mp (mem_sdiff.mp h).1)
    · exact Graffiti189LongestPath.dist_two hc (fun e => zOff h (e ▸ lmem))
        (fun e => noflankZ h e.symm) lz
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
  have bd := distanceTwo_le_of_even d l (cap l)
  change X.card + L.card = G.degree x at cx
  change Z.card + L.card = G.degree z at cz
  refine ⟨q,hqMin,znq,?_⟩
  change G.degree z ≤ 4
  omega

#print axioms gap_two_midpoint_small
end Graffiti189LongestPath.GapTwin
