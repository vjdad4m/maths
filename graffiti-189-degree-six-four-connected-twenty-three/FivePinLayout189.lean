import FiveCheapBudget189
import WideWing189
import DenseOwnerRoute189
import MarkedWingPath189
import Interior189
import GapStrong189
open private Graffiti189LongestPath.WideWing.inside_deg Graffiti189LongestPath.WideWing.two_per_block from WideWing189
open SimpleGraph SimpleGraph.Walk Finset Graffiti189LongestPath
open Graffiti189LongestPath.Normalize Graffiti189LongestPath.GapTwin
open Graffiti189LongestPath.OneSlack Graffiti189LongestPath.Rigidity
open Graffiti189LongestPath.GapStrong Graffiti189LongestPath.WideWing
open Graffiti189LongestPath.Interior Graffiti189LongestPath.HighDichotomy
open private Graffiti189LongestPath.pin_data Graffiti189LongestPath.no_endpoints
  Graffiti189LongestPath.boundary_card_of_connectivity from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.pin_pos
  Graffiti189LongestPath.Rigidity.LeftMarks Graffiti189LongestPath.Rigidity.RightMarks
  Graffiti189LongestPath.Rigidity.card_leftMarks Graffiti189LongestPath.Rigidity.card_rightMarks from Rigidity189
open private Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem
  Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary
  Graffiti189LongestPath.OneSlack.card_pinVertices from OneSlack189
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 15000000
namespace Graffiti189LongestPath.FivePinLayout
open Graffiti189LongestPath.FiveCheapBudget
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_layout (hc : G.Connected) (k : ℕ) (hk : k=4)
    (cap : ∀ v,(EvenFrom G v).card≤k+3)
    (conn : ∀ S : Finset V,S.card<k → (G.induce ((↑S:Set V)ᶜ)).Connected)
    (deg : ∀ u v : V,u≠v → k+2≤G.degree u ∨ k+2≤G.degree v)
    {a b : V} {p : G.Walk a b} (hp : IsLongest p) (hMin : EdgeMinAvoid (k+2) p)
    (C : OmittedComponent p) (h : C.vertices.card=5) (plen : p.length=17)
    (full : ∀ v,v∈p.support ∨ v∈C.vertices)
    (few : ∀ z∈C.vertices,(Pins p z).card≤2)
    (low : ∀ z∈C.vertices,k+2-2≤G.degree z) :
    ∃ x y i j s t, PairData p C.vertices x y i j s t ∧
      (∀ z∈C.vertices,∀ m∈Pins p z,m∈({i,j,s,t}:Finset ℕ)) := by
  classical
  let H := C.vertices
  have hO : ∀ v∈H,v∉p.support := C.off
  have hN : H.Nonempty := C.nonempty
  have hsize : H.card=5 := h
  let Q := G.induce (H:Set V)
  have qcard : Fintype.card ↥(H:Set V) = H.card := Fintype.card_coe H
  have inner (v : ↥(H:Set V)) :
      G.degree v.val ≤ (Pins p v.val).card+Q.degree v :=
    Graffiti189LongestPath.WideWing.inside_deg hp C v
  have hi_pins (v : V) (vh : v∈H) (high : k+2≤G.degree v) :
      (Pins p v).card=2 := by
    let z : ↥(H:Set V) := ⟨v,vh⟩
    have e := inner z
    have q := Q.degree_lt_card_verts z
    have f := few v vh
    change G.degree v≤(Pins p v).card+Q.degree z at e
    omega
  have universal (v : V) (vh : v∈H) (high : k+2≤G.degree v) :
      ∀ w∈H,v≠w → G.Adj v w := by
    intro w wh vw
    let z : ↥(H:Set V) := ⟨v,vh⟩
    let u : ↥(H:Set V) := ⟨w,wh⟩
    have e := inner z
    have f := few v vh
    have dz : 4≤Q.degree z := by
      change G.degree v≤(Pins p v).card+Q.degree z at e
      omega
    have sub : Q.neighborFinset z⊆(univ:Finset ↥(H:Set V)).erase z := by
      intro r hr
      exact mem_erase.mpr ⟨((Q.mem_neighborFinset _ _).mp hr).ne.symm,mem_univ _⟩
    have cd : ((univ:Finset ↥(H:Set V)).erase z).card≤(Q.neighborFinset z).card := by
      rw [card_erase_of_mem (mem_univ z),card_univ,qcard,hsize,Q.card_neighborFinset_eq_degree]
      omega
    have e := eq_of_subset_of_card_le sub cd
    apply (Q.mem_neighborFinset z u).mp
    rw [e]
    exact mem_erase.mpr ⟨fun ne => vw (congrArg Subtype.val ne.symm),mem_univ _⟩
  have clique : ∀ u∈H,∀ v∈H,u≠v → G.Adj u v := by
    intro u uh v vh uv
    exact (deg u v uv).elim (fun d => universal u uh d v vh uv)
      (fun d => (universal v vh d u uh uv.symm).symm)
  let I := (range p.length).filter (fun j => ∃ z∈H, (4≤k ∨ k+2≤G.degree z) ∧ j∈Pins p z)
  have Idata {j : ℕ} (hj : j ∈ I) : ∃ z∈H, (4≤k ∨ k+2≤G.degree z) ∧ j∈Pins p z :=
    (mem_filter.mp hj).2
  have atLeast : k≤I.card := by
    have ck := componentPins_card hp C k conn
    have sub : componentPins C ⊆ I.image p.getVert := by
      intro u hu
      obtain ⟨hu,z,hz,ez⟩ := mem_filter.mp hu
      obtain ⟨j,hj,he⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp
        (hO z hz) (List.mem_toFinset.mp hu) ez
      exact mem_image.mpr ⟨j,mem_filter.mpr ⟨(mem_filter.mp hj).1,z,hz,Or.inl (by omega),hj⟩,he⟩
    exact ck.trans ((card_le_card sub).trans card_image_le)
  have sep {i j : Nat} (hi : i∈I) (hj : j∈I) (e : i<j) : i+2≤j := by
    obtain ⟨u,hu,du,hi⟩ := Idata hi
    obtain ⟨v,hv,dv,hj⟩ := Idata hj
    by_cases eq : u=v
    · subst v
      apply Classical.byContradiction
      intro nLe
      have eLt : j < i+2 := Nat.lt_of_not_ge nLe
      have ij : i+1=j := by omega
      have fl : p.getVert j ∈ FlankVertices p u := mem_image.mpr
        ⟨j,mem_union.mpr (Or.inr (mem_image.mpr ⟨i,hi,ij⟩)),rfl⟩
      have pB := Graffiti189LongestPath.OneSlack.pin_vertices_subset_boundary (hO u hu)
        (mem_image.mpr ⟨j,hj,rfl⟩)
      exact (mem_sdiff.mp (flanks_outside_boundary hc hp (hO u hu) fl)).2 pB
    · obtain ⟨q,hq,hS⟩ := C.joined u hu v hv
      have pos : 0 < q.length := by
        cases q with
        | nil => exact (eq rfl).elim
        | cons e q => simp
      have hd := gap_three_of_linked_pins hp hi hj e q hq pos (fun z hz => hO z (hS z hz))
      omega
  have allI {v : V} (hv : v∈H) {m : Nat} (hm : m∈Pins p v) : m∈I :=
    mem_filter.mpr ⟨(mem_filter.mp hm).1,v,hv,Or.inl (by omega),hm⟩
  have coreGap {u v : V} (hu : u∈H) (hv : v∈H) (ne : u≠v)
      {m n : Nat} (hm : m∈Pins p u) (hn : n∈Pins p v) (hh : m<n) : m+6≤n := by
    have z := wide_gap_of_small_wing hp C (k+2) low deg few (by
        change H.card+7≤2*(k+2); omega) hu hv ne hm hn hh
    change m+H.card+1≤n at z
    omega
  have cheap {m n : Nat} (hm : m∈I) (hn : n∈I) (mn : m<n) (short : n<m+6) :
      ∃ u∈H, m∈Pins p u ∧ n∈Pins p u ∧ ∀ v∈H, (m∈Pins p v ∨ n∈Pins p v) → v=u := by
    obtain ⟨u,hu,_,hmu⟩ := Idata hm
    obtain ⟨v,hv,_,hnv⟩ := Idata hn
    have e : u=v := Classical.byContradiction (fun h => (Nat.not_le_of_lt short) (coreGap hu hv h hmu hnv mn))
    subst v
    exact ⟨u,hu,hmu,hnv,fun v hv h => Classical.byContradiction (fun ne => (Nat.not_le_of_lt short)
      (h.elim (fun h => coreGap hv hu ne h hnv mn) (fun h => coreGap hu hv (Ne.symm ne) hmu h mn)))⟩
  have dist {m n : Nat} (hm : m∈I) (hn : n∈I) (mn : m<n) : m+3≤n := by
    have h2 := sep hm hn mn
    apply Nat.le_of_not_gt
    intro ns
    obtain ⟨v,hv,hmv,hnv,_⟩ := cheap hm hn mn (by omega)
    have eq : Pins p v = {m,m+2} := by
      have sub : ({m,m+2}:Finset Nat) ⊆ Pins p v := by
        intro r h
        simp only [mem_insert,mem_singleton] at h
        rcases h with rfl|rfl
        · exact hmv
        · rwa [show m+2=n by omega]
      have ff := few v hv
      exact (eq_of_subset_of_card_le sub (by simpa using ff)).symm
    have vd := low v hv
    have vo := hO v hv
    have ne : v ≠ p.getVert (m+1) := fun e => vo (e.symm ▸ p.getVert_mem_support _)
    have dd := deg v (p.getVert (m+1)) ne
    have se := sum_degree_gap_exchange hc (k+2) cap hMin.1 vo m eq
    by_cases dh : k+2≤G.degree v
    · have bb := (normalized_high_omission hc (k+2) k (by omega) le_rfl cap conn hMin vo dh m hmv).2
      exact bb (by rwa [show m+2=n by omega])
    · have ss := se.2 (by omega)
      omega
  have bounds {m : Nat} (hm : m∈I) : 1≤m ∧ m+1≤p.length := by
    obtain ⟨v,hv,_,hh⟩ := Idata hm
    have h := (Graffiti189LongestPath.pin_data hh).1
    have hh₁ := Graffiti189LongestPath.Rigidity.pin_pos hp (hO v hv) hh
    omega
  have sorted : ∃ a' b' c' d' : Nat,
      a'∈I ∧ b'∈I ∧ c'∈I ∧ d'∈I ∧ a'<b' ∧ b'<c' ∧ c'<d' := by
    have cn : 4≤I.card := by omega
    let a' := I.min' (by apply card_pos.mp; omega)
    have aI : a'∈I := min'_mem _ _
    let I₁ := I.erase a'
    have c₁ : I₁.card+1=I.card := card_erase_add_one aI
    let b' := I₁.min' (by apply card_pos.mp; omega)
    have bI : b'∈I₁ := min'_mem _ _
    let I₂ := I₁.erase b'
    have c₂ : I₂.card+1=I₁.card := card_erase_add_one bI
    let c' := I₂.min' (by apply card_pos.mp; omega)
    have dI : c'∈I₂ := min'_mem _ _
    let I₃ := I₂.erase c'
    have c₃ : I₃.card+1=I₂.card := card_erase_add_one dI
    let d' := I₃.min' (by apply card_pos.mp; omega)
    have eI : d'∈I₃ := min'_mem _ _
    have h₁ := min'_le I b' (mem_erase.mp bI).2
    have h₂ := min'_le I₁ c' (mem_erase.mp dI).2
    have h₃ := min'_le I₂ d' (mem_erase.mp eI).2
    have ne₁ := (mem_erase.mp bI).1
    have ne₂ := (mem_erase.mp dI).1
    have ne₃ := (mem_erase.mp eI).1
    exact ⟨a',b',c',d',aI,(mem_erase.mp bI).2,
      (mem_erase.mp (mem_erase.mp dI).2).2,(mem_erase.mp (mem_erase.mp (mem_erase.mp eI).2).2).2,
      by omega,by omega,by omega⟩
  obtain ⟨r,s,t,u,hr,hs,ht,hu,rs,st,tu⟩ := sorted
  have no_double {a' b' c' : Nat} (ha : a'∈I) (hb : b'∈I) (hc' : c'∈I)
      (ab : a'<b') (bc : b'<c') (s1 : b'<a'+6) (s2 : c'<b'+6) : False := by
    obtain ⟨x₁,hx₁,ha',hb',unique₁⟩ := cheap ha hb ab s1
    obtain ⟨x₂,hx₂,hb'',hc'',_⟩ := cheap hb hc' bc s2
    have eq := unique₁ x₂ hx₂ (Or.inr hb'')
    subst x₂
    have sub : ({a',b',c'}:Finset Nat) ⊆ Pins p x₁ := by
      intro m hm
      simp only [mem_insert,mem_singleton] at hm
      rcases hm with rfl|rfl|rfl
      · exact ha'
      · exact hb'
      · exact hc''
    have cnt := card_le_card sub
    have e : ({a',b',c'}:Finset Nat).card=3 := by
      simp [show a'≠b' by omega,show a'≠c' by omega,show b'≠c' by omega]
    have f := few x₁ hx₁
    omega
  have dr := dist hr hs rs
  have ds := dist hs ht st
  have dt := dist ht hu tu
  have br := (bounds hr).1
  have bu := (bounds hu).2
  have totalI : I.card≤4 := by
    have q := Graffiti189LongestPath.WideWing.two_per_block I 9 2 (by decide)
      (by intro i ii; have q := (bounds ii).2; omega)
      (by intro i ii j jj l ll ij jl
          have t := dist ii jj ij
          have s := dist jj ll jl
          by_contra! e
          exact no_double ii jj ll ij jl (by omega) (by omega))
    omega
  have all : I={r,s,t,u} := by
    apply (eq_of_subset_of_card_le _ _).symm
    · intro m hm
      simp only [mem_insert,mem_singleton] at hm
      rcases hm with rfl|rfl|rfl|rfl <;> assumption
    · rw [show ({r,s,t,u}:Finset Nat).card=4 by
        simp [show r≠s by omega,show r≠t by omega,show r≠u by omega,
          show s≠t by omega,show s≠u by omega,show t≠u by omega]]
      exact totalI
  have exists_high_excluding (v w : V) :
      ∃ z∈H,z≠v ∧ z≠w ∧ k+2≤G.degree z := by
    have some (F : Finset V) (fc : F.card≤3) : ∃ z∈H,z∉F := by
      by_contra! na
      have cl := card_le_card (show H⊆F from na)
      omega
    obtain ⟨z,zh,r⟩ := some {v,w} (by
      have q := card_insert_le v ({w}:Finset V)
      rw [card_singleton] at q
      omega)
    obtain ⟨z',zh',r'⟩ := some {v,w,z} (by
      have q := card_insert_le v ({w,z}:Finset V)
      have l := card_insert_le w ({z}:Finset V)
      rw [card_singleton] at l
      omega)
    simp only [mem_insert,mem_singleton,not_or] at r r'
    exact (deg z z' (fun e => r'.2.2 e.symm)).elim
      (fun dz => ⟨z,zh,r.1,r.2,dz⟩) (fun dz => ⟨z',zh',r'.1,r'.2.1,dz⟩)
  have pair {v : V} (vh : v∈H) {a b : ℕ} (aa : a∈Pins p v) (bb : b∈Pins p v)
      (lt : a<b) : Pins p v = {a,b} := by
    refine (eq_of_subset_of_card_le ?_ ?_).symm
    · intro m mm
      simp only [mem_insert,mem_singleton] at mm
      exact mm.elim (fun e => e.symm ▸ aa) (fun e => e.symm ▸ bb)
    · rw [show ({a,b}:Finset ℕ).card=2 by simp [ne_of_lt lt]]
      exact few v vh
  have fill {v : V} (vh : v∈H) (high : k+2≤G.degree v) {a b : ℕ}
      (lt : a<b) (sub : ∀ m∈Pins p v,m=a ∨ m=b) : Pins p v={a,b} := by
    apply eq_of_subset_of_card_le
    · intro m hm
      simpa only [mem_insert,mem_singleton] using sub m hm
    · rw [hi_pins v vh high]
      simp [ne_of_lt lt]
  have occurs {v : V} (vh : v∈H) {m : ℕ} (mm : m∈Pins p v) :
      m=r ∨ m=s ∨ m=t ∨ m=u := by
    have z := allI vh mm
    rw [all] at z
    simpa only [mem_insert,mem_singleton] using z
  have not_both (rs' : s<r+6) (tu' : u<t+6) : False := by
    obtain ⟨x,xh,_,_,xo⟩ := cheap hr hs rs rs'
    obtain ⟨y,yh,_,_,yo⟩ := cheap ht hu tu tu'
    obtain ⟨v,vh,vx,vy,vd⟩ := exists_high_excluding x y
    have c := hi_pins v vh vd
    obtain ⟨m,mm⟩ := card_pos.mp (show 0<(Pins p v).card by omega)
    rcases occurs vh mm with e|e|e|e
    · exact vx (xo v vh (Or.inl (e ▸ mm)))
    · exact vx (xo v vh (Or.inr (e ▸ mm)))
    · exact vy (yo v vh (Or.inl (e ▸ mm)))
    · exact vy (yo v vh (Or.inr (e ▸ mm)))
  by_cases short1 : s<r+6
  · have q1 : t≥s+6 := Nat.le_of_not_gt (fun e => no_double hr hs ht rs st short1 e)
    have q2 : u≥t+6 := Nat.le_of_not_gt (not_both short1)
    have r1 : r=1 := by omega
    have s1 : s=4 := by omega
    have t1 : t=10 := by omega
    have u1 : u=16 := by omega
    obtain ⟨x,xh,xr,xs,xo⟩ := cheap hr hs rs short1
    obtain ⟨y,yh,yx,_,dy⟩ := exists_high_excluding x x
    have yy := fill yh dy tu (by
      intro m mm
      rcases occurs yh mm with er|es|et|eu
      · exact (yx (xo y yh (Or.inl (er ▸ mm)))).elim
      · exact (yx (xo y yh (Or.inr (es ▸ mm)))).elim
      · exact Or.inl et
      · exact Or.inr eu)
    refine ⟨x,y,r,s,t,u,⟨Or.inl ⟨r1,s1,t1,u1⟩,plen,h,xh,yh,yx.symm,hO,full,clique,pair xh xr xs rs,yy,xo⟩,?_⟩
    intro v vh m mm
    exact all ▸ allI vh mm
  by_cases short2 : t<s+6
  · have q1 : s≥r+6 := Nat.le_of_not_gt short1
    have q2 : u≥t+6 := Nat.le_of_not_gt (fun e => no_double hs ht hu st tu short2 e)
    have r1 : r=1 := by omega
    have s1 : s=7 := by omega
    have t1 : t=10 := by omega
    have u1 : u=16 := by omega
    obtain ⟨x,xh,xs,xt,xo⟩ := cheap hs ht st short2
    obtain ⟨y,yh,yx,_,dy⟩ := exists_high_excluding x x
    have yy := fill yh dy (show r<u by omega) (by
      intro m mm
      rcases occurs yh mm with er|es|et|eu
      · exact Or.inl er
      · exact (yx (xo y yh (Or.inl (es ▸ mm)))).elim
      · exact (yx (xo y yh (Or.inr (et ▸ mm)))).elim
      · exact Or.inr eu)
    refine ⟨x,y,s,t,r,u,⟨Or.inr (Or.inl ⟨s1,t1,r1,u1⟩),plen,h,xh,yh,yx.symm,hO,full,clique,pair xh xs xt st,yy,xo⟩,?_⟩
    intro v vh m mm
    have q := occurs vh mm
    simp only [mem_insert,mem_singleton]
    tauto
  have short3 : u<t+6 := by omega
  have r1 : r=1 := by omega
  have s1 : s=7 := by omega
  have t1 : t=13 := by omega
  have u1 : u=16 := by omega
  obtain ⟨x,xh,xt,xu,xo⟩ := cheap ht hu tu short3
  obtain ⟨y,yh,yx,_,dy⟩ := exists_high_excluding x x
  have yy := fill yh dy rs (by
    intro m mm
    rcases occurs yh mm with er|es|et|eu
    · exact Or.inl er
    · exact Or.inr es
    · exact (yx (xo y yh (Or.inl (et ▸ mm)))).elim
    · exact (yx (xo y yh (Or.inr (eu ▸ mm)))).elim)
  refine ⟨x,y,t,u,r,s,⟨Or.inr (Or.inr ⟨t1,u1,r1,s1⟩),plen,h,xh,yh,yx.symm,hO,full,clique,pair xh xt xu tu,yy,xo⟩,?_⟩
  intro v vh m mm
  have q := occurs vh mm
  simp only [mem_insert,mem_singleton]
  tauto

#print axioms exists_layout
end Graffiti189LongestPath.FivePinLayout
