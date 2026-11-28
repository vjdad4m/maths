import MarkedOrder189
import TerminalOreAdapter199
open Finset SimpleGraph SimpleGraph.Walk Graffiti189LongestPath Graffiti189LongestPath.Rigidity
open private Graffiti189LongestPath.pin_data from SmallSeparator189
open private Graffiti189LongestPath.Rigidity.lengths_take_drop from Rigidity189
set_option warningAsError true
set_option linter.unusedSectionVars false
namespace Graffiti189LongestPath.WideWing
variable {V : Type*} {G : SimpleGraph V}

private lemma drop_support {a b : V} (p : G.Walk a b) (j : Nat) :
    (p.drop j).support ⊆ p.support := by
  induction p generalizing j with
  | nil => simp [Walk.drop]
  | cons e p ih =>
    cases j with
    | zero => simp [Walk.drop]
    | succ j => exact fun w hw => List.mem_cons_of_mem _ (ih j hw)

private lemma drop_path {a b : V} (p : G.Walk a b) (hp : p.IsPath) (j : Nat) :
    (p.drop j).IsPath := by
  induction p generalizing j with
  | nil => simp [Walk.drop]
  | cons e p ih =>
    cases j with
    | zero => exact hp
    | succ j => exact ih hp.of_cons j

private lemma splice_interval {a b x y : V} (p : G.Walk a b) (hp : p.IsPath)
    (q : G.Walk x y) (hq : q.IsPath)
    (dis : ∀ w ∈ q.support, w ∉ p.support)
    (i j : Nat) (gap : i < j) (hj : j ≤ p.length)
    (al : G.Adj (p.getVert i) x) (ar : G.Adj y (p.getVert j)) :
    ∃ r : G.Walk a b, r.IsPath ∧
      r.length+j = p.length+q.length+i+2 ∧ ∀ w∈r.support, w∈p.support ∨ w∈q.support := by
  induction p generalizing i j with
  | nil => simp at hj; omega
  | @cons a v b e p ih =>
    cases i with
    | zero =>
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hl : j ≤ p.length := by simp at hj; omega
      have ht := (Graffiti189LongestPath.Rigidity.lengths_take_drop p j hl).2
      have e₁ : G.Adj a x := al
      have e₂ : G.Adj y (p.getVert j) := ar
      let s := p.drop j
      let r₀ := q.append (.cons e₂ s)
      have pr : r₀.IsPath := by
        rw [isPath_def,support_append,List.nodup_append]
        refine ⟨hq.support_nodup, ?_, ?_⟩
        · simpa [support_cons] using (drop_path p hp.of_cons j).support_nodup
        · intro t ht hst
          have hs : t ∈ s.support := by simpa [support_cons] using hst
          exact dis t ht (List.mem_cons_of_mem _ (drop_support p j hs))
      have na : a ∉ r₀.support := by
        rw [mem_support_append_iff]
        rintro (ha|ha)
        · exact dis a ha (by simp)
        · simp only [support_cons,List.mem_cons] at ha
          exact ha.elim (fun e => dis a (e.symm ▸ q.end_mem_support) (by simp))
            (fun h => (cons_isPath_iff _ _).mp hp |>.2 (drop_support p j h))
      refine ⟨.cons e₁ r₀,pr.cons na,?_,?_⟩
      · simp only [length_cons, r₀,length_append,s,ht]
        omega
      · intro w hw
        simp only [support_cons,List.mem_cons,r₀,mem_support_append_iff] at hw
        rcases hw with hau | hq | hyy | hp
        · exact Or.inl (by simp [hau])
        · exact Or.inr hq
        · exact Or.inr (hyy.symm ▸ q.end_mem_support)
        · exact Or.inl (List.mem_cons_of_mem _ (drop_support p j hp))
    | succ i =>
      obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hjl : j≤p.length := by simp at hj; omega
      obtain ⟨r,hr,hL,hS⟩ := ih hp.of_cons
        (fun w hw hps => dis w hw (List.mem_cons_of_mem _ hps)) i j (by omega) hjl al ar
      refine ⟨.cons e r,hr.cons ?_,by simp only [Walk.length_cons]; omega,?_⟩
      · intro ha
        exact (hS a ha).elim ((cons_isPath_iff _ _).mp hp).2
          (fun h => dis a h (by simp))
      · intro w hw
        simp only [support_cons,List.mem_cons] at hw
        exact hw.elim (fun e => Or.inl (by simp [e]))
          (fun h => (hS w h).elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr)

theorem terminal_length_le_gap [Fintype V] [DecidableRel G.Adj]
    {a b x y : V} {p : G.Walk a b} (hp : IsLongest p)
    {i j : Nat} (hi : i∈Pins p x) (hj : j∈Pins p y) (lt : i<j)
    (q : G.Walk x y) (hq : q.IsPath) (off : ∀ w∈q.support,w∉p.support) :
    q.length+2+i ≤ j := by
  obtain ⟨r,hr,he,_⟩ := splice_interval p hp.1 q hq off i j lt
    (Nat.le_of_lt (Graffiti189LongestPath.pin_data hj).1)
    (Graffiti189LongestPath.pin_data hi).2.symm (Graffiti189LongestPath.pin_data hj).2
  have hh := hp.2 a b r hr
  omega

#print axioms terminal_length_le_gap

open Graffiti189LongestPath.OneSlack
open private Graffiti189LongestPath.OneSlack.card_pinVertices
  Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem from OneSlack189
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The graph is complete on a specified set. -/
private def CompleteOn (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ u∈A,∀ v∈A,u≠v → G.Adj u v

private theorem clique_chain (A : Finset V) (clique : CompleteOn G A)
    (L : List V) (nd : L.Nodup) (mem : ∀ z∈L,z∈A) : List.Chain' G.Adj L := by
  have h : L.Pairwise G.Adj := by
    induction L with
    | nil => exact .nil
    | cons a t ih =>
      rw [List.pairwise_cons]
      have nt := List.nodup_cons.mp nd
      refine ⟨?_,ih nt.2 (fun z zt=>mem _ (List.mem_cons_of_mem _ zt))⟩
      intro z zt
      exact clique a (mem _ (by simp)) z (mem _ (by simp [zt]))
        (fun h=>nt.1 (h.symm ▸ zt))
  exact h.chain'

private theorem walk_of_chain (a : V) (L : List V)
    (cl : List.Chain' G.Adj (a::L)) : ∃ b,∃ q : G.Walk a b,q.support=a::L := by
  induction L generalizing a with
  | nil => exact ⟨a,.nil,rfl⟩
  | cons b L ih =>
    obtain ⟨c,q,eq⟩ := ih b cl.tail
    exact ⟨c,.cons cl.rel_head q,by simp [eq]⟩

theorem rooted_path_in_clique (A : Finset V) (clique : CompleteOn G A)
    {x : V} (xa : x∈A) :
    ∃ y,∃ q : G.Walk x y,q.IsPath ∧ ∀ v,v∈q.support ↔ v∈A := by
  classical
  let L := (A.erase x).toList
  have nd : (x::L).Nodup := by simp [L,(A.erase x).nodup_toList]
  have lm (v : V) : v∈x::L ↔ v∈A := by
    by_cases e : v=x <;> simp [L,e,xa]
  obtain ⟨y,q,ql⟩ := walk_of_chain x L
    (clique_chain A clique (x::L) nd (fun v hv=>(lm v).mp hv))
  exact ⟨y,q,(by rw [isPath_def,ql];exact nd),fun v=>by rw [ql,lm]⟩

theorem path_between_in_clique (A : Finset V) (clique : CompleteOn G A)
    {x y : V} (xa : x∈A) (ya : y∈A) (xy : x≠y) :
    ∃ q : G.Walk x y,q.IsPath ∧ ∀ v,v∈q.support ↔ v∈A := by
  classical
  let M := ((A.erase x).erase y).toList
  let L := M++[y]
  have ndM : M.Nodup := Finset.nodup_toList _
  have yM : y∉M := by simp [M]
  have xM : x∉M := by simp [M]
  have nd : (x::L).Nodup := by
    rw [List.nodup_cons]
    refine ⟨by simp [L,xM,xy],?_⟩
    rw [List.nodup_append]
    refine ⟨ndM,by simp,?_⟩
    intro u um uy
    have uy' : u=y := by simpa using uy
    exact yM (uy' ▸ um)
  have lm (v : V) : v∈x::L ↔ v∈A := by
    by_cases hx : v=x
    · simp [hx,xa]
    by_cases hy : v=y
    · simp [L,hy,ya]
    · simp [L,M,hx,hy]
  obtain ⟨z,q,ql⟩ := walk_of_chain x L
    (clique_chain A clique (x::L) nd (fun v hv=>(lm v).mp hv))
  have zy : z=y := by
    have last : q.support.getLast? = some z := by
      rw [List.getLast?_eq_getLast (by simp),q.getLast_support]
    rw [ql,show x::L=(x::M)++[y] by rfl,List.getLast?_concat] at last
    simpa using last.symm
  subst z
  exact ⟨q,(by rw [isPath_def,ql];exact nd),fun v=>by rw [ql,lm]⟩

private theorem terminalOre
    (deg : ∀ u v : V,u≠v → ¬ G.Adj u v → Fintype.card V+1≤G.degree u+G.degree v)
    {x y : V} (xy : x≠y) : ∃ q : G.Walk x y,q.IsPath ∧ ∀ v,v∈q.support := by
  classical
  let Z : SimpleGraph V := ⊤
  have cl : CompleteOn Z univ := by
    intro u hu v hv ne
    exact ne
  obtain ⟨p,hp,all⟩ := path_between_in_clique univ cl (mem_univ x) (mem_univ y) xy
  apply CrossSaturation.terminal_ore_closure (H:=Z) (le_top : G≤Z)
    (fun u v e h => deg u v (Adj.ne e) h) p hp
  exact fun w => (all w).mpr (mem_univ w)

private lemma inside_deg {a b : V} {p : G.Walk a b} (hp : IsLongest p)
    (H : OmittedComponent p) (x : ↥(H.vertices : Set V)) :
    G.degree x.val ≤ (Pins p x.val).card + (G.induce (H.vertices : Set V)).degree x := by
  classical
  let N := G.neighborFinset x.val ∩ H.vertices
  have sub : G.neighborFinset x.val ⊆ PinVertices p x.val ∪ N := by
    intro y hy
    have ed := (G.mem_neighborFinset x.val y).mp hy
    by_cases h : y∈H.vertices
    · exact mem_union.mpr (Or.inr (mem_inter.mpr ⟨hy,h⟩))
    · obtain ⟨i,hi,ei⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp
        (H.off _ x.property) (H.closed _ x.property _ h ed) ed
      exact mem_union.mpr (Or.inl (mem_image.mpr ⟨i,hi,ei⟩))
  have cnt := card_le_card sub
  have cnt' := card_union_le (PinVertices p x.val) N
  rw [G.card_neighborFinset_eq_degree] at cnt
  rw [Graffiti189LongestPath.OneSlack.card_pinVertices hp] at cnt'
  have eq : N.card = (G.induce (H.vertices : Set V)).degree x := by
    let J := G.induce (H.vertices : Set V)
    rw [← J.card_neighborFinset_eq_degree]
    refine card_bij' (fun y hy => (⟨y,(mem_inter.mp hy).2⟩ : ↥(H.vertices : Set V)))
      (fun y _ => y.val) ?_ ?_ ?_ ?_
    · intro y hy
      exact (J.mem_neighborFinset x _).mpr ((G.mem_neighborFinset x.val y).mp (mem_inter.mp hy).1)
    · intro y hy
      exact mem_inter.mpr ⟨(G.mem_neighborFinset x.val y.val).mpr ((J.mem_neighborFinset x y).mp hy),y.property⟩
    · intro y hy; rfl
    · intro y hy; exact Subtype.ext rfl
  omega

/-- A sufficiently small omitted component is Hamilton-connected under the
degree assumptions and the at-most-two-pin restriction. -/
theorem terminal_wing {a b : V} {p : G.Walk a b} (hp : IsLongest p) (H : OmittedComponent p)
    (d : Nat) (low : ∀ x ∈ H.vertices, d-2≤G.degree x)
    (high : ∀ x y : V, x≠y → d≤G.degree x ∨ d≤G.degree y)
    (few : ∀ x∈H.vertices, (Pins p x).card≤2)
    (small : H.vertices.card+7≤2*d)
    {x y : V} (hx : x∈H.vertices) (hy : y∈H.vertices) (ne : x≠y) :
    ∃ q : G.Walk x y, q.IsPath ∧ (∀ w∈q.support, w∈H.vertices) ∧ q.length+1=H.vertices.card := by
  classical
  let U := ↥(H.vertices : Set V)
  let J := G.induce (H.vertices : Set V)
  let u : U := ⟨x,hx⟩
  let v : U := ⟨y,hy⟩
  have nuv : u ≠ v := fun e => ne (congrArg Subtype.val e)
  have cc : Fintype.card U = H.vertices.card := Fintype.card_coe _
  have hdeg (s t : U) (ne : s ≠ t) (_ : ¬J.Adj s t) :
      Fintype.card U+1 ≤ J.degree s+J.degree t := by
    have es := inside_deg hp H s
    have et := inside_deg hp H t
    have eS := few _ s.property
    have eT := few _ t.property
    have lows := low _ s.property
    have lowt := low _ t.property
    have nes : s.val ≠ t.val := fun e => ne (Subtype.ext e)
    change G.degree s.val ≤ (Pins p s.val).card+J.degree s at es
    change G.degree t.val ≤ (Pins p t.val).card+J.degree t at et
    rcases high s.val t.val nes with h|h <;> omega
  obtain ⟨q,hq,all⟩ := terminalOre (G:=J) hdeg nuv
  let f : J →g G := ⟨Subtype.val,fun e => e⟩
  have ef : Function.Injective f := Subtype.val_injective
  refine ⟨q.map f,map_isPath_of_injective ef hq,?_,?_⟩
  · intro w hw
    rw [support_map] at hw
    obtain ⟨s,_,rfl⟩ := List.mem_map.mp hw
    exact s.property
  · have es : q.support.toFinset = (univ : Finset U) := ext fun w =>
      ⟨fun _ => mem_univ _,fun _ => List.mem_toFinset.mpr (all w)⟩
    have hc := congrArg card es
    rw [List.toFinset_card_of_nodup hq.support_nodup,length_support,card_univ,cc] at hc
    simpa only [length_map] using hc

/-- If two pin positions of a small omitted component have distinct porters,
the gap between them contains at least as many vertices as the whole component. -/
theorem wide_gap_of_small_wing {a b : V} {p : G.Walk a b} (hp : IsLongest p) (H : OmittedComponent p)
    (d : Nat) (low : ∀ x ∈ H.vertices, d-2≤G.degree x)
    (high : ∀ x y : V, x≠y → d≤G.degree x ∨ d≤G.degree y)
    (few : ∀ x∈H.vertices, (Pins p x).card≤2)
    (small : H.vertices.card+7≤2*d)
    {x y : V} (hx : x∈H.vertices) (hy : y∈H.vertices) (ne : x≠y)
    {i j : Nat} (hi : i∈Pins p x) (hj : j∈Pins p y) (lt : i<j) :
    i+H.vertices.card+1 ≤ j := by
  obtain ⟨q,hq,off,len⟩ := terminal_wing hp H d low high few small hx hy ne
  have g := terminal_length_le_gap hp hi hj lt q hq (fun w hw => H.off w (off w hw))
  omega

#print axioms terminal_wing
#print axioms wide_gap_of_small_wing

private lemma two_per_block (I : Finset Nat) (K m : Nat) (pos : 0<K)
    (lt : ∀ i∈I, i<m*K)
    (wide : ∀ i∈I,∀ j∈I,∀ k∈I,i<j → j<k → i+K≤k) :
    I.card ≤ 2*m := by
  classical
  let f (i : Nat) := i/K
  have into (i : Nat) (hi : i ∈ I) : f i ∈ range m := by
    apply mem_range.mpr
    exact (Nat.div_lt_iff_lt_mul pos).mpr (lt i hi)
  have fib (q : Nat) : (I.filter fun i => f i=q).card ≤ 2 := by
    by_contra! h
    obtain ⟨a,ha,b,hb,c,hc,ab,ac,bc⟩ := Finset.two_lt_card.mp h
    have trouble {x y z : Nat}
        (hx : x∈I.filter (fun i=>f i=q))
        (hy : y∈I.filter (fun i=>f i=q))
        (hz : z∈I.filter (fun i=>f i=q))
        (hxy : x<y) (hyz : y<z) : False := by
      have dx := (mem_filter.mp hx).2
      have dz := (mem_filter.mp hz).2
      change x/K=q at dx
      change z/K=q at dz
      have mx := Nat.mod_add_div x K
      have mz := Nat.mod_add_div z K
      rw [dx] at mx
      rw [dz] at mz
      have lz := Nat.mod_lt z pos
      have hh := wide x (mem_filter.mp hx).1 y (mem_filter.mp hy).1 z
        (mem_filter.mp hz).1 hxy hyz
      omega
    rcases lt_or_gt_of_ne ab with hab | hba <;>
      rcases lt_or_gt_of_ne ac with hac | hca <;>
      rcases lt_or_gt_of_ne bc with hbc | hcb
    · exact trouble ha hb hc hab hbc
    · exact trouble ha hc hb hac hcb
    · omega
    · exact trouble hc ha hb hca hab
    · exact trouble hb ha hc hba hac
    · omega
    · exact trouble hb hc ha hbc hca
    · exact trouble hc hb ha hcb hba
  have cnt := card_eq_sum_card_fiberwise (f:=f) (s:=I) (t:=range m) (fun _ => into _)
  rw [cnt]
  calc
    _ ≤ ∑ _v ∈ range m, (2 : Nat) := sum_le_sum (fun q _ => fib q)
    _ = _ := by simp [Nat.mul_comm]

/-- When the omitted wing satisfies terminal Ore, each interval of h+4
consecutive indices contains at most two wing pins. -/
theorem pin_blocks {a b : V} {p : G.Walk a b} (hp : IsLongest p) (H : OmittedComponent p)
    (d : Nat) (low : ∀ x ∈ H.vertices, d-2≤G.degree x)
    (high : ∀ x y : V, x≠y → d≤G.degree x ∨ d≤G.degree y)
    (few : ∀ x∈H.vertices, (Pins p x).card≤2)
    (small : H.vertices.card+7≤2*d)
    (spaced : ∀ x ∈ H.vertices, ∀ y ∈ H.vertices, ∀ i∈Pins p x, ∀ j∈Pins p y, i<j → i+3≤j)
    (m : Nat) (short : p.length≤m*(H.vertices.card+4)) :
    (componentPins H).card ≤ 2*m := by
  classical
  let I := (range p.length).filter (fun j => ∃ z∈H.vertices, j∈Pins p z)
  have data {i : Nat} (hi : i∈I) : ∃ z∈H.vertices,i∈Pins p z := (mem_filter.mp hi).2
  have triple (i : Nat) (hi : i∈I) (j : Nat) (hj : j∈I) (k : Nat) (hk : k∈I)
      (ij : i<j) (jk : j<k) : i+(H.vertices.card+4)≤k := by
    obtain ⟨x,hx,ix⟩ := data hi
    obtain ⟨y,hy,jy⟩ := data hj
    obtain ⟨z,hz,kz⟩ := data hk
    by_cases e : x=y
    · subst y
      have yz : x≠z := by
        intro eq
        subst z
        have ct := Finset.two_lt_card.mpr ⟨i,ix,j,jy,k,kz,by omega,by omega,by omega⟩
        have sm := few x hx
        omega
      have w := wide_gap_of_small_wing hp H d low high few small hx hz yz jy kz jk
      have v := spaced x hx x hx i ix j jy ij
      omega
    · have w := wide_gap_of_small_wing hp H d low high few small hx hy e ix jy ij
      have v := spaced y hy z hz j jy k kz jk
      omega
  have q := two_per_block I (H.vertices.card+4) m (by omega)
    (fun i hi => (mem_range.mp (mem_filter.mp hi).1).trans_le short) triple
  have sub : componentPins H ⊆ I.image p.getVert := by
    intro v hv
    obtain ⟨vp,x,hx,ed⟩ := mem_filter.mp hv
    obtain ⟨i,hi,he⟩ := Graffiti189LongestPath.OneSlack.pin_of_neighbor_mem hp
      (H.off x hx) (List.mem_toFinset.mp vp) ed
    exact mem_image.mpr ⟨i,mem_filter.mpr ⟨(mem_filter.mp hi).1,x,hx,hi⟩,he⟩
  exact (card_le_card sub).trans (card_image_le.trans q)

#print axioms pin_blocks
end Graffiti189LongestPath.WideWing
