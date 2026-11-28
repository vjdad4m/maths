import TerminalOreClosure189

namespace Graffiti189LongestPath.CrossSaturation.ThresholdSix
open SimpleGraph SimpleGraph.Walk Finset Graffiti189Ore
open private liftCap_support leaf_cap_degree_ge from OreClosure189
open private cap_path_forces_end from TwoTerminalOre189
variable {V : Type*} [Fintype V] [DecidableEq V] {G H : SimpleGraph V}
  [DecidableRel G.Adj] [DecidableRel H.Adj]
set_option linter.unusedSectionVars false

private theorem leaf_degree_increased (x : V) :
    G.degree x + 1 ≤ (Graffiti189Ore.cap G (fun v=>v=x)).degree (some x) := by
  classical
  let K := Graffiti189Ore.cap G (fun v=>v=x)
  let f : V ↪ Option V := ⟨some,Option.some_injective V⟩
  have h : K.neighborFinset (some x)=insert none ((G.neighborFinset x).map f) := by
    ext y
    cases y <;> simp [K,Graffiti189Ore.cap,mem_neighborFinset,f]
  have np : (none : Option V)∉(G.neighborFinset x).map f := by simp [f]
  change G.degree x + 1 ≤ K.degree (some x)
  rw [←card_neighborFinset_eq_degree K,h,card_insert_of_not_mem np,card_map,card_neighborFinset_eq_degree]

/-- A new edge incident to the prescribed last vertex gets one unit of
degree-sum slack; the other new edges need the ordinary terminal Ore sum. -/
theorem weighted_terminal_ore_closure (sub : G≤H) {x y : V}
    (deg : ∀ u v : V,H.Adj u v → ¬G.Adj u v →
      Fintype.card V+1≤G.degree u+G.degree v+(if u=y ∨ v=y then 1 else 0))
    (p : H.Walk x y) (pp : p.IsPath) (ps : ∀ v,v∈p.support) :
    ∃ q : G.Walk x y,q.IsPath ∧ ∀ v,v∈q.support := by
  classical
  let P (v : V) := v=y
  have hm : Graffiti189Ore.cap G P≤Graffiti189Ore.cap H P := by
    intro i j e
    cases i <;> cases j <;> try exact e
    exact sub e
  have hw : Graffiti189Ore.Rooted (Graffiti189Ore.cap H P) (some x) := by
    let q := p.map (liftCap H P)
    have qp : q.IsPath := IsPath.mk'
      (liftCap_support p ▸ pp.support_nodup.map (liftCap_injective H P))
    have off : (none : Option V)∉q.support := by
      change (none : Option V)∉(p.map (liftCap H P)).support
      rw [liftCap_support]
      simp
    let e : (Graffiti189Ore.cap H P).Adj (some y) none := rfl
    refine ⟨none,q.concat e,articulation_path_concat_new q qp e off,?_⟩
    intro z
    cases z with
    | none => exact (q.concat e).end_mem_support
    | some v =>
      rw [support_concat,List.concat_eq_append]
      exact List.mem_append_left _ (liftCap_support p ▸ List.mem_map.mpr ⟨v,ps v,rfl⟩)
  apply cap_path_forces_end
  apply Graffiti189Ore.rooted_closure hm (some x) _ hw
  intro i j e no
  cases i <;> cases j
  · exact (no e).elim
  · exact (no e).elim
  · exact (no e).elim
  rename_i u v
  have c := deg u v e no
  have zu := leaf_cap_degree_ge (G:=G) y u
  have zv := leaf_cap_degree_ge (G:=G) y v
  change G.degree u≤(Graffiti189Ore.cap G P).degree (some u) at zu
  change G.degree v≤(Graffiti189Ore.cap G P).degree (some v) at zv
  rw [Fintype.card_option]
  split at c
  · rename_i mark
    rcases mark with rfl | rfl
    · have k := leaf_degree_increased (G:=G) u
      change G.degree v≤(Graffiti189Ore.cap G (fun w=>w=u)).degree (some v) at zv
      change _ ≤ (Graffiti189Ore.cap G (fun w=>w=u)).degree (some u) +
        (Graffiti189Ore.cap G (fun w=>w=u)).degree (some v)
      omega
    have k := leaf_degree_increased (G:=G) v
    change G.degree u≤(Graffiti189Ore.cap G (fun w=>w=v)).degree (some u) at zu
    change _ ≤ (Graffiti189Ore.cap G (fun w=>w=v)).degree (some u) +
      (Graffiti189Ore.cap G (fun w=>w=v)).degree (some v)
    omega
  omega

private def starClose (G : SimpleGraph V) (M : Finset V) : SimpleGraph V where
  Adj x y := G.Adj x y ∨ (x≠y ∧ (x∈M ∨ y∈M))
  symm := fun _ _ h=>h.elim (fun e=>.inl e.symm) (fun e=>.inr ⟨e.1.symm,e.2.symm⟩)
  loopless := fun x h=>h.elim (G.loopless x) (fun h=>h.1 rfl)

private instance (G : SimpleGraph V) [DecidableRel G.Adj] (M : Finset V) :
    DecidableRel (starClose G M).Adj := fun _ _=>inferInstanceAs (Decidable (_ ∨ (_ ∧ _)))

private theorem star_mono (G : SimpleGraph V) (M : Finset V) : G≤starClose G M :=
  fun _ _ e=>.inl e

private theorem local_degree_mono (sub : G≤H) (x : V) : G.degree x≤H.degree x := by
  rw [←card_neighborFinset_eq_degree,←card_neighborFinset_eq_degree]
  exact card_le_card (fun y h=>(mem_neighborFinset _ _ _).mpr (sub ((mem_neighborFinset _ _ _).mp h)))

private theorem star_degree_of_marked (M : Finset V) {x : V} (xm : x∈M) :
    Fintype.card V-1≤(starClose G M).degree x := by
  have h : (univ.erase x : Finset V)⊆(starClose G M).neighborFinset x := by
    intro z hz
    exact (mem_neighborFinset _ _ _).mpr (.inr ⟨(mem_erase.mp hz).1.symm,.inl xm⟩)
  have c := card_le_card h
  rw [card_erase_of_mem (mem_univ _),card_univ,card_neighborFinset_eq_degree] at c
  exact c

private theorem star_degree_of_unmarked (M : Finset V) {x : V} (xm : x∉M) :
    M.card≤(starClose G M).degree x := by
  have h : M⊆(starClose G M).neighborFinset x := by
    intro z hz
    exact (mem_neighborFinset _ _ _).mpr (.inr ⟨fun e=>xm (e.symm ▸ hz),.inr hz⟩)
  have c := card_le_card h
  rwa [card_neighborFinset_eq_degree] at c

private theorem degree_strict_of_new_edge (sub : G≤H) {x y : V}
    (yes : H.Adj x y) (no : ¬G.Adj x y) : G.degree x+1≤H.degree x := by
  have i : insert y (G.neighborFinset x)⊆H.neighborFinset x := by
    intro z hz
    rcases mem_insert.mp hz with rfl|hz
    · exact (mem_neighborFinset _ _ _).mpr yes
    exact (mem_neighborFinset _ _ _).mpr (sub ((mem_neighborFinset _ _ _).mp hz))
  have t := card_le_card i
  rw [card_insert_of_not_mem (fun h=>no ((mem_neighborFinset _ _ _).mp h)),
    card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at t
  exact t

/-- A 10-vertex graph of minimum degree five, with at least one higher
degree, has a spanning path between one mark in each of two disjoint groups
provided every vertex outside those groups already has degree at least six. -/
theorem cross_marked_ten_ore (n : Fintype.card V=10) (A B : Finset V)
    (dis : Disjoint A B) (na : A.Nonempty) (nb : B.Nonempty)
    (minDeg : ∀ x,5≤G.degree x) {r : V} (hr : 6≤G.degree r)
    (dark : ∀ x,x∉A → x∉B → 6≤G.degree x) :
    ∃ x∈A,∃ y∈B,∃ p : G.Walk x y,p.IsPath ∧ ∀ z,z∈p.support := by
  classical
  let J := starClose G {r}
  have gJ : G≤J := star_mono G _
  have minJ (x : V) : 5≤J.degree x := (minDeg x).trans (local_degree_mono gJ x)
  have oreJ (u v : V) (uv : J.Adj u v) (no : ¬G.Adj u v) :
      Fintype.card V+1≤G.degree u+G.degree v := by
    have z : u=r ∨ v=r := by
      rcases uv with uv|uv
      · exact (no uv).elim
      simpa using uv.2
    rcases z with rfl|rfl
    · have k := minDeg v
      omega
    have k := minDeg u
    omega
  by_cases all : ∀ x,6≤J.degree x
  · obtain ⟨x,xa⟩ := na
    obtain ⟨y,yb⟩ := nb
    have xy : x≠y := fun e=>disjoint_left.mp dis xa (e.symm ▸ yb)
    obtain ⟨p,pp,ps⟩ := hamilton_connected_of_ore (G:=J)
      (fun u v _ _=>by have a:=all u; have b:=all v; omega) xy
    obtain ⟨q,qq,qs⟩ := terminal_ore_closure gJ oreJ p pp ps
    exact ⟨x,xa,y,yb,q,qq,qs⟩
  push_neg at all
  obtain ⟨p,p5⟩ := all
  have hp : J.degree p=5 := by have h := minJ p; omega
  have pr : p≠r := by
    intro eq
    have rJ := local_degree_mono gJ r
    rw [eq] at hp
    omega
  have port : p∈A ∨ p∈B := by
    by_cases a : p∈A
    · exact .inl a
    by_cases b : p∈B
    · exact .inr b
    have h := dark p a b
    have k := local_degree_mono gJ p
    omega
  let K := starClose J {p}
  have jK : J≤K := star_mono J _
  have minK (x : V) : 5≤K.degree x := (minJ x).trans (local_degree_mono jK x)
  let M := univ.filter (fun x=>6≤K.degree x)
  let E := (univ.erase p)\J.neighborFinset p
  have pd : (J.neighborFinset p)⊆(univ.erase p : Finset V) := by
    intro q h
    exact mem_erase.mpr ⟨((mem_neighborFinset _ _ _).mp h).ne.symm,mem_univ _⟩
  have e4 : E.card=4 := by
    change ((univ.erase p)\J.neighborFinset p).card=4
    rw [card_sdiff pd,card_erase_of_mem (mem_univ _),card_univ,card_neighborFinset_eq_degree,n,hp]
  have re : r∉E := by
    intro m
    apply (mem_sdiff.mp m).2
    exact (mem_neighborFinset _ _ _).mpr (.inr ⟨pr,.inr (by simp)⟩)
  have pe : p∉E := fun h=>(mem_erase.mp (mem_sdiff.mp h).1).1 rfl
  have eM : E⊆M := by
    intro x h
    obtain ⟨yes,no⟩ := mem_sdiff.mp h
    have neq := (mem_erase.mp yes).1
    have new : K.Adj x p := .inr ⟨neq,.inr (by simp)⟩
    have k := degree_strict_of_new_edge jK new (fun e=>no ((mem_neighborFinset _ _ _).mpr e.symm))
    exact mem_filter.mpr ⟨mem_univ _,(Nat.succ_le_succ (minJ x)).trans k⟩
  have pM : p∈M := by
    have z := star_degree_of_marked (G:=J) ({p}:Finset V) (mem_singleton_self p)
    exact mem_filter.mpr ⟨mem_univ _,by change Fintype.card V-1≤K.degree p at z; omega⟩
  have rM : r∈M := mem_filter.mpr ⟨mem_univ _,
    hr.trans ((local_degree_mono gJ r).trans (local_degree_mono jK r))⟩
  have m6 : 6≤M.card := by
    have h := card_le_card (show insert r (insert p E)⊆M from insert_subset rM (insert_subset pM eM))
    rw [card_insert_of_not_mem (by simp [pr.symm,re]),card_insert_of_not_mem pe,e4] at h
    omega
  let L := starClose K M
  have kL : K≤L := star_mono K _
  have minL (x : V) : 6≤L.degree x := by
    by_cases h : x∈M
    · exact (mem_filter.mp h).2.trans (local_degree_mono kL x)
    exact m6.trans (star_degree_of_unmarked (G:=K) M h)
  have oreL (u v : V) (uv : L.Adj u v) (no : ¬K.Adj u v) :
      Fintype.card V+1≤K.degree u+K.degree v := by
    have h : u∈M ∨ v∈M := uv.elim (fun e=>(no e).elim) And.right
    rcases h with h|h
    · have h1 := (mem_filter.mp h).2
      have h2 := minK v
      omega
    have h1 := (mem_filter.mp h).2
    have h2 := minK u
    omega
  have oreK (u v : V) (uv : K.Adj u v) (no : ¬J.Adj u v) :
      Fintype.card V+1≤J.degree u+J.degree v+(if u=p ∨ v=p then 1 else 0) := by
    have k : u=p ∨ v=p := by
      rcases uv with uv|uv
      · exact (no uv).elim
      simpa using uv.2
    rw [if_pos k]
    have a := minJ u
    have b := minJ v
    omega
  have finish {q : V} (pq : q≠p) :
      ∃ z : G.Walk q p,z.IsPath ∧ ∀ v,v∈z.support := by
    obtain ⟨l,lp,ls⟩ := hamilton_connected_of_ore (G:=L)
      (fun u v _ _=>by have a:=minL u; have b:=minL v; omega) pq
    obtain ⟨k,kp,ks⟩ := terminal_ore_closure kL oreL l lp ls
    obtain ⟨j,jp,js⟩ := weighted_terminal_ore_closure jK oreK k kp ks
    exact terminal_ore_closure gJ oreJ j jp js
  rcases port with pa|pb
  · obtain ⟨q,qb⟩ := nb
    have pq : q≠p := fun e=>disjoint_left.mp dis pa (e ▸ qb)
    obtain ⟨z,zp,zs⟩ := finish pq
    exact ⟨p,pa,q,qb,z.reverse,zp.reverse,by simpa only [support_reverse,List.mem_reverse] using zs⟩
  obtain ⟨q,qa⟩ := na
  have pq : q≠p := fun e=>disjoint_left.mp dis qa (e.symm ▸ pb)
  obtain ⟨z,zp,zs⟩ := finish pq
  exact ⟨q,qa,p,pb,z,zp,zs⟩

#print axioms weighted_terminal_ore_closure
#print axioms cross_marked_ten_ore
end Graffiti189LongestPath.CrossSaturation.ThresholdSix
