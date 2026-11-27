import OreSpliceIndex189
import Mathlib.Data.Fintype.Option

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*}

def cap (G : SimpleGraph V) (P : V → Prop) : SimpleGraph (Option V) where
  Adj x y := match x,y with
    | none, none => False
    | some x, none => P x
    | none, some y => P y
    | some x, some y => G.Adj x y
  symm := by
    intro x y
    cases x <;> cases y <;> try exact id
    exact fun h => G.symm h
  loopless := by intro x; cases x <;> simp

instance (G : SimpleGraph V) (P : V → Prop) [DecidableRel G.Adj]
    [DecidablePred P] : DecidableRel (cap G P).Adj := by
  intro x y
  cases x <;> cases y <;> unfold cap <;> infer_instance

def liftCap (G : SimpleGraph V) (P : V → Prop) : G →g cap G P where
  toFun := some
  map_rel' := id

theorem liftCap_injective (G : SimpleGraph V) (P : V → Prop) :
    Function.Injective (liftCap G P) := fun _ _ h=>Option.some.inj h

private theorem liftCap_support {G : SimpleGraph V} {P : V → Prop}
    {a b : V} (p : G.Walk a b) :
    (p.map (liftCap G P)).support = p.support.map some := by
  exact support_map _ _

theorem degree_cap_universal (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj] (x : V) :
    (cap G (fun _=>True)).degree (some x) = G.degree x + 1 := by
  classical
  let H := cap G (fun _=>True)
  let I : V ↪ Option V := ⟨some, Option.some_injective V⟩
  have e : H.neighborFinset (some x) = insert none ((G.neighborFinset x).map I) := by
    ext v
    cases v with
    | none => simp [H,mem_neighborFinset,cap]
    | some q => simp [H,mem_neighborFinset,cap,I]
  change (H.neighborFinset (some x)).card = _
  have Hnot : (none : Option V) ∉ (G.neighborFinset x).map I := by simp [I]
  rw [e,card_insert_of_not_mem Hnot, card_map,card_neighborFinset_eq_degree]

private theorem unliftCap {G : SimpleGraph V} {P : V → Prop}
    {a : V} {b : Option V} (p : (cap G P).Walk (.some a) b)
    (none_off : none ∉ p.support) :
    ∃ y : V, b=some y ∧ ∃ q : G.Walk a y, p.support=q.support.map some := by
  generalize ha : some a = va at p
  induction p generalizing a with
  | nil => exact ⟨a,ha.symm,.nil,by simp [←ha]⟩
  | @cons x v z e p ih =>
    subst x
    cases v with
    | none => exact False.elim (none_off (by simp))
    | some w =>
      obtain ⟨y,hy,q,hq⟩ := ih (a:=w) rfl (fun h=>none_off (by simp [h]))
      exact ⟨y,hy,.cons e q, by simp [hq]⟩

#print axioms degree_cap_universal
end Graffiti189Ore

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} {G : SimpleGraph V}

theorem cap_ring {P : V→Prop} {a b : V} (p : G.Walk a b)
    (hp : p.IsPath) (all : ∀ x, x ∈ p.support) (ab : a≠b) (ha : P a) (hb : P b) :
    ∃ c : (cap G P).Walk none none, SpanningRing c ∧ c.edges.Nodup ∧
      c.edges = s(none,some a) :: p.edges.map (Sym2.map some) ++ [s(some b,none)] := by
  let p' := p.map (liftCap G P)
  have na : (cap G P).Adj none (some a) := ha
  have bn : (cap G P).Adj (some b) none := hb
  let c := Walk.cons na (p'.concat bn)
  have ctail : c.support.tail = (p.support.map some).concat none := by
    simp only [c,support_cons,List.tail_cons,support_concat,p',liftCap_support]
  have ce : c.edges = s(none,some a) :: p.edges.map (Sym2.map some) ++ [s(some b,none)] := by
    simp only [c,Walk.concat,edges_cons,edges_append,p',edges_map,edges_nil]
    rfl
  have off : (none : Option V) ∉ p.support.map some := by simp
  have c' : p'.edges = p.edges.map (Sym2.map some) := edges_map _ _
  have npath : p'.IsPath := IsPath.mk' (liftCap_support p ▸ List.Nodup.map (fun _ _ h=>Option.some.inj h) hp.support_nodup)
  have absent (x : V) : s(none,some x) ∉ p'.edges := fun h => by
    have k := p'.fst_mem_support_of_mem_edges h
    exact off (liftCap_support p ▸ k)
  have ab' : s(none,(some a : Option V)) ≠ s(some b,none) := by
    intro h
    rw [Sym2.eq_swap] at h
    have h' := (Sym2.eq_iff.mp h)
    simp [ab] at h'
  refine ⟨c,⟨?_,?_⟩,?_,ce⟩
  · rw [ctail,List.concat_eq_append,List.nodup_append]
    exact ⟨List.Nodup.map (fun _ _ h=>Option.some.inj h) hp.support_nodup,
      by simp, fun w hw hnone => off ((List.mem_singleton.mp hnone) ▸ hw)⟩
  · intro x
    rw [ctail,List.concat_eq_append,List.mem_append]
    cases x with
    | none => exact Or.inr (by simp)
    | some z => exact Or.inl (List.mem_map.mpr ⟨z,all z,rfl⟩)
  · rw [ce,←c', List.cons_append, List.nodup_cons,List.nodup_append]
    refine ⟨?_,npath.edges_nodup,by simp,?_⟩
    · simp [absent a,ab']
    · intro e he h
      have eq : e = s(some b,none) := List.mem_singleton.mp h
      subst e
      rw [Sym2.eq_swap] at he
      exact absent b he

#print axioms cap_ring
end Graffiti189Ore

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk
variable {V : Type*} {G : SimpleGraph V}

theorem ring_to_cap_path {P : V→Prop} [DecidableEq V] {a : Option V}
    (c : (cap G P).Walk a a) (hc : SpanningRing c) :
    ∃ x y : V, ∃ p : G.Walk x y, P x ∧ P y ∧ p.IsPath ∧ ∀ v, v ∈ p.support := by
  have hn : none ∈ c.support := List.mem_of_mem_tail (hc.2 none)
  let r := c.rotate hn
  have rr : SpanningRing r := by
    have e := (support_rotate c hn).perm
    exact ⟨e.nodup_iff.mpr hc.1, fun v=>e.mem_iff.mpr (hc.2 v)⟩
  clear_value r
  cases r with
  | nil =>
    have h := rr.2 none
    simp at h
  | cons v p =>
    rename_i e
    cases e with
    | none => exact False.elim (by exact v)
    | some x =>
      have pp : p.IsPath := IsPath.mk' rr.1
      have all : ∀ w, w ∈ p.reverse.support := by simpa only [support_reverse,List.mem_reverse] using rr.2
      generalize ep : p.reverse = q at all
      have qp : q.IsPath := ep ▸ pp.reverse
      cases q with
      | cons ez rest =>
        rename_i z
        cases z with
        | none => exact False.elim (by exact ez)
        | some y =>
          obtain ⟨u,hu,l,hl⟩ := unliftCap rest ((cons_isPath_iff ez rest).1 qp).2
          have xu : x=u := Option.some.inj hu
          subst u
          have lup : l.IsPath := by
            have ln := ((cons_isPath_iff ez rest).1 qp).1.support_nodup
            exact IsPath.mk' (List.Nodup.of_map some (hl ▸ ln))
          refine ⟨x,y,l.reverse,v,ez,lup.reverse,?_⟩
          intro w
          rw [support_reverse,List.mem_reverse]
          have mem := all (some w)
          simp only [support_cons,List.mem_cons,reduceCtorEq, false_or,hl,List.mem_map] at mem
          obtain ⟨z,hz,eq⟩ := mem
          exact Option.some.inj eq ▸ hz

#print axioms ring_to_cap_path
end Graffiti189Ore

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

def Traceable (G : SimpleGraph V) : Prop :=
  ∃ a b : V, ∃ p : G.Walk a b, p.IsPath ∧ ∀ v, v ∈ p.support

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidableRel H.Adj] in
private theorem only_cap {u v : V}
    (only : ∀ x y, H.Adj x y → G.Adj x y ∨ s(x,y)=s(u,v)) :
    ∀ x y : Option V, (cap H (fun _=>True)).Adj x y →
      (cap G (fun _=>True)).Adj x y ∨ s(x,y)=s(some u,some v) := by
  intro x y e
  cases x <;> cases y <;> try exact Or.inl e
  obtain g|g := only _ _ e
  · exact Or.inl g
  · exact Or.inr (congrArg (Sym2.map some) g)

omit [Fintype V] [DecidableEq V] in
private theorem only_edgeSet {W : Type*} {A B : SimpleGraph W} {k : Sym2 W}
    (only : ∀ x y, B.Adj x y → A.Adj x y ∨ s(x,y)=k) :
    ∀ e ∈ B.edgeSet, e ∈ A.edgeSet ∨ e=k := by
  intro e
  induction e using Sym2.ind with
  | h x y => simpa only [SimpleGraph.mem_edgeSet] using only x y

omit [DecidableEq V] [DecidableRel H.Adj] in
theorem traceable_closure_one {u v : V}
    (only : ∀ x y, H.Adj x y → G.Adj x y ∨ s(x,y)=s(u,v))
    (deg : Fintype.card V ≤ G.degree u + G.degree v + 1)
    (ht : Traceable H) : Traceable G := by
  classical
  obtain ⟨a,b,p,hp,all⟩ := ht
  by_cases h : s(u,v) ∈ p.edges
  swap
  · have ed : ∀ e ∈ p.edges, e ∈ G.edgeSet := by
      intro e he
      exact (only_edgeSet only e (p.edges_subset_edgeSet he)).resolve_right
        (fun eq=>h (eq ▸ he))
    let q := p.transfer G ed
    have qs : q.support=p.support := support_transfer p ed
    exact ⟨a,b,q,IsPath.mk' (qs ▸ hp.support_nodup),fun w=>qs ▸ all w⟩
  have ab : a≠b := by
    intro eq
    subst b
    have e0 : 0=p.length := (hp.getVert_eq_end_iff (Nat.zero_le _)).mp (by simp)
    have zn := length_eq_zero_iff.mp e0.symm
    simp [zn] at h
  obtain ⟨c,hc,cn,_⟩ := cap_ring (P:=fun _=>True) p hp all ab trivial trivial
  have he : s((some u : Option V),some v) ∈ c.edges := by
    rename_i hen
    rw [hen]
    simp only [List.cons_append,List.mem_cons,List.mem_append]
    exact Or.inr (Or.inl (List.mem_map.mpr ⟨_,h,rfl⟩))
  obtain ⟨x,y,w,wp,wa,xye,we⟩ := cut_spanning_ring hc he cn
  have transfer : ∀ e ∈ w.edges, e ∈ (cap G (fun _=>True)).edgeSet := by
    intro e he'
    obtain ⟨_,hn⟩ := we e he'
    exact (only_edgeSet (only_cap only) e (w.edges_subset_edgeSet he')).resolve_right hn
  let q := w.transfer (cap G (fun _=>True)) transfer
  have qs : q.support=w.support := support_transfer w transfer
  have qp : q.IsPath := IsPath.mk' (qs ▸ wp.support_nodup)
  have qa : ∀ z, z ∈ q.support := fun z=>qs ▸ wa z
  have eqlen : q.length + 1 = Fintype.card (Option V) := by
    rw [← length_support,← List.toFinset_card_of_nodup qp.support_nodup]
    have e : q.support.toFinset=univ := eq_univ_of_forall (fun z=>List.mem_toFinset.mpr (qa z))
    rw [e,card_univ]
  have ends := Sym2.eq_iff.mp xye
  have dsum : q.length < (cap G (fun _=>True)).degree x + (cap G (fun _=>True)).degree y := by
    rcases ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;>
      rw [degree_cap_universal,degree_cap_universal] <;>
      simp only [Fintype.card_option] at eqlen <;> omega
  obtain ⟨ring,hr⟩ := ore_ring q qp qa dsum
  obtain ⟨x',y',p',_,_,path,all'⟩ := ring_to_cap_path ring hr
  exact ⟨x',y',p',path,all'⟩

#print axioms traceable_closure_one
end Graffiti189Ore

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj]

def Rooted (G : SimpleGraph V) (root : V) : Prop :=
  ∃ b : V, ∃ p : G.Walk root b, p.IsPath ∧ ∀ v, v ∈ p.support

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem rooted_cap_traceable {r : V} (h : Rooted G r) :
    Traceable (cap G (fun x=>x=r)) := by
  obtain ⟨b,p,path,all⟩ := h
  let P : V→Prop := fun x=>x=r
  let q := p.map (liftCap G P)
  have qp : q.IsPath := IsPath.mk' (liftCap_support p ▸
    List.Nodup.map (fun _ _ eq=>Option.some.inj eq) path.support_nodup)
  have off : (none : Option V) ∉ q.support := by simp [q,liftCap_support,liftCap]
  have e : (cap G P).Adj none (some r) := rfl
  refine ⟨none,some b,.cons e q,qp.cons off,?_⟩
  intro x
  cases x with
  | none => simp
  | some y =>
    exact List.mem_cons_of_mem _ (liftCap_support p ▸ List.mem_map.mpr ⟨y,all y,rfl⟩)

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem leaf_cap_neighbor {r : V} {v : Option V}
    (h : (cap G (fun x=>x=r)).Adj none v) : v=some r := by
  cases v with
  | none => exact False.elim h
  | some x => exact congrArg some h

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem leaf_cap_traceable_rooted {r : V} (h : Traceable (cap G (fun x=>x=r))) :
    Rooted G r := by
  obtain ⟨a,b,p,path,all⟩ := h
  have end_leaf : a=none ∨ b=none := by
    by_contra bad
    push_neg at bad
    obtain ⟨i,eq,hi⟩ := mem_support_iff_exists_getVert.mp (all none)
    have big : 0<i := by
      by_contra h
      have i0 : i=0 := by omega
      exact bad.1 (by simpa [i0] using eq)
    have small : i<p.length := by
      by_contra h
      have il : i=p.length := by omega
      exact bad.2 (by simpa [il] using eq)
    have ep := p.adj_getVert_succ (i:=i-1) (by omega)
    have en := p.adj_getVert_succ small
    rw [show i-1+1=i by omega,eq] at ep
    rw [eq] at en
    have same := (leaf_cap_neighbor ep.symm).trans (leaf_cap_neighbor en).symm
    have badEq := path.getVert_injOn (by simp; omega : i-1 ∈ {j | j ≤ p.length})
      (by simp; omega : i+1 ∈ {j | j ≤ p.length}) same
    omega
  have form : ∃ y : Option V, ∃ q : (cap G (fun x=>x=r)).Walk none y,
      q.IsPath ∧ ∀ v, v ∈ q.support := by
    rcases end_leaf with a'|b'
    · subst a; exact ⟨_,p,path,all⟩
    · subst b
      refine ⟨_,p.reverse,path.reverse,?_⟩
      simpa only [support_reverse,List.mem_reverse] using all
  obtain ⟨y,q,qp,qa⟩ := form
  cases q with
  | nil =>
    have bad := qa (some r)
    simp at bad
  | cons e w =>
    have eq := leaf_cap_neighbor e
    subst_vars
    obtain ⟨z,_,l,ls⟩ := unliftCap w ((cons_isPath_iff e w).1 qp).2
    refine ⟨z,l,IsPath.mk' (List.Nodup.of_map some
      (ls ▸ ((cons_isPath_iff e w).1 qp).1.support_nodup)),?_⟩
    intro x
    have xm := qa (some x)
    simp only [support_cons,List.mem_cons,reduceCtorEq,false_or,ls,List.mem_map] at xm
    obtain ⟨v,vm,eq⟩ := xm
    exact (Option.some.inj eq) ▸ vm

private theorem leaf_cap_degree_other (r x : V) (xr : x≠r) :
    (cap G (fun v=>v=r)).degree (some x) = G.degree x := by
  classical
  let K := cap G (fun v=>v=r)
  let I : V ↪ Option V := ⟨some, Option.some_injective V⟩
  have e : K.neighborFinset (some x) = (G.neighborFinset x).map I := by
    ext v
    cases v with
    | none => simp [K,mem_neighborFinset,cap,xr]
    | some q => simp [K,mem_neighborFinset,cap,I]
  change (K.neighborFinset (some x)).card = _
  rw [e,card_map,card_neighborFinset_eq_degree]

private theorem leaf_cap_degree_ge (r x : V) :
    G.degree x ≤ (cap G (fun v=>v=r)).degree (some x) := by
  classical
  let K := cap G (fun v=>v=r)
  let I : V ↪ Option V := ⟨some, Option.some_injective V⟩
  have sub : (G.neighborFinset x).map I ⊆ K.neighborFinset (some x) := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_map.mp hz
    exact (mem_neighborFinset K _ _).mpr ((mem_neighborFinset G _ _).mp hx)
  have le := card_le_card sub
  simpa [K,card_map,card_neighborFinset_eq_degree] using le

omit [DecidableEq V] in
theorem rooted_closure_one {u v : V} (r : V)
    (only : ∀ x y, H.Adj x y → G.Adj x y ∨ s(x,y)=s(u,v))
    (deg : Fintype.card V ≤ G.degree u + G.degree v)
    (h : Rooted H r) : Rooted G r := by
  classical
  let P : V→Prop := fun x=>x=r
  have oc : ∀ x y : Option V, (cap H P).Adj x y →
      (cap G P).Adj x y ∨ s(x,y)=s(some u,some v) := by
    intro x y e
    cases x <;> cases y <;> try exact Or.inl e
    obtain g|g := only _ _ e
    · exact Or.inl g
    · exact Or.inr (congrArg (Sym2.map some) g)
  have d : Fintype.card (Option V) ≤ (cap G P).degree (some u) + (cap G P).degree (some v) + 1 := by
    have e := leaf_cap_degree_ge (G:=G) r u
    have f := leaf_cap_degree_ge (G:=G) r v
    change G.degree u ≤ (cap G P).degree (some u) at e
    change G.degree v ≤ (cap G P).degree (some v) at f
    rw [Fintype.card_option]
    omega
  exact leaf_cap_traceable_rooted (traceable_closure_one oc d (rooted_cap_traceable h))

#print axioms rooted_closure_one
end Graffiti189Ore

namespace Graffiti189Ore
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V]
variable {G H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]

private theorem degree_increasing {A B : SimpleGraph V} [DecidableRel A.Adj] [DecidableRel B.Adj]
    (ab : A≤B) (x : V) : A.degree x ≤ B.degree x := by
  have c : A.neighborFinset x ⊆ B.neighborFinset x := fun y hy =>
    (mem_neighborFinset B x y).mpr (ab ((mem_neighborFinset A x y).mp hy))
  exact card_le_card c

noncomputable def graphSize (A : SimpleGraph V) : ℕ := by
  classical
  exact A.edgeFinset.card

private theorem graphSize_lt {A B : SimpleGraph V} (h : A<B) : graphSize A < graphSize B := by
  classical
  exact card_lt_card (edgeFinset_strict_mono h)

private theorem graphSize_le {A B : SimpleGraph V} (h : A≤B) : graphSize A ≤ graphSize B := by
  classical
  exact card_le_card (edgeFinset_mono h)

omit [DecidableRel H.Adj] in
/-- Root-preserving Ore closure: all additional edges may be removed if
each corresponding original degree sum is at least the graph order. -/
theorem rooted_closure (sub : G ≤ H) (r : V)
    (hdeg : ∀ x y, H.Adj x y → ¬ G.Adj x y → Fintype.card V ≤ G.degree x + G.degree y)
    (hp : Rooted H r) : Rooted G r := by
  classical
  induction hn : graphSize H-graphSize G using Nat.strong_induction_on generalizing G with
  | h n ih =>
    by_cases eq : G=H
    · simpa [eq] using hp
    have not_sub : ¬ H ≤ G := fun e=>eq (le_antisymm sub e)
    have missing : ∃ u v, H.Adj u v ∧ ¬G.Adj u v := by
      by_contra neg
      push_neg at neg
      exact not_sub (fun {u v} e=>neg u v e)
    obtain ⟨u,v,uv,nu⟩ := missing
    let K := G ⊔ fromEdgeSet ({s(u,v)} : Set (Sym2 V))
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    have gk : G≤K := le_sup_left
    have kh : K≤H := by
      intro x y e
      rcases (sup_adj _ _ x y).mp e with e|e
      · exact sub e
      · obtain ⟨es,_⟩ := (fromEdgeSet_adj _).mp e
        have eqs : s(x,y)=s(u,v) := es
        apply (SimpleGraph.mem_edgeSet H).mp
        rw [eqs]
        exact (SimpleGraph.mem_edgeSet H).mpr uv
    have kv : K.Adj u v := (sup_adj _ _ _ _).mpr (Or.inr ((fromEdgeSet_adj _).mpr ⟨rfl,uv.ne⟩))
    have glt : G < K := lt_of_le_of_ne gk (fun e=>nu (e.symm ▸ kv))
    have less : graphSize H-graphSize K<n := by
      have smaller := graphSize_lt glt
      have below := graphSize_le kh
      omega
    have nd (x y : V) (e : H.Adj x y) (k : ¬K.Adj x y) :
        Fintype.card V ≤ K.degree x+K.degree y := by
      have orig := hdeg x y e (fun g=>k (gk g))
      exact orig.trans (Nat.add_le_add (degree_increasing gk x) (degree_increasing gk y))
    have rr := ih _ less (G:=K) kh nd rfl
    refine rooted_closure_one r (u:=u) (v:=v) ?_ (hdeg u v uv nu) rr
    intro x y e
    rcases (sup_adj _ _ x y).mp e with e|e
    · exact Or.inl e
    · exact Or.inr ((fromEdgeSet_adj _).mp e).1

#print axioms rooted_closure
end Graffiti189Ore
