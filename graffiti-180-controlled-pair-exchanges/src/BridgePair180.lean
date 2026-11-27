import GateBound180
set_option warningAsError true
namespace Minimal180.Controlled
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
/-- An old edge that is the only edge between two sides of the old core. -/
def BridgeIn (J : SimpleGraph V) (S : Finset V) (p q : V) : Prop :=
  J.Adj p q ∧ ∃ f : V→Bool, f p≠f q ∧
    ∀ i∈S\{p,q},∀ j∈S,J.Adj i j → f i=f j

omit [Fintype V] in
theorem component_exit (J : SimpleGraph V) (S Z : Finset V) (conn : Con J S)
    (p a : V) (ps : p∈S) (pz : p∈Z) (ar : a∈S\Z) :
    ∃ i∈part J (S\Z) a,∃ j∈Z,J.Adj i j := by
  classical
  let R := S\Z
  let H := part J R a
  by_contra no
  have closed {i j : V} (ih : i∈H) (js : j∈S) (e : J.Adj i j) : j∈H := by
    have nz : j∉Z := fun h => no ⟨i,ih,j,h,e⟩
    have jr : j∈R := mem_sdiff.mpr ⟨js,nz⟩
    obtain ⟨ir,ai⟩ := (mem_part ..).mp ih
    exact (mem_part ..).mpr ⟨jr,ai.trans (show (within J R).Adj i j from ⟨e,ir,jr⟩).reachable⟩
  let f (v : V) := decide (v∈H)
  have edges : OnEdges J S f := fun i hi j hj e => decide_eq_decide.mpr
    ⟨fun h => closed h hj e,fun h => closed h hi e.symm⟩
  have eq := ((connected_cuts J S).mp conn).2 f edges a (mem_sdiff.mp ar).1 p ps
  have ah : a∈H := (mem_part ..).mpr ⟨ar,.refl _⟩
  have ph : p∉H := fun h => (mem_sdiff.mp ((mem_part ..).mp h).1).2 pz
  simp [f,ah,ph] at eq

omit [Fintype V] in
theorem two_port_count (J : SimpleGraph V) (S : Finset V) (p q y s t : V)
    (conn : Con J S) (ps : p∈S) (yr : y∈S\{p,q}) (sr : s∈S\{p,q}) (tr : t∈S\{p,q})
    (left : ∀ i∈S\{p,q},J.Adj p i → i=s ∨ J.Adj i s)
    (right : ∀ i∈S\{p,q},J.Adj q i → i=t ∨ J.Adj i t) :
    (remote J (S\{p,q}) y).card≤1 := by
  classical
  let Z : Finset V := {p,q}
  let R := S\Z
  let A := R.image (part J R)
  have sub : A⊆{part J R s,part J R t} := by
    intro H h
    obtain ⟨a,ar,rfl⟩ := mem_image.mp h
    obtain ⟨i,ih,v,vz,e⟩ := component_exit J S Z conn p a ps (mem_insert_self ..) ar
    obtain ⟨ir,ai⟩ := (mem_part ..).mp ih
    have via {u:V} (ur:u∈R) (step:i=u ∨ J.Adj i u) : part J R a=part J R u := by
      rcases step with eq|adj
      · exact part_eq_of_reach J R (eq ▸ ai)
      · exact part_eq_of_reach J R (ai.trans (show (within J R).Adj i u from ⟨adj,ir,ur⟩).reachable)
    rcases mem_insert.mp vz with vp|vq
    · exact mem_insert.mpr (Or.inl (via sr (left i ir (vp ▸ e.symm))))
    · have vq' := mem_singleton.mp vq
      exact mem_insert.mpr (Or.inr (mem_singleton.mpr (via tr (right i ir (vq' ▸ e.symm)))))
  have ct := card_le_card sub
  have up : ({part J R s,part J R t}:Finset (Finset V)).card≤2 :=
    (card_insert_le ..).trans (by simp)
  have del := card_erase_add_one (show part J R y∈A from mem_image_of_mem _ yr)
  change (A.erase (part J R y)).card≤1
  omega

omit [Fintype V] in
theorem gates_of_bridge (J : SimpleGraph V) (S : Finset V) (p q y : V)
    (bridge : BridgeIn J S p q) (ps : p∈S) (qs : q∈S) :
    ∀ H∈remote J (S\{p,q}) y,∃ z∈({p,q}:Finset V),∀ i∈H,∀ j∈({p,q}:Finset V),J.Adj i j → j=z := by
  classical
  let R := S\{p,q}
  obtain ⟨f,neq,stable⟩ := bridge.2
  intro H hr
  obtain ⟨a,ar,eq⟩ := mem_image.mp (mem_of_mem_erase hr)
  have route {i j : V} (walk : (within J R).Walk i j) : f i=f j := by
    induction walk with
    | nil => rfl
    | cons e _ ih => exact (stable _ e.2.1 _ (mem_sdiff.mp e.2.2).1 e.1).trans ih
  have label {i : V} (h : i∈H) : i∈R ∧ f a=f i := by
    obtain ⟨ir,path⟩ := (mem_part ..).mp (eq ▸ h)
    obtain ⟨walk⟩ := path
    exact ⟨ir,route walk⟩
  have side {i j : V} (hi:i∈H) (js:j∈S) (ij:J.Adj i j) : f a=f j :=
    (label hi).2.trans (stable i (label hi).1 j js ij)
  by_cases same : f a=f p
  · refine ⟨p,mem_insert_self ..,?_⟩
    intro i hi j hj e
    rcases mem_insert.mp hj with jp|jq
    · exact jp
    · have jq' := mem_singleton.mp jq
      have e' : J.Adj i q := jq' ▸ e
      exact (neq (same.symm.trans (side hi qs e'))).elim
  · refine ⟨q,mem_insert_of_mem (mem_singleton_self _),?_⟩
    intro i hi j hj e
    rcases mem_insert.mp hj with jp|jq
    · exact (same (side hi ps (jp ▸ e))).elim
    · exact mem_singleton.mp jq

/-- Local bridge criterion for a genuine two-vertex repair, with no
preselected return or retained-component decomposition. Each side has an
old port adjacent to every other retained neighbor of its endpoint. -/
theorem pair_of_bridge_ports (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w p q s t : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (zs : ({p,q}:Finset V)⊆(U\C).erase y)
    (nc : NoCut (J⊔SimpleGraph.edge x y)) (sat : ∀ b∈C.erase x,J.Adj x b)
    (bridge : BridgeIn J (univ\C) p q)
    (sr : s∈(univ\C)\{p,q}) (tr : t∈(univ\C)\{p,q}) (ps : J.Adj p s) (qt : J.Adj q t)
    (left : ∀ i∈(univ\C)\{p,q},J.Adj p i → i=s ∨ J.Adj i s)
    (right : ∀ i∈(univ\C)\{p,q},J.Adj q i → i=t ∨ J.Adj i t) :
    FirstForm J U x y w ∧ ∃ b∈C.erase x, let L := (C.erase x).erase b ∪ {p,q}
      L⊆U\{x,y} ∧ L.card=C.card ∧ L\C={p,q} ∧ C\L={x,b} ∧
      Con (J⊔SimpleGraph.edge x y) (univ\L) ∧ ∀ z∈L,Dominates (J⊔SimpleGraph.edge x y) (univ\L) z := by
  classical
  let Z : Finset V := {p,q}
  have ins {v : V} (h : v∈Z) : v∈univ\C :=
    mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp (mem_of_mem_erase (zs h))).2⟩
  have yr : y∈(univ\C)\Z := mem_sdiff.mpr ⟨tip.2.1,fun h => (mem_erase.mp (zs h)).1 rfl⟩
  have pS := ins (mem_insert_self p {q})
  have qS := ins (mem_insert_of_mem (mem_singleton_self q))
  apply pair_of_at_most_one J hc hn x y w xy old xw wy U C Z cu count tip zs (card_pair bridge.1.ne) nc sat
  · intro z hz
    rcases mem_insert.mp hz with eq|k
    · exact ⟨s,sr,eq ▸ ps⟩
    · exact ⟨t,tr,mem_singleton.mp k ▸ qt⟩
  · exact two_port_count J (univ\C) p q y s t tip.2.2.1 pS yr sr tr left right
  · exact gates_of_bridge J (univ\C) p q y bridge pS qS

#print axioms two_port_count
#print axioms gates_of_bridge
#print axioms pair_of_bridge_ports
end Minimal180.Controlled
