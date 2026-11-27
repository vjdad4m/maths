import PrivateAnchor180

set_option warningAsError true
namespace Minimal180.PrivateCore
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180 Controlled
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The certificate obtained by returning x,b and releasing Z is valid in the upper graph. -/
def PairWorks (J : SimpleGraph V) (C Z : Finset V) (x y b : V) : Prop :=
  let L := (C.erase x).erase b ∪ Z
  let G := J⊔SimpleGraph.edge x y
  Con G (univ\L) ∧ ∀ q∈L,Dominates G (univ\L) q

private theorem private_demand (J : SimpleGraph V) (C Z : Finset V) (x z q : V)
    (hz : z∈Z) (priv : q∈privateLeaves J C x z) (far : ¬NearTwo J x q) :
    q∈demand J ((univ\C)\Z) C Z x := by
  obtain ⟨qc,_,only⟩ := (private_iff ..).mp priv
  refine (mem_demand ..).mpr ⟨mem_union_left _ qc,?_,fun e => far (Or.inr (Or.inl e.symm))⟩
  rintro ⟨a,ar,qa⟩
  exact (mem_sdiff.mp ar).2 (only a (mem_sdiff.mp ar).1 qa ▸ hz)

/-- A pair repair releasing even one failed non-cut vertex with a single
private leaf must return an old nonneighbor of x adjacent to that leaf.
It must meet the retained core, even when that core is disconnected. -/
theorem forced_detached_return (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (U C Z : Finset V) (x y z q b : V) (xy : x≠y) (cu : C⊆U) (ct : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (free : Z⊆(U\C).erase y) (hz : z∈Z)
    (safe : Con J ((univ\C).erase z)) (failed : ¬SingleWorks J C x y z)
    (unique : privateLeaves J C x z={q}) (bc : b∈C.erase x) (wins : PairWorks J C Z x y b) :
    ¬J.Adj x b ∧ J.Adj b q ∧ Dominates J ((univ\C)\Z) b := by
  classical
  let R := (univ\C)\Z
  have far := singleton_far J hc hn U C x y z q xy cu ct tip (free hz) safe failed unique
  have priv : q∈privateLeaves J C x z := unique ▸ mem_singleton_self q
  have d := private_demand J C Z x z q hz priv far
  have zs : Z⊆(univ\C).erase y := fun a ha => mem_erase.mpr ⟨(mem_erase.mp (free ha)).1,
    mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp (mem_of_mem_erase (free ha))).2⟩⟩
  obtain ⟨join,serve⟩ := (pair_exchange_iff J C Z x y b xy tip bc zs).mp wins
  have yr : y∈R := mem_sdiff.mpr ⟨tip.2.1,fun h => (mem_erase.mp (free h)).1 rfl⟩
  have lower : Dominates J R b ∨ J.Adj x b := by
    rcases join y yr with ⟨i,hi,bi⟩|⟨xb,_⟩
    · exact Or.inl ⟨i,((mem_part ..).mp hi).1,bi⟩
    · exact Or.inr xb
  rcases serve q d with eq|qb
  · subst b
    rcases lower with qr|xq
    · exact ((mem_demand ..).mp d).2.1 qr |>.elim
    · exact (far (Or.inr (Or.inl xq))).elim
  · have no : ¬J.Adj x b := fun xb => far (Or.inr (Or.inr ⟨b,xb,qb.symm⟩))
    exact ⟨no,qb.symm,lower.resolve_right no⟩

/-- For two individually failed singleton-private releases, with a connected
retained core, the admissible returns are exactly the old common neighbors
of the two private leaves which meet the retained core. A leaf supported
on both releases alone is allowed whenever x already dominates it. -/
theorem detached_pair_iff (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (U C : Finset V) (x y p t u v b : V) (xy : x≠y) (cu : C⊆U) (ct : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (free : ({p,t}:Finset V)⊆(U\C).erase y)
    (safe : ∀ z∈({p,t}:Finset V),Con J ((univ\C).erase z))
    (failed : ∀ z∈({p,t}:Finset V),¬SingleWorks J C x y z)
    (pu : privateLeaves J C x p={u}) (tv : privateLeaves J C x t={v})
    (conn : Con J ((univ\C)\{p,t}))
    (feed : ∀ z∈({p,t}:Finset V),Dominates J ((univ\C)\{p,t}) z)
    (mixed : ∀ a∈C.erase x, J.Adj a p → J.Adj a t → ¬Dominates J ((univ\C)\{p,t}) a → J.Adj a x)
    (bc : b∈C.erase x) :
    PairWorks J C {p,t} x y b ↔ ¬J.Adj x b ∧ J.Adj b u ∧ J.Adj b v ∧ Dominates J ((univ\C)\{p,t}) b := by
  classical
  let Z : Finset V := {p,t}
  let R := (univ\C)\Z
  have hp : p∈Z := mem_insert_self .. 
  have ht : t∈Z := mem_insert_of_mem (mem_singleton_self _)
  constructor
  · intro yes
    obtain ⟨no,bu,dom⟩ := forced_detached_return J hc hn U C Z x y p u b xy cu ct tip free hp
      (safe p hp) (failed p hp) pu bc yes
    have other := forced_detached_return J hc hn U C Z x y t v b xy cu ct tip free ht
      (safe t ht) (failed t ht) tv bc yes
    exact ⟨no,bu,other.2.1,dom⟩
  · rintro ⟨_,bu,bv,bd⟩
    have zs : Z⊆(univ\C).erase y := fun a ha => mem_erase.mpr ⟨(mem_erase.mp (free ha)).1,
      mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp (mem_of_mem_erase (free ha))).2⟩⟩
    apply (pair_exchange_iff J C Z x y b xy tip bc zs).mpr
    constructor
    · intro a ar
      have eq : part J R a=R := part_eq_of_closed J R R a ar (Subset.rfl) conn (fun _ _ _ jr _ => jr)
      exact Or.inl (eq ▸ bd)
    · intro a ad
      obtain ⟨place,miss,nx⟩ := (mem_demand ..).mp ad
      rcases mem_union.mp place with ac|az
      · have only (i : V) (is' : i∈univ\C) (e : J.Adj a i) : i=p ∨ i=t := by
          by_contra neither
          have nz : i∉Z := by simpa only [Z,mem_insert,mem_singleton] using neither
          exact miss ⟨i,mem_sdiff.mpr ⟨is',nz⟩,e⟩
        obtain ⟨i,is',ai⟩ := tip.2.2.2.2 a (mem_of_mem_erase ac) (mem_erase.mp ac).1
        rcases only i is' ai with rfl|rfl
        · have nt : ¬J.Adj a t := fun at' => nx (mixed a ac ai at' miss)
          have h := (private_iff J C x i a).mpr ⟨ac,ai,fun j js aj =>
            (only j js aj).resolve_right (fun eq => nt (eq ▸ aj))⟩
          exact Or.inr ((mem_singleton.mp (pu ▸ h)) ▸ bu.symm)
        · have np : ¬J.Adj a p := fun ap => nx (mixed a ac ap ai miss)
          have h := (private_iff J C x i a).mpr ⟨ac,ai,fun j js aj =>
            (only j js aj).resolve_left (fun eq => np (eq ▸ aj))⟩
          exact Or.inr ((mem_singleton.mp (tv ▸ h)) ▸ bv.symm)
      · exact (miss (feed a az)).elim

#print axioms forced_detached_return
#print axioms detached_pair_iff
end Minimal180.PrivateCore
