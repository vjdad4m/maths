import SingletonJunction

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge
open Substitute
set_option maxHeartbeats 6000000
noncomputable section
variable {V : Type*} [DecidableEq V]
variable {G K : SimpleGraph V}

private theorem tri_path {a b c : V} (ab : G.Adj a b) (bc : G.Adj b c) (ac : a≠c) :
    Closed G ({a,b,c} : Finset V) := by
  have n : ({a,b,c} : Finset V).card=3 := by simp [ab.ne,bc.ne,ac]
  exact tile_closed ⟨n,(Kelmans.tile_iff_path G _ n).mpr
    ⟨a,b,c,ab.ne,ac,bc.ne,ab,bc,rfl⟩⟩

/-- At a singleton junction, a triangle and a nonzero-residue terminal
can absorb a rooted cap tile that avoids its link toward the closed
third shore. The cap root may use the singleton-facing port, the
triangle-facing port, or both. -/
theorem triangle_and_singleton_absorb_cap
    {C : Finset V} {x a b c d e : V}
    (xC : x∉C) (aC : a∉C) (bC : b∉C) (cC : c∉C)
    (xa : x≠a) (xc : x≠c)
    (xb : G.Adj x b) (ab : G.Adj a b) (bc : G.Adj b c) (ac : G.Adj a c)
    (xd : G.Adj x d) (ae : G.Adj a e)
    (cap : Closed K (insert x C))
    (nbr : ∀ u∈C,K.Adj x u→u=d ∨ u=e)
    (keep : ∀ u∈C,∀ v∈C,K.Adj u v→G.Adj u v) :
    Closed G (C∪{x,a,b,c}) := by
  classical
  obtain ⟨P,hP⟩ := cap
  obtain ⟨T,TP,xT⟩ := mem_biUnion.mp (hP.cover.symm ▸ mem_insert_self x C)
  have Tsub : T⊆insert x C := hP.tile_sub K TP
  have other {u : V} (mu : u∈T) (e : u≠x) : u∈C := by
    rcases mem_insert.mp (Tsub mu) with h|h
    · exact (e h).elim
    · exact h
  have rests : (insert x C)\T=C\T := by
    ext v
    simp only [mem_sdiff,mem_insert]
    constructor
    · rintro ⟨e|e,notT⟩
      · exact (notT (e.symm ▸ xT)).elim
      · exact ⟨e,notT⟩
    · rintro ⟨e,notT⟩
      exact ⟨Or.inr e,notT⟩
  have rem : Closed G (C\T) := by
    have good := remove_tile hP TP
    rw [rests] at good
    exact ⟨_,change_edges (G:=G) good
      (fun u um v vm=>keep _ (mem_sdiff.mp um).1 _ (mem_sdiff.mp vm).1)⟩
  have notext {z : V} (zC : z∈C) :
      z≠x ∧ z≠a ∧ z≠b ∧ z≠c :=
    ⟨fun e=>xC (e ▸ zC),fun e=>aC (e ▸ zC),fun e=>bC (e ▸ zC),fun e=>cC (e ▸ zC)⟩
  have repair {u v : V} (ut : u∈T) (vt : v∈T)
      (shape : T={x,u,v}) (part : Closed G ({x,a,b,c}∪{u,v})) :
      Closed G (C∪{x,a,b,c}) := by
    have sep : Disjoint (C\T) ({x,a,b,c}∪{u,v}) := by
      apply disjoint_left.mpr
      intro z m e
      obtain ⟨zC,zT⟩ := mem_sdiff.mp m
      have h := notext zC
      simp only [mem_union,mem_insert,mem_singleton] at e
      rcases e with ⟨e|e|e|e⟩|⟨e|e⟩
      · exact h.1 e
      · exact h.2.1 e
      · exact h.2.2.1 e
      · exact h.2.2.2 e
      · exact zT (e.symm ▸ ut)
      · exact zT (e.symm ▸ vt)
    have pasted := add_closed rem part sep
    have join : (C\T)∪({x,a,b,c}∪{u,v})=C∪{x,a,b,c} := by
      ext z
      have uu : z=u→z=x ∨ z∈C := fun eq=>mem_insert.mp (Tsub (eq.symm ▸ ut))
      have vv : z=v→z=x ∨ z∈C := fun eq=>mem_insert.mp (Tsub (eq.symm ▸ vt))
      simp only [shape,mem_union,mem_sdiff,mem_insert,mem_singleton]
      tauto
    exact join ▸ pasted
  have leaf {u v : V} (uT : u∈T) (vT : v∈T)
      (ux : u≠x) (vx : v≠x) (uv : K.Adj u v) (xu : K.Adj x u)
      (shape : T={x,u,v}) : Closed G (C∪{x,a,b,c}) := by
    have uC := other uT ux
    have vC := other vT vx
    have un := notext uC
    have vn := notext vC
    have adj := keep u uC v vC uv
    apply repair uT vT shape
    rcases nbr _ uC xu with same|same
    · have ud : G.Adj x u := same.symm ▸ xd
      have part := tri_path ud adj vn.1.symm
      have tr := tri_path ab bc ac.ne
      have sep : Disjoint ({x,u,v}:Finset V) ({a,b,c}:Finset V) := by
        apply disjoint_left.mpr
        intro z co atTri
        simp only [mem_insert,mem_singleton] at co atTri
        rcases co with rfl|rfl|rfl
        · rcases atTri with e|e|e
          · exact xa e
          · exact xb.ne e
          · exact xc e
        · exact atTri.elim un.2.1 (fun e=>e.elim un.2.2.1 un.2.2.2)
        · exact atTri.elim vn.2.1 (fun e=>e.elim vn.2.2.1 vn.2.2.2)
      have out := add_closed part tr sep
      have eq : ({x,u,v}:Finset V)∪{a,b,c}=({x,a,b,c}∪{u,v}) := by
        ext z
        simp only [mem_insert,mem_singleton,mem_union]
        tauto
      exact eq ▸ out
    · have ue : G.Adj a u := same.symm ▸ ae
      have part := tri_path ue adj vn.2.1.symm
      have tr := tri_path xb bc xc
      have sep : Disjoint ({a,u,v}:Finset V) ({x,b,c}:Finset V) := by
        apply disjoint_left.mpr
        intro z co atTri
        simp only [mem_insert,mem_singleton] at co atTri
        rcases co with rfl|rfl|rfl
        · exact atTri.elim xa.symm (fun e=>e.elim ab.ne ac.ne)
        · exact atTri.elim un.1 (fun e=>e.elim un.2.2.1 un.2.2.2)
        · exact atTri.elim vn.1 (fun e=>e.elim vn.2.2.1 vn.2.2.2)
      have out := add_closed part tr sep
      have eq : ({a,u,v}:Finset V)∪{x,b,c}=({x,a,b,c}∪{u,v}) := by
        ext z
        simp only [mem_insert,mem_singleton,mem_union]
        tauto
      exact eq ▸ out
  have centered {u v : V} (uT : u∈T) (vT : v∈T)
      (ux : u≠x) (vx : v≠x) (uv : u≠v)
      (xu : K.Adj x u) (xv : K.Adj x v)
      (shape : T={x,u,v}) : Closed G (C∪{x,a,b,c}) := by
    have uC := other uT ux
    have vC := other vT vx
    have fix {m n : V} (mC : m∈C) (nC : n∈C) (mn : m≠n) (md : m=d) (ne : n=e) :
        Closed G ({x,a,b,c}∪{m,n}) := by
      have m0 : G.Adj x m := md.symm ▸ xd
      have n1 : G.Adj a n := ne.symm ▸ ae
      have mnot := notext mC
      have nnot := notext nC
      have part := tri_path m0.symm xb mnot.2.2.1
      have tr := tri_path n1.symm ac nnot.2.2.2
      have sep : Disjoint ({m,x,b}:Finset V) ({n,a,c}:Finset V) := by
        apply disjoint_left.mpr
        intro z h e
        simp only [mem_insert,mem_singleton] at h e
        rcases h with rfl|rfl|rfl
        · exact e.elim mn (fun e=>e.elim mnot.2.1 mnot.2.2.2)
        · exact e.elim nnot.1.symm (fun e=>e.elim xa xc)
        · exact e.elim nnot.2.2.1.symm (fun e=>e.elim ab.ne.symm bc.ne)
      have out := add_closed part tr sep
      have eq : ({m,x,b}:Finset V)∪{n,a,c}=({x,a,b,c}∪{m,n}) := by
        ext z
        simp only [mem_insert,mem_singleton,mem_union]
        tauto
      exact eq ▸ out
    apply repair uT vT shape
    rcases nbr u uC xu with hd|he <;> rcases nbr v vC xv with dd|ee
    · exact (uv (hd.trans dd.symm)).elim
    · exact fix uC vC uv hd ee
    · have out := fix vC uC uv.symm dd he
      have commute : ({v,u} : Finset V)={u,v} := by
        ext z
        simp only [mem_insert,mem_singleton]
        tauto
      exact (congrArg (fun Q : Finset V=>{x,a,b,c}∪Q) commute) ▸ out
    · exact (uv (he.trans ee.symm)).elim
  have tile := hP.tile T TP
  obtain ⟨u,v,w,uv,uw,vw,e1,e2,shape⟩ := (Kelmans.tile_iff_path K T tile.1).mp tile.2
  have uT : u∈T := by simp [shape]
  have vT : v∈T := by simp [shape]
  have wT : w∈T := by simp [shape]
  change x∈T at xT
  simp only [shape,mem_insert,mem_singleton] at xT
  rcases xT with rfl|rfl|rfl
  · exact leaf vT wT uv.symm uw.symm e2 e1 shape
  · apply centered uT wT uv vw.symm uw e1.symm e2
    rw [shape]
    ext z
    simp only [mem_insert,mem_singleton]
    tauto
  · apply leaf vT uT vw uw e1.symm e2.symm
    · rw [shape]
      ext z
      simp only [mem_insert,mem_singleton]
      tauto

#print axioms triangle_and_singleton_absorb_cap
end
end KelmansCactus.AtomicBridge
