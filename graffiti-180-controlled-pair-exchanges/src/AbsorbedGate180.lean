import GateBound180
set_option warningAsError true
namespace Minimal180.Controlled
open Finset SimpleGraph Graffiti177 Rooted180 Converse180 Assembly180
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A component can absorb old leaves whose exits all return to the enlarged
region or its gate. Deleting the gate then forces a direct contact from H
to a useful old leaf outside the enlarged region. -/
theorem contact_after_absorption (J : SimpleGraph V) (C Z H F : Finset V) (x y z : V)
    (tip : NeedsTip J C (univ\C) x y) (zs : Z⊆(univ\C).erase y)
    (nc : NoCut (J⊔SimpleGraph.edge x y)) (remoteH : H∈remote J ((univ\C)\Z) y)
    (zz : z∈Z) (gate : ∀ i∈H,∀ j∈Z,J.Adj i j → j=z)
    (fc : F⊆C.erase x) (sealed : ∀ i∈F,∀ j,J.Adj i j → j∈H∪F ∨ j=z)
    (useful : ∀ b∈C.erase x,b∉F → Dominates J H b → J.Adj x b) :
    ∃ b∈C.erase x,J.Adj x b ∧ Dominates J H b := by
  classical
  let R := (univ\C)\Z
  let G := J⊔SimpleGraph.edge x y
  obtain ⟨different,hm⟩ := mem_erase.mp remoteH
  obtain ⟨a,ar,eq⟩ := mem_image.mp hm
  have mem {i:V} : i∈H ↔ i∈R ∧ (within J R).Reachable a i := by rw [←eq,mem_part]
  have yh : y∉H := fun h => different (eq.symm.trans (part_eq_of_reach J R (mem.mp h).2))
  have yc : y∉C := (mem_sdiff.mp tip.2.1).2
  have zc : z∉C := (mem_sdiff.mp (mem_of_mem_erase (zs zz))).2
  have zh : z∉H := fun h => (mem_sdiff.mp (mem.mp h).1).2 zz
  have outside (v : V) (nh:v∉H) (nC:v∉C) : v∉H∪F := by
    intro h
    rcases mem_union.mp h with h|h
    · exact nh h
    · exact nC (mem_of_mem_erase (fc h))
  have zy := (mem_erase.mp (zs zz)).1
  obtain ⟨i,inside,j,out,jz,edge⟩ := escape_gate G nc (H∪F) a z y
    (mem_union_left _ (mem.mpr ⟨ar,.refl _⟩)) (outside z zh zc) (outside y yh yc) zy.symm
  have old {i j : V} (ix : i≠x) (iy : i≠y) (e : G.Adj i j) : J.Adj i j := by
    rcases e with e|e
    · exact e
    · rcases ((edge_adj ..).mp e).1 with h|h
      · exact (ix h.1).elim
      · exact (iy h.1).elim
  rcases mem_union.mp inside with ih|ifr
  · obtain ⟨ir,reach⟩ := mem.mp ih
    have ix : i≠x := fun e => (mem_sdiff.mp (mem_sdiff.mp ir).1).2 (e ▸ tip.1)
    have ij := old ix (fun e => yh (e ▸ ih)) edge
    have jx : j≠x := fun e => tip.2.2.2.1 ⟨i,(mem_sdiff.mp ir).1,e ▸ ij.symm⟩
    have jc : j∈C := by
      by_contra nC
      have nz : j∉Z := fun h => jz (gate i ih j h ij)
      have jr : j∈R := mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_univ _,nC⟩,nz⟩
      have e : (within J R).Adj i j := ⟨ij,ir,jr⟩
      exact out (mem_union_left _ (mem.mpr ⟨jr,reach.trans e.reachable⟩))
    have cb := mem_erase.mpr ⟨jx,jc⟩
    have contact : Dominates J H j := ⟨i,ih,ij.symm⟩
    exact ⟨j,cb,useful j cb (fun h => out (mem_union_right _ h)) contact,contact⟩
  · obtain ⟨ix,ic⟩ := mem_erase.mp (fc ifr)
    have ij := old ix (fun e => yc (e ▸ ic)) edge
    exact ((sealed i ifr j ij).elim out jz).elim

/-- The cardinality and actual leaf set are retained. If the number of
remote components is smaller than the number of releases, this supplies
a first-form certificate with exactly one unit of improvement. -/
theorem controlled_of_absorbed_gates (J : SimpleGraph V) (hc : J.Connected) (hn : 2<Fintype.card V)
    (x y w : V) (xy : x≠y) (old : ¬J.Adj x y) (xw : J.Adj x w) (wy : J.Adj w y)
    (U C Z : Finset V) (cu : C⊆U) (count : C.card=weightedLeaves J U+1)
    (tip : NeedsTip J C (univ\C) x y) (zs : Z⊆(U\C).erase y)
    (nc : NoCut (J⊔SimpleGraph.edge x y)) (empty : demand J ((univ\C)\Z) C Z x=∅)
    (regions : ∀ H∈remote J ((univ\C)\Z) y,∃ z∈Z,∃ F⊆C.erase x,
      (∀ i∈H,∀ j∈Z,J.Adj i j → j=z) ∧ (∀ i∈F,∀ j,J.Adj i j → j∈H∪F ∨ j=z) ∧
      (∀ b∈C.erase x,b∉F → Dominates J H b → J.Adj x b)) :
    ∃ B⊆C.erase x, B.card≤(remote J ((univ\C)\Z) y).card ∧ Z.card≤B.card+1 ∧
      (B.card<Z.card → FirstForm J U x y w) ∧
      let L := (C.erase x\B)∪Z
      Con (J⊔SimpleGraph.edge x y) (univ\L) ∧ ∀ q∈L,Dominates (J⊔SimpleGraph.edge x y) (univ\L) q := by
  classical
  let R := (univ\C)\Z
  let K := remote J R y
  have zs' : Z⊆(univ\C).erase y := by
    intro t h
    obtain ⟨ty,tc⟩ := mem_erase.mp (zs h)
    exact mem_erase.mpr ⟨ty,mem_sdiff.mpr ⟨mem_univ _,(mem_sdiff.mp tc).2⟩⟩
  have contact (H : Finset V) (h : H∈K) : ∃ b∈C.erase x,J.Adj x b ∧ Dominates J H b := by
    obtain ⟨z,zz,F,fc,gate,sealed,useful⟩ := regions H h
    exact contact_after_absorption J C Z H F x y z tip zs' nc h zz gate fc sealed useful
  let f (H : Finset V) := if h : H∈K then (contact H h).choose else x
  have hf (H : Finset V) (h : H∈K) : f H∈C.erase x ∧ J.Adj x (f H) ∧ Dominates J H (f H) := by
    simpa only [f,dif_pos h] using (contact H h).choose_spec
  let B := K.image f
  have good (b:V) (h:b∈B) : b∈C.erase x ∧ J.Adj x b := by
    obtain ⟨H,hH,eq⟩ := mem_image.mp h
    rw [←eq]
    exact ⟨(hf H hH).1,(hf H hH).2.1⟩
  have bc : B⊆C.erase x := fun _ h => (good _ h).1
  have links (b:V) (h:b∈B) : J.Adj x b := (good b h).2
  have join (H:Finset V) (h:H∈K) : ∃ b∈B,Dominates J H b :=
    ⟨f H,mem_image_of_mem f h,(hf H h).2.2⟩
  have serve (q:V) (h:q∈demand J R C Z x) : q∈B ∨ Dominates J B q := by
    have absent : q∉(∅:Finset V) := by simp
    exact False.elim (absent (empty ▸ h))
  exact ⟨B,bc,card_image_le,release_bound J hc hn x y w xy old xw wy U C B Z cu count tip bc zs links join serve,
    fun gain => first_of_return_set J hc hn x y w xy old xw wy U C B Z cu count tip bc zs gain links join serve,
    return_certificate J C B Z x y xy tip bc zs' links join serve⟩

#print axioms contact_after_absorption
#print axioms controlled_of_absorbed_gates
end Minimal180.Controlled
