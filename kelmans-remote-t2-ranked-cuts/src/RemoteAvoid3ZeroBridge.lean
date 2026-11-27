import RemoteFourCutAttachment
import RemoteFourCutTransport
import RemoteT2CompletionClassify
import RemoteAvoid3ZeroFromTester
import RemoteT2ZeroShore
import FourRingCutAux

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteAvoid3ZeroBridge
open SquareCap (FactorOn boundary SmallTrivial attach factor_map)
open RemoteT2CompletionTransfer (eraseEdge marked SmallerIsolatedAvoid3)
open RemoteFourCutAttachment (Side sideGraph true_shore_attachment)
open RemoteFourCutTransport (transfer_degree transfer_small)
open RemoteT2FourCutMatching (ColorThree)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
private theorem side_order_lower (c : V→Bool) (q : Bool) (h : ColorThree c q) :
    1<Fintype.card (Side c q) := by
  classical
  obtain ⟨a,b,_,ab,_,_,ha,hb,_⟩ := h
  let x : Side c q := ⟨a,ha⟩
  let y : Side c q := ⟨b,hb⟩
  have ne : x≠y := fun eq=>ab (congrArg Subtype.val eq)
  have card := card_le_univ (s:=({x,y}:Finset (Side c q)))
  simpa [ne] using card

/-- Factor both actual width-four shores internally by strictly smaller
six-vertex testers. No surviving seam wire is needed. -/
theorem zero_factor_of_two_four_cuts (small : SmallTrivial G) (cub : ∀ v,G.degree v=3)
    (cL cR : V→Bool)
    (lt : ColorThree cL true) (lf : ColorThree cL false)
    (rt : ColorThree cR true) (rf : ColorThree cR false)
    (wl : (boundary G cL).card=4) (wr : (boundary G cR).card=4)
    (lres : Fintype.card (Side cL true)%6=0) (rres : Fintype.card (Side cR true)%6=0)
    {x y u v : V} (xy : x≠y)
    (partition : ∀ z : V,z≠x∧z≠y ↔ cL z=true∨cR z=true)
    (separate : ∀ z : V,¬(cL z=true∧cR z=true))
    (uL : cL u=true) (vR : cR v=true)
    (avo : SmallerIsolatedAvoid3.{u} (Fintype.card V)) :
    FactorOn (eraseEdge G u v) ((univ.erase x).erase y) := by
  classical
  obtain ⟨pL,rL,_,isoL,_,_⟩ := true_shore_attachment G cL small cub lt lf wl
  obtain ⟨pR,rR,_,isoR,_,_⟩ := true_shore_attachment G cR small cub rt rf wr
  let L := Side cL true
  let R := Side cR true
  let GL := sideGraph G cL true
  let GR := sideGraph G cR true
  let J : L⊕R ↪ V := ⟨Sum.elim Subtype.val Subtype.val,by
    rintro (a|a) (b|b) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · have eq : a.val=b.val := h
      exact (separate b.val ⟨eq ▸ a.property,b.property⟩).elim
    · have eq : a.val=b.val := h
      exact (separate b.val ⟨b.property,eq ▸ a.property⟩).elim
    · exact congrArg Sum.inr (Subtype.ext h)⟩
  let X := (eraseEdge G u v).comap J
  have ud : cR u=false := Bool.eq_false_iff.mpr (fun t=>separate u ⟨uL,t⟩)
  have vd : cL v=false := Bool.eq_false_iff.mpr (fun t=>separate v ⟨t,vR⟩)
  have lg (a b : L) (h : GL.Adj a b) : X.Adj (Sum.inl a) (Sum.inl b) := by
    change G.Adj a.val b.val ∧ ¬marked u v a.val b.val
    refine ⟨h,?_⟩
    rintro (⟨_,m⟩|⟨m,_⟩)
    · exact (by decide : false≠true) (vd.symm.trans (m ▸ b.property))
    · exact (by decide : false≠true) (vd.symm.trans (m ▸ a.property))
  have rg (a b : R) (h : GR.Adj a b) : X.Adj (Sum.inr a) (Sum.inr b) := by
    change G.Adj a.val b.val ∧ ¬marked u v a.val b.val
    refine ⟨h,?_⟩
    rintro (⟨m,_⟩|⟨_,m⟩)
    · exact (by decide : false≠true) (ud.symm.trans (m ▸ a.property))
    · exact (by decide : false≠true) (ud.symm.trans (m ▸ b.property))
  have cover : (univ : Finset (L⊕R)).map J=(univ.erase x).erase y := by
    ext z
    constructor
    · intro hz
      obtain ⟨a,_,e⟩ := mem_map.mp hz
      have hz' : z≠x∧z≠y := (partition z).mpr (by
        cases a with
        | inl a =>
          change a.val=z at e
          exact Or.inl (e ▸ a.property)
        | inr a =>
          change a.val=z at e
          exact Or.inr (e ▸ a.property))
      exact mem_erase.mpr ⟨hz'.2,mem_erase.mpr ⟨hz'.1,mem_univ _⟩⟩
    · intro hz
      obtain ⟨hy,hm⟩ := mem_erase.mp hz
      obtain ⟨hx,_⟩ := mem_erase.mp hm
      rcases (partition z).mp ⟨hx,hy⟩ with c|c
      · exact mem_map.mpr ⟨Sum.inl ⟨z,c⟩,mem_univ _,rfl⟩
      · exact mem_map.mpr ⟨Sum.inr ⟨z,c⟩,mem_univ _,rfl⟩
  have budget : Fintype.card L+Fintype.card R+2≤Fintype.card V := by
    have large : 2≤Fintype.card V := by
      have lb := card_le_univ (s:=({x,y}:Finset V))
      simpa [xy] using lb
    have h := congrArg Finset.card cover
    rw [card_map,card_univ,Fintype.card_sum,
      card_erase_of_mem (mem_erase.mpr ⟨xy.symm,mem_univ _⟩),
      card_erase_of_mem (mem_univ _),card_univ] at h
    omega
  have cL' (z : L⊕Side cL false) :
      (attach GL (sideGraph G cL false) pL rL).degree z=3 :=
    (transfer_degree isoL z).trans (cub (isoL z))
  have cR' (z : R⊕Side cR false) :
      (attach GR (sideGraph G cR false) pR rR).degree z=3 :=
    (transfer_degree isoR z).trans (cub (isoR z))
  have lpos : 1<Fintype.card L := side_order_lower cL true lt
  have rpos : 1<Fintype.card R := side_order_lower cR true rt
  have lr : Fintype.card L%6=0 := lres
  have rr : Fintype.card R%6=0 := rres
  have lbl : 6≤Fintype.card L := by omega
  have lbr : 6≤Fintype.card R := by omega
  have ll : 4<Fintype.card L := by omega
  have rl : 4<Fintype.card R := by omega
  have gl : Fintype.card L+6<Fintype.card V := by omega
  have gr : Fintype.card R+6<Fintype.card V := by omega
  have left := RemoteAvoid3ZeroFromTester.zero_factor_from_attachment pL rL (transfer_small isoL small)
    cL' ll (side_order_lower cL false lf) lr (Fintype.card V) gl avo
  have right := RemoteAvoid3ZeroFromTester.zero_factor_from_attachment pR rR (transfer_small isoR small)
    cR' rl (side_order_lower cR false rf) rr (Fintype.card V) gr avo
  have fact := RemoteT2ZeroShore.factor_two_shores lg rg left right
  have lifted := factor_map (G:=X) (H:=eraseEdge G u v) J (fun _ _ h=>h) fact
  rwa [cover] at lifted



section Natural
open RemoteT2PairCounts (extend innerCut extended_boundary outside_cut_balance OutsideTwo mismatch)
open RemoteT2CompletionClassify (OutsideThree)

omit [Fintype V] [DecidableRel G.Adj] in
private theorem three_converted (c : V→Bool) {x y : V} {b : Bool}
    (h : OutsideThree c x y b) (s t : Bool) :
    ColorThree (extend c x y s t) b := by
  obtain ⟨a,d,e,ax,ay,dx,dy,ex,ey,ad,ae,de,ha,hd,he⟩ := h
  exact ⟨a,d,e,ad,ae,de,by simp [extend,ax,ay,ha],by simp [extend,dx,dy,hd],by simp [extend,ex,ey,he]⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem three_flipped (c : V→Bool) {b : Bool} (h : ColorThree c b) :
    ColorThree (fun z=> !(c z)) (!b) := by
  obtain ⟨a,d,e,ad,ae,de,ha,hd,he⟩ := h
  exact ⟨a,d,e,ad,ae,de,by simp [ha],by simp [hd],by simp [he]⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem three_to_two (c : V→Bool) {x y : V} {b : Bool}
    (h : OutsideThree c x y b) : OutsideTwo c x y b := by
  obtain ⟨a,d,e,ax,ay,dx,dy,ex,ey,ad,ae,de,ha,hd,he⟩ := h
  exact ⟨a,d,ax,ay,dx,dy,ad,ha,hd⟩

/-- The actual zero-zero residual cut has a factor from strictly
smaller isolated-pattern three-edge avoidance alone. -/
theorem balanced_zero_remote_factor
    (small : SmallTrivial G) (cub : ∀ v,G.degree v=3)
    {x y u v : V} (xy : G.Adj x y)
    (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y)
    (c : V→Bool) (cp : OutsideThree c x y true) (cn : OutsideThree c x y false)
    (cu : c u=true) (cv : c v=false) (C : (innerCut G c x y).card=2)
    (lres : Fintype.card (Side (extend c x y false false) true)%6=0)
    (rres : Fintype.card (Side (fun z=> !(extend c x y true true z)) true)%6=0)
    (smaller : SmallerIsolatedAvoid3.{u} (Fintype.card V)) :
    FactorOn (eraseEdge G u v) ((univ.erase x).erase y) := by
  classical
  let P := extend c x y false false
  let N := fun z=> !(extend c x y true true z)
  have pos := three_to_two c cp
  have neg := three_to_two c cn
  obtain ⟨xf,xt,yf,yt⟩ := (outside_cut_balance G small c xy (cub x) (cub y) pos neg).2 C
  have pWidth : (boundary G P).card=4 := by
    rw [extended_boundary G c xy,C,xf,yf]
    decide
  have nWidth : (boundary G N).card=4 := by
    have flip := FourRingCutAux.boundary_flip_card G (extend c x y true true)
    change (boundary G N).card=(boundary G (extend c x y true true)).card at flip
    rw [flip,extended_boundary G c xy,C,xt,yt]
    decide
  have part (z : V) : z≠x∧z≠y ↔ P z=true∨N z=true := by
    by_cases zx : z=x
    · subst z
      simp [P,N,extend]
    · by_cases zy : z=y
      · subst z
        simp [P,N,extend,xy.ne.symm]
      · cases cz : c z <;> simp [P,N,extend,zx,zy,cz]
  have sep (z : V) : ¬(P z=true∧N z=true) := by
    by_cases zx : z=x
    · subst z
      simp [P,N,extend]
    · by_cases zy : z=y
      · subst z
        simp [P,N,extend,xy.ne.symm]
      · cases cz : c z <;> simp [P,N,extend,zx,zy,cz]
  have leftU : P u=true := by simp [P,extend,ux,uy,cu]
  have rightV : N v=true := by simp [N,extend,vx,vy,cv]
  exact zero_factor_of_two_four_cuts G small cub P N
    (three_converted c cp _ _) (three_converted c cn _ _)
    (three_flipped (extend c x y true true) (three_converted c cn _ _))
    (three_flipped (extend c x y true true) (three_converted c cp _ _))
    pWidth nWidth lres rres xy.ne part sep leftU rightV smaller


#print axioms balanced_zero_remote_factor
#print axioms zero_factor_of_two_four_cuts
end Natural
end KelmansCactus.AtomicBridge.RemoteAvoid3ZeroBridge
