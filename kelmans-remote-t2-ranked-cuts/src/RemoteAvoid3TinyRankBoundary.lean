import RemoteAvoid3LargeBridge

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteAvoid3TinyRankBoundary
open SquareCap (SmallTrivial FactorOn boundary)
open RemoteT2CompletionTransfer (eraseEdge)
open RemoteAvoid3RankTransfer (SmallerRemoteT2)
open RemoteT2TinyShoreChain (outside mem_outside)
open RemoteFourCutAttachment (Side true_shore_attachment)
open RemoteT2FourCutMatching (ColorThree)
open RemoteT2PairCounts (extend innerCut outside_cut_balance extended_boundary OutsideTwo)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] in
private theorem membershipP (c : V→Bool) (x y z : V) :
    extend c x y false false z=true ↔ z≠x∧z≠y∧c z=true := by
  by_cases a : z=x
  · simp [extend,a]
  · by_cases b : z=y
    · simp [extend,a,b]
    · simp [extend,a,b]

omit [Fintype V] in
private theorem membershipN (c : V→Bool) (x y z : V) :
    (!(extend c x y true true z))=true ↔ z≠x∧z≠y∧c z=false := by
  by_cases a : z=x
  · simp [extend,a]
  · by_cases b : z=y
    · simp [extend,a,b]
    · simp [extend,a,b]

omit [DecidableEq V] in
private theorem count_three (c : V→Bool) (b : Bool) (n : 3≤Fintype.card (Side c b)) :
    ColorThree c b := by
  classical
  let f := (Fintype.equivFin (Side c b)).symm
  let x := f ⟨0,by omega⟩
  let y := f ⟨1,by omega⟩
  let z := f ⟨2,by omega⟩
  refine ⟨x.val,y.val,z.val,?_,?_,?_,x.property,y.property,z.property⟩
  · intro e
    have h : (0:ℕ)=1 := congrArg Fin.val (f.injective (Subtype.ext e : x=y))
    omega
  · intro e
    have h : (0:ℕ)=2 := congrArg Fin.val (f.injective (Subtype.ext e : x=z))
    omega
  · intro e
    have h : (1:ℕ)=2 := congrArg Fin.val (f.injective (Subtype.ext e : y=z))
    omega



/-- Three vertices cannot be a shore of a genuine balanced bridge:
the two removed vertices can be put on the other shore, creating a
width-four cut, whose four original boundary vertices are distinct. -/
theorem no_three_vertex_balanced_shore
    (small : SmallTrivial G) (cub : ∀ z,G.degree z=3)
    {x y : V} (xy : G.Adj x y) (c : V→Bool)
    (p : OutsideTwo c x y true) (n : OutsideTwo c x y false)
    (C : (innerCut G c x y).card=2) :
    ((outside x y).filter (fun z=>c z=true)).card≠3 ∧
    ((outside x y).filter (fun z=>c z=false)).card≠3 := by
  classical
  let P := extend c x y false false
  let N := fun z=> !(extend c x y true true z)
  have sidesP : Fintype.card (Side P true)=((outside x y).filter (fun z=>c z=true)).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext z
    simp [P,mem_filter,mem_outside,membershipP,and_assoc]
  have sidesN : Fintype.card (Side N true)=((outside x y).filter (fun z=>c z=false)).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext z
    simp only [mem_filter,mem_univ,true_and,mem_outside,and_assoc]
    exact membershipN c x y z
  obtain ⟨xf,xt,yf,yt⟩ := (outside_cut_balance G small c xy (cub x) (cub y) p n).2 C
  have pc : (boundary G P).card=4 := by
    rw [extended_boundary G c xy,C,xf,yf]
    decide
  have nc : (boundary G N).card=4 := by
    have e := FourRingCutAux.boundary_flip_card G (extend c x y true true)
    change (boundary G N).card=(boundary G (extend c x y true true)).card at e
    rw [e,extended_boundary G c xy,C,xt,yt]
    decide
  have fP : ColorThree P false := by
    obtain ⟨u,_,ux,uy,_,_,_,uc,_⟩ := n
    refine ⟨x,y,u,xy.ne,ux.symm,uy.symm,?_,?_,?_⟩
    · simp [P,extend]
    · simp [P,extend,xy.ne.symm]
    · simp [P,extend,ux,uy,uc]
  have fN : ColorThree N false := by
    obtain ⟨u,_,ux,uy,_,_,_,uc,_⟩ := p
    refine ⟨x,y,u,xy.ne,ux.symm,uy.symm,?_,?_,?_⟩
    · simp [N,extend]
    · simp [N,extend,xy.ne.symm]
    · simp [N,extend,ux,uy,uc]
  have wing (d : V→Bool) (width : (boundary G d).card=4) (ff : ColorThree d false) :
      Fintype.card (Side d true)≠3 := by
    intro h
    have sz : 3≤Fintype.card (Side d true) := h.symm ▸ (by decide : (3:ℕ)≤3)
    have tt := count_three d true sz
    obtain ⟨port,_,_,_,_,_⟩ := true_shore_attachment G d small cub tt ff width
    have k := Fintype.card_le_of_injective port port.injective
    simp [SquareCap.Port,h] at k
  exact ⟨fun h=>wing P pc fP (sidesP.trans h),fun h=>wing N nc fN (sidesN.trans h)⟩

private theorem two_lower (c : V→Bool) (x y : V) (b : Bool) (h : OutsideTwo c x y b) :
    2≤((outside x y).filter (fun z=>c z=b)).card := by
  classical
  obtain ⟨a,d,ax,ay,dx,dy,ne,ha,hd⟩ := h
  have s : ({a,d}:Finset V)⊆(outside x y).filter (fun z=>c z=b) := by
    intro z m
    simp only [mem_insert,mem_singleton] at m
    rcases m with rfl|rfl
    · exact mem_filter.mpr ⟨mem_outside.mpr ⟨ax,ay⟩,ha⟩
    · exact mem_filter.mpr ⟨mem_outside.mpr ⟨dx,dy⟩,hd⟩
  simpa [ne] using card_le_card s

/-- Exact tiny-rank normal form. Under the same Remote T2 conjecture
on strictly smaller source orders, a counterexample with a genuine
nontrivial bridge must have a surviving shore of size exactly two
or four. This is not a resolution of these tight-order configurations. -/
theorem minimal_remote_bridge_is_two_or_four
    (small : SmallTrivial G) (big : 5≤Fintype.card V) (cub : ∀ v,G.degree v=3)
    (modG : Fintype.card V%6=2) {x y u v : V} (xy : G.Adj x y) (uv : G.Adj u v)
    (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y)
    (c : V→Bool) (cu : c u=true) (cv : c v=false) (C : (innerCut G c x y).card=2)
    (p : OutsideTwo c x y true) (n : OutsideTwo c x y false)
    (prev : SmallerRemoteT2.{u} (Fintype.card V))
    (bad : ¬FactorOn (eraseEdge G u v) (outside x y)) :
    let l := ((outside x y).filter (fun z=>c z=true)).card
    let r := ((outside x y).filter (fun z=>c z=false)).card
    (l=2∨l=4) ∨ (r=2∨r=4) := by
  have low := RemoteAvoid3LargeBridge.minimal_remote_bridge_shore_small G small big cub modG xy uv
    ux uy vx vy c cu cv C prev bad
  have a := two_lower c x y true p
  have b := two_lower c x y false n
  obtain ⟨noL,noR⟩ := no_three_vertex_balanced_shore G small cub xy c p n C
  omega

#print axioms no_three_vertex_balanced_shore
#print axioms minimal_remote_bridge_is_two_or_four
end KelmansCactus.AtomicBridge.RemoteAvoid3TinyRankBoundary
