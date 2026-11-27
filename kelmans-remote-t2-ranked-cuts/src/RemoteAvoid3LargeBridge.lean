import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import RemoteAvoid3RankedBridge
import RemoteAvoid3RankTransfer
import RemoteRankOrdinaryT2
import RemoteT2TinyShoreChain

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteAvoid3LargeBridge
open SquareCap (SmallTrivial FactorOn boundary attach cap)
open RemoteT2CompletionTransfer (eraseEdge marked SmallerIsolatedAvoid3)
open RemoteFourCutAttachment (Side sideGraph true_shore_attachment)
open RemoteFourCutTransport (transfer_degree transfer_small)
open RemoteT2FourCutMatching (ColorThree)
open RemoteT2PairCounts (extend innerCut extended_boundary outside_cut_balance OutsideTwo)
open RemoteT2CompletionClassify (OutsideThree)
open RemoteT2TinyShoreChain (outside mem_outside)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem deletion_symm (a b : V) : eraseEdge G a b=eraseEdge G b a := by
  ext x y
  change (G.Adj x y∧¬marked a b x y) ↔ G.Adj x y∧¬marked b a x y
  simp [marked,or_comm]

omit [DecidableRel G.Adj] in
private theorem flip_inner (c : V→Bool) (x y : V) :
    (innerCut G (fun z=> !(c z)) x y).card=(innerCut G c x y).card := by
  classical
  have eq : innerCut G (fun z=> !(c z)) x y=(innerCut G c x y).image Prod.swap := by
    ext ⟨u,v⟩
    constructor
    · intro h
      have mem : (v,u)∈innerCut G c x y := by
        simp only [innerCut,boundary,mem_filter,mem_univ,true_and] at h ⊢
        obtain ⟨⟨hc,hd,e⟩,ux,uy,vx,vy⟩ := h
        have f : c u=false := by cases k : c u <;> simp_all
        have t : c v=true := by cases k : c v <;> simp_all
        exact ⟨⟨t,f,e.symm⟩,vx,vy,ux,uy⟩
      exact mem_image.mpr ⟨(v,u),mem,rfl⟩
    · intro h
      obtain ⟨⟨a,b⟩,m,e⟩ := mem_image.mp h
      have h' : (b,a)=(u,v) := e
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj h'
      simp only [innerCut,boundary,mem_filter,mem_univ,true_and] at m ⊢
      obtain ⟨⟨ac,bc,ab⟩,ax,ay,bx,by'⟩ := m
      exact ⟨⟨by simp [bc],by simp [ac],ab.symm⟩,bx,by',ax,ay⟩
  rw [eq,card_image_of_injective _ Prod.swap_injective]

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

private theorem even_shore (small : SmallTrivial G) (cub : ∀ v,G.degree v=3)
    (c : V→Bool) (t : ColorThree c true) (f : ColorThree c false) (cut : (boundary G c).card=4) :
    Fintype.card (Side c true)%2=0 := by
  classical
  obtain ⟨p,r,_,E,_,_⟩ := true_shore_attachment G c small cub t f cut
  let L := Side c true
  let R := Side c false
  let H := sideGraph G c true
  let J := sideGraph G c false
  have cA (a : L⊕R) : (attach H J p r).degree a=3 := (transfer_degree E a).trans (cub (E a))
  have sA : SmallTrivial (attach H J p r) := transfer_small E small
  have nL := Fintype.card_le_of_injective p p.injective
  have four : Fintype.card SquareCap.Port=4 := by simp [SquareCap.Port]
  rw [four] at nL
  by_cases l4 : Fintype.card (Side c true)=4
  · simp [l4]
  · have large : 4<Fintype.card L := by
      change 4<Fintype.card (Side c true)
      omega
    have out : 1<Fintype.card R := by
      obtain ⟨a,b,_,ab,_,_,ha,hb,_⟩ := f
      let A : R := ⟨a,ha⟩
      let B : R := ⟨b,hb⟩
      have ne : A≠B := fun e=>ab (congrArg Subtype.val e)
      have size := card_le_univ (s:=({A,B}:Finset R))
      simpa [ne] using size
    obtain ⟨k,_,_⟩ := SquareCap.cubic_good_cap out large cA sA
    let C := cap H p k
    have cc : ∀ a,C.degree a=3 := SquareCap.cap_cubic (fun v=>cA (Sum.inl v)) k
    have count := C.sum_degrees_eq_twice_card_edges
    simp [cc,Finset.card_univ] at count
    omega

open RemoteAvoid3RankedBridge (ShoreRankMode ranked_factor_of_balanced_cut)
open RemoteAvoid3RankTransfer (SmallerRemoteT2 smaller_avoid3_of_remote)


/-- An actual nontrivial bridge with both shores larger than four
cannot occur in a smallest-order Remote T2 failure. The only
packing premise is Remote T2 on strictly smaller inputs.
The original marked edge need not itself be remote. -/
theorem large_balanced_bridge_from_smaller_remote
    (small : SmallTrivial G) (big : 5≤Fintype.card V) (cub : ∀ v,G.degree v=3)
    (modG : Fintype.card V%6=2) {x y u v : V} (xy : G.Adj x y) (uv : G.Adj u v)
    (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y)
    (c : V→Bool) (cu : c u=true) (cv : c v=false) (C : (innerCut G c x y).card=2)
    (ll : 4<((outside x y).filter (fun z=>c z=true)).card)
    (rr : 4<((outside x y).filter (fun z=>c z=false)).card)
    (prev : SmallerRemoteT2.{u} (Fintype.card V)) :
    FactorOn (eraseEdge G u v) (outside x y) := by
  classical
  let P := extend c x y false false
  let N := fun z=> !(extend c x y true true z)
  let d := fun z=> !(c z)
  let rank := Fintype.card V-2
  have coverRank : rank+2=Fintype.card V := by dsimp [rank]; omega
  have prev' : SmallerRemoteT2.{u} (rank+2) := coverRank.symm ▸ prev
  have avoid := smaller_avoid3_of_remote rank prev'
  have ordinary := RemoteRankOrdinaryT2.smaller_t2_of_remote _ prev
  have PE (z : V) : P z=true↔z≠x∧z≠y∧c z=true := membershipP c x y z
  have NE (z : V) : N z=true↔z≠x∧z≠y∧c z=false := membershipN c x y z
  have ep : extend d x y false false=N := by
    funext z
    by_cases a : z=x
    · simp [extend,a,N]
    · by_cases b : z=y
      · simp [extend,a,b,N]
      · simp [extend,a,b,N,d]
  have en : (fun z=> !(extend d x y true true z))=P := by
    funext z
    by_cases a : z=x
    · simp [extend,a,P]
    · by_cases b : z=y
      · simp [extend,a,b,P]
      · simp [extend,a,b,P,d]
  have formP : Fintype.card (Side P true) = ((outside x y).filter (fun z=>c z=true)).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext z
    simp [mem_filter,mem_outside,PE,and_assoc]
  have formN : Fintype.card (Side N true) = ((outside x y).filter (fun z=>c z=false)).card := by
    rw [Fintype.card_subtype]
    congr 1
    ext z
    simp [mem_filter,mem_outside,NE,and_assoc]
  have size : Fintype.card (Side P true)+Fintype.card (Side N true)=rank := by
    let A := (outside x y).filter (fun z=>c z=true)
    let B := (outside x y).filter (fun z=>c z=false)
    have disj : Disjoint A B := by
      apply disjoint_left.mpr
      intro z a b
      exact (by decide : true≠false) (((mem_filter.mp a).2).symm.trans (mem_filter.mp b).2)
    have cv' : A∪B=outside x y := by
      ext z
      cases h : c z <;> simp [A,B,h]
    have sum : A.card+B.card=(outside x y).card := (card_union_of_disjoint disj).symm.trans (congrArg Finset.card cv')
    have sz : (outside x y).card=rank := by
      unfold outside
      rw [card_erase_of_mem (mem_erase.mpr ⟨xy.ne.symm,mem_univ _⟩),
        card_erase_of_mem (mem_univ _),card_univ]
      dsimp [rank]
      omega
    exact (congrArg₂ Nat.add formP formN).trans (sum.trans sz)
  have bigL : 4<Fintype.card (Side P true) := formP.symm ▸ ll
  have bigR : 4<Fintype.card (Side N true) := formN.symm ▸ rr
  have ap : 3≤Fintype.card (Side P true) := by omega
  have bn : 3≤Fintype.card (Side N true) := by omega
  have hp := count_three P true ap
  have hn := count_three N true bn
  have toOutside {e : V→Bool} {b : Bool} (h : ColorThree e true)
      (convert : ∀ z : V,e z=true↔z≠x∧z≠y∧c z=b) : OutsideThree c x y b := by
    obtain ⟨a,b',r,ab,ar,br,ha,hb,hr⟩ := h
    obtain ⟨ax,ay,ac⟩ := (convert a).mp ha
    obtain ⟨bx,by',bc⟩ := (convert b').mp hb
    obtain ⟨rx,ry,rc⟩ := (convert r).mp hr
    exact ⟨a,b',r,ax,ay,bx,by',rx,ry,ab,ar,br,ac,bc,rc⟩
  have pt := toOutside hp PE
  have nt := toOutside hn NE
  have two {b : Bool} (h : OutsideThree c x y b) : OutsideTwo c x y b := by
    obtain ⟨a,d,e,ax,ay,dx,dy,ex,ey,ad,ae,de,ha,hd,he⟩ := h
    exact ⟨a,d,ax,ay,dx,dy,ad,ha,hd⟩
  have hfP : ColorThree P false := by
    refine ⟨x,y,v,xy.ne,vx.symm,vy.symm,?_,?_,?_⟩
    · simp [P,extend]
    · simp [P,extend,xy.ne.symm]
    · simp [P,extend,vx,vy,cv]
  have hfN : ColorThree N false := by
    refine ⟨x,y,u,xy.ne,ux.symm,uy.symm,?_,?_,?_⟩
    · simp [N,extend]
    · simp [N,extend,xy.ne.symm]
    · simp [N,extend,ux,uy,cu]
  obtain ⟨xf,xt,yf,yt⟩ := (outside_cut_balance G small c xy (cub x) (cub y) (two pt) (two nt)).2 C
  have pc : (boundary G P).card=4 := by
    rw [extended_boundary G c xy,C,xf,yf]
    decide
  have nc : (boundary G N).card=4 := by
    have e := FourRingCutAux.boundary_flip_card G (extend c x y true true)
    change (boundary G N).card=(boundary G (extend c x y true true)).card at e
    rw [e,extended_boundary G c xy,C,xt,yt]
    decide
  have eP := even_shore G small cub P hp hfP pc
  have eN := even_shore G small cub N hn hfN nc
  have casesR : (Fintype.card (Side P true)%6=0 ∧ Fintype.card (Side N true)%6=0) ∨
      (Fintype.card (Side P true)%6=4 ∧ Fintype.card (Side N true)%6=2) ∨
      (Fintype.card (Side P true)%6=2 ∧ Fintype.card (Side N true)%6=4) := by omega
  rcases casesR with ⟨l,r⟩|⟨l,r⟩|⟨l,r⟩
  · have mode : ShoreRankMode (Fintype.card (Side P true)) (Fintype.card (Side N true)) rank :=
      Or.inl ⟨l,r⟩
    exact ranked_factor_of_balanced_cut G small cub xy uv ux uy vx vy c pt nt cu cv C rank mode avoid ordinary
  · have mode : ShoreRankMode (Fintype.card (Side P true)) (Fintype.card (Side N true)) rank :=
      Or.inr ⟨l,r,by omega,by omega⟩
    exact ranked_factor_of_balanced_cut G small cub xy uv ux uy vx vy c pt nt cu cv C rank mode avoid ordinary
  · rw [deletion_symm G u v]
    have pt' : OutsideThree d x y true := by
      obtain ⟨a,b,e,ax,ay,bx,by',ex,ey,ab,ae,be,ha,hb,he⟩ := nt
      exact ⟨a,b,e,ax,ay,bx,by',ex,ey,ab,ae,be,by simp [d,ha],by simp [d,hb],by simp [d,he]⟩
    have nt' : OutsideThree d x y false := by
      obtain ⟨a,b,e,ax,ay,bx,by',ex,ey,ab,ae,be,ha,hb,he⟩ := pt
      exact ⟨a,b,e,ax,ay,bx,by',ex,ey,ab,ae,be,by simp [d,ha],by simp [d,hb],by simp [d,he]⟩
    have mode : ShoreRankMode (Fintype.card (Side N true)) (Fintype.card (Side P true)) rank :=
      Or.inr ⟨r,l,by omega,by omega⟩
    have et := congrArg (fun f : V→Bool=>Fintype.card (Side f true)) ep
    have ef := congrArg (fun f : V→Bool=>Fintype.card (Side f true)) en
    have m2 := (congrArg₂ (fun a b=>ShoreRankMode a b rank) et ef).mpr mode
    have fut : d v=true := by simp [d,cv]
    have fuf : d u=false := by simp [d,cu]
    exact ranked_factor_of_balanced_cut G small cub xy uv.symm vx vy ux uy d pt' nt' fut fuf
      ((flip_inner G c x y).trans C) rank m2 avoid ordinary

/-- In a counterexample with a verified smaller-order Remote T2 premise,
every nontrivial bridge shore pair has a shore of at most four vertices. -/
theorem minimal_remote_bridge_shore_small
    (small : SmallTrivial G) (big : 5≤Fintype.card V) (cub : ∀ v,G.degree v=3)
    (modG : Fintype.card V%6=2) {x y u v : V} (xy : G.Adj x y) (uv : G.Adj u v)
    (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y)
    (c : V→Bool) (cu : c u=true) (cv : c v=false) (C : (innerCut G c x y).card=2)
    (prev : SmallerRemoteT2.{u} (Fintype.card V))
    (bad : ¬FactorOn (eraseEdge G u v) (outside x y)) :
    ((outside x y).filter (fun z=>c z=true)).card≤4 ∨
      ((outside x y).filter (fun z=>c z=false)).card≤4 := by
  by_contra! h
  exact bad (large_balanced_bridge_from_smaller_remote G small big cub modG xy uv ux uy vx vy
    c cu cv C h.1 h.2 prev)

#print axioms large_balanced_bridge_from_smaller_remote
#print axioms minimal_remote_bridge_shore_small
end KelmansCactus.AtomicBridge.RemoteAvoid3LargeBridge
