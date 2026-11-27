import FourRingCutAux
import RemoteFourCutAttachment
import RemoteFourCutTransport
import RemoteAvoid3MixedBridge
import RemoteT2TinyShoreChain

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.RemoteAvoid3TinyBridge
open SquareCap (boundary FactorOn SmallTrivial attach factor_map)
open RemoteT2PairCounts (extend innerCut outside_cut_balance extended_boundary OutsideTwo)
open RemoteT2TinyShoreChain (outside mem_outside tiny_width_two_chain)
open RemoteFourCutAttachment (Side sideGraph true_shore_attachment)
open RemoteFourCutTransport (transfer_degree transfer_small)
open RemoteT2FourCutMatching (ColorThree)
open RemoteT2CompletionTransfer (eraseEdge marked SmallerIsolatedAvoid3)
open RemoteAvoid3PortProfiles (SingleReady)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem three_by_card (c : V→Bool) (b : Bool) (lb : 3≤Fintype.card (Side c b)) :
    ColorThree c b := by
  classical
  let f := (Fintype.equivFin (Side c b)).symm
  let x := f ⟨0,by omega⟩
  let y := f ⟨1,by omega⟩
  let z := f ⟨2,by omega⟩
  refine ⟨x.val,y.val,z.val,?_,?_,?_,x.property,y.property,z.property⟩
  · intro e
    have bad := f.injective (Subtype.ext e : x=y)
    have k : (0:ℕ)=1 := congrArg Fin.val bad
    omega
  · intro e
    have bad := f.injective (Subtype.ext e : x=z)
    have k : (0:ℕ)=2 := congrArg Fin.val bad
    omega
  · intro e
    have bad := f.injective (Subtype.ext e : y=z)
    have k : (1:ℕ)=2 := congrArg Fin.val bad
    omega

/-- Pure factor theorem for the genuine two-vertex shore. The deleted
edge (u,v) crosses a width-two cut after removing x,y; its true
shore consists exactly of u,w. This proof has no remoteness,
explicit port-layout, or extra F2/T2 hypotheses. It only assumes
the same strictly smaller isolated-edge-pattern Avoid3 promise
as the non-tiny mixed-residue bridge case. -/
theorem tiny_remote_factor
    (small : SmallTrivial G) (big : 5≤Fintype.card V) (cub : ∀ z,G.degree z=3)
    (rem : Fintype.card V%6=2)
    {x y u v w : V} (xy : G.Adj x y)
    (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y) (wx : w≠x) (wy : w≠y)
    (uw : u≠w) (uv : G.Adj u v)
    (c : V→Bool) (cu : c u=true) (cv : c v=false) (cw : c w=true)
    (precise : ∀ z : V,z≠x → z≠y → (c z=true ↔ z=u∨z=w))
    (cut : (innerCut G c x y).card=2)
    (avo : SmallerIsolatedAvoid3.{u} (Fintype.card V)) :
    FactorOn (eraseEdge G u v) (outside x y) := by
  classical
  obtain ⟨q,qx,qy,cq,_,wq,_,_,iffFactor⟩ :=
    tiny_width_two_chain G small big cub xy ux uy vx vy wx wy uw uv c cu cv cw precise cut
  let B := fun z=> !(extend c x y true true z)
  have b_eq (z : V) : B z=true ↔ z≠x∧z≠y∧c z=false := by
    by_cases zx : z=x
    · simp [B,extend,zx]
    · by_cases zy : z=y
      · simp [B,extend,zx,zy]
      · cases hz : c z <;> simp [B,extend,zx,zy,hz]
  have notB (z : V) : ¬(B z=true) ↔ z=x∨z=y∨z=u∨z=w := by
    by_cases zx : z=x
    · simp [zx,B,extend]
    · by_cases zy : z=y
      · simp [zx,zy,B,extend,xy.ne.symm]
      · rw [b_eq]
        simp only [zx,zy,ne_eq,not_false_eq_true,true_and,false_or]
        cases hz : c z
        · have n : ¬(z=u∨z=w) := by
            intro o
            have h := (precise z zx zy).mpr o
            rw [hz] at h
            cases h
          simp [hz,n]
        · simp [hz,(precise z zx zy).mp hz]
  let D : Finset V := {x,y,u,w}
  let F : Finset V := univ.filter (fun z=>B z=true)
  have cardD : D.card=4 := by simp [D,xy.ne,ux.symm,uy.symm,wx.symm,wy.symm,uw]
  have disj : Disjoint F D := by
    apply disjoint_left.mpr
    intro z zf zd
    exact ((notB z).mpr (by simpa [D] using zd)) (mem_filter.mp zf).2
  have all : F∪D=univ := by
    ext z
    simp only [F,D,mem_union,mem_filter,mem_univ,true_and,iff_true,mem_insert,mem_singleton]
    by_cases hz : B z=true
    · exact Or.inl hz
    · exact Or.inr ((notB z).mp hz)
  let A := Side B true
  have cardF : Fintype.card A=F.card := Fintype.card_subtype (fun z=>B z=true)
  have cardA : Fintype.card A+4=Fintype.card V := by
    have e := congrArg Finset.card all
    rw [card_union_of_disjoint disj,cardD,card_univ,←cardF] at e
    exact e
  have bmod : Fintype.card A%6=4 := by omega
  have lbA : 4≤Fintype.card A := by omega
  have a3 : 3≤Fintype.card A := by omega
  have bt : ColorThree B true := three_by_card B true a3
  have bf : ColorThree B false := by
    refine ⟨x,y,u,xy.ne,ux.symm,uy.symm,?_,?_,?_⟩
    · simp [B,extend]
    · simp [B,extend,xy.ne.symm]
    · simp [B,extend,ux,uy,cu]
  have pos : OutsideTwo c x y true := ⟨u,w,ux,uy,wx,wy,uw,cu,cw⟩
  have neg : OutsideTwo c x y false := by
    obtain ⟨a,b,_,ab,_,_,ha,hb,_⟩ := bt
    obtain ⟨ax,ay,ac⟩ := (b_eq a).mp ha
    obtain ⟨bx,by',bc⟩ := (b_eq b).mp hb
    exact ⟨a,b,ax,ay,bx,by',ab,ac,bc⟩
  obtain ⟨_,xt,_,yt⟩ := (outside_cut_balance G small c xy (cub x) (cub y) pos neg).2 cut
  have bcut : (boundary G B).card=4 := by
    have swap := FourRingCutAux.boundary_flip_card G (extend c x y true true)
    change (boundary G B).card=(boundary G (extend c x y true true)).card at swap
    rw [swap,extended_boundary G c xy,cut,xt,yt]
    decide
  obtain ⟨p,r,markPort,E,_,_⟩ := true_shore_attachment G B small cub bt bf bcut
  let J := sideGraph G B true
  let O := sideGraph G B false
  let qA : A := ⟨q,(b_eq q).mpr ⟨qx,qy,cq⟩⟩
  let wO : Side B false := ⟨w,by simp [B,extend,wx,wy,cw]⟩
  obtain ⟨i,iq,_⟩ := markPort qA wO wq.symm
  have cb (z : A⊕Side B false) : (attach J O p r).degree z=3 :=
    (transfer_degree E z).trans (cub (E z))
  have single : SingleReady J qA := by
    by_cases e : Fintype.card A=4
    · exact RemoteAvoid3MixedBridge.tiny_from_original_shore p r cb e qA
    · have out : 1<Fintype.card (Side B false) := by
        let ax : Side B false := ⟨x,by simp [B,extend]⟩
        let ay : Side B false := ⟨y,by simp [B,extend,xy.ne.symm]⟩
        have ne : ax≠ay := fun h=>xy.ne (congrArg Subtype.val h)
        have card := card_le_univ (s:=({ax,ay}:Finset (Side B false)))
        simpa [ne] using card
      have larg : 4<Fintype.card A := by omega
      have gap : Fintype.card A+2<Fintype.card V := by omega
      rw [←iq]
      exact RemoteAvoid3MixedBridge.single_from_original_shore p r cb
        (transfer_small E small) larg out bmod (Fintype.card V) gap avo i
  let f : A↪V := Function.Embedding.subtype (fun z=>B z=true)
  have adj (a b : A) (h : J.Adj a b) : (eraseEdge G u v).Adj (f a) (f b) := by
    refine ⟨h,?_⟩
    rintro (⟨e,_⟩|⟨_,e⟩)
    · exact (notB u).mpr (Or.inr (Or.inr (Or.inl rfl))) (e ▸ a.property)
    · exact (notB u).mpr (Or.inr (Or.inr (Or.inl rfl))) (e ▸ b.property)
  have mapped := factor_map f adj single
  have support : (univ.erase qA).map f=outside x y \ ({u,w,q}:Finset V) := by
    ext z
    constructor
    · intro zs
      obtain ⟨a,am,e⟩ := mem_map.mp zs
      change a.val=z at e
      have h : B z=true := e ▸ a.property
      obtain ⟨zx,zy,_⟩ := (b_eq z).mp h
      have zu : z≠u := fun k=> (notB z).mpr (Or.inr (Or.inr (Or.inl k))) h
      have zw : z≠w := fun k=> (notB z).mpr (Or.inr (Or.inr (Or.inr k))) h
      have zq : z≠q := fun k=> (mem_erase.mp am).1 (Subtype.ext (e.trans k))
      exact mem_sdiff.mpr ⟨mem_outside.mpr ⟨zx,zy⟩,by simp [zu,zw,zq]⟩
    · intro zs
      obtain ⟨a,b⟩ := mem_sdiff.mp zs
      obtain ⟨zx,zy⟩ := mem_outside.mp a
      have ne : z≠u∧z≠w∧z≠q := by simpa using b
      have h : B z=true := by
        by_cases hz : B z=true
        · exact hz
        · rcases (notB z).mp hz with p|p|p|p
          · exact (zx p).elim
          · exact (zy p).elim
          · exact (ne.1 p).elim
          · exact (ne.2.1 p).elim
      let zA : A := ⟨z,h⟩
      have zq : zA≠qA := fun r=>ne.2.2 (congrArg Subtype.val r)
      exact mem_map.mpr ⟨zA,mem_erase.mpr ⟨zq,mem_univ _⟩,rfl⟩
  apply iffFactor.mpr
  rwa [support] at mapped

/-- Count-based wrapper: specifying a two-vertex shore does not
require naming the partner of the omitted edge's endpoint. -/
theorem tiny_remote_factor_of_count
    (small : SmallTrivial G) (big : 5≤Fintype.card V) (cub : ∀ z,G.degree z=3)
    (rem : Fintype.card V%6=2)
    {x y u v : V} (xy : G.Adj x y)
    (ux : u≠x) (uy : u≠y) (vx : v≠x) (vy : v≠y) (uv : G.Adj u v)
    (c : V→Bool) (cu : c u=true) (cv : c v=false)
    (two : ((outside x y).filter (fun z=>c z=true)).card=2)
    (cut : (innerCut G c x y).card=2)
    (avo : SmallerIsolatedAvoid3.{u} (Fintype.card V)) :
    FactorOn (eraseEdge G u v) (outside x y) := by
  classical
  let S := (outside x y).filter (fun z=>c z=true)
  obtain ⟨a,b,neq,h⟩ := card_eq_two.mp two
  have find : u∈S := mem_filter.mpr ⟨mem_outside.mpr ⟨ux,uy⟩,cu⟩
  change S={a,b} at h
  have cert : ∃ w : V,u≠w∧S={u,w} := by
    rw [h,mem_insert,mem_singleton] at find
    rcases find with rfl|rfl
    · exact ⟨b,neq,h⟩
    · exact ⟨a,neq.symm,h.trans (by ext z; simp [or_comm])⟩
  obtain ⟨w,uw,e⟩ := cert
  have wt : w∈S := by rw [e]; simp
  obtain ⟨wm,cw⟩ := mem_filter.mp wt
  obtain ⟨wx,wy⟩ := mem_outside.mp wm
  have precise (z : V) (zx : z≠x) (zy : z≠y) : c z=true ↔ z=u∨z=w := by
    have h : z∈S ↔ c z=true := by simp [S,zx,zy]
    rw [e,mem_insert,mem_singleton] at h
    exact h.symm
  exact tiny_remote_factor G small big cub rem xy ux uy vx vy wx wy uw uv c cu cv cw precise cut avo

#print axioms tiny_remote_factor
#print axioms tiny_remote_factor_of_count
end KelmansCactus.AtomicBridge.RemoteAvoid3TinyBridge
