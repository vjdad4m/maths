import ThreePort
import LaminarMinima

open Finset SimpleGraph
namespace KelmansCactus.AtomicBridge.OddUncross
open ThreePort FourRingCutAux
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- Cap a matching shore with a single new vertex. -/
abbrev CapV (A : Finset V) := (↑A : Type u) ⊕ Unit
abbrev capRoot (A : Finset V) : CapV A := Sum.inr ()
private def capPort (A : Finset V) (p : Fin 3→V) (pA : ∀ i,p i∈A) (i : Fin 3) :
    CapV A := Sum.inl ⟨p i,pA i⟩

omit [Fintype V] [DecidableEq V] in
def atomCap (G : SimpleGraph V) (A : Finset V) (p : Fin 3→V) : SimpleGraph (CapV A) where
  Adj x y := match x,y with
    | Sum.inl a, Sum.inl b => G.Adj a.val b.val
    | Sum.inr _, Sum.inr _ => False
    | Sum.inl a, Sum.inr _ | Sum.inr _, Sum.inl a => ∃ i,p i=a.val
  symm := by
    rintro (a|a) (b|b) h
    · exact h.symm
    · exact h
    · exact h
    · exact h
  loopless := by
    intro a h
    cases a with
    | inl a => exact G.loopless _ h
    | inr a => exact h

private def capMap (A : Finset V) (x : V) : CapV A :=
  if h : x∈A then Sum.inl ⟨x,h⟩ else capRoot A

omit [Fintype V] in
@[simp] private theorem cap_map_pos {A : Finset V} {x : V} (h : x∈A) :
    capMap A x=Sum.inl ⟨x,h⟩ := dif_pos h
omit [Fintype V] in
@[simp] private theorem cap_map_neg {A : Finset V} {x : V} (h : x∉A) :
    capMap A x=capRoot A := dif_neg h

/-- A cut whose capped root is false has at least as many edges as the
corresponding original cut. The matching hypothesis is essential at the
root: different original exits cannot collapse to the same directed edge. -/
private theorem bound_projected_cap_cut {A : Finset V} {p q : Fin 3→V}
    (seam : Seam (G:=G) A p q) (c : CapV A→Bool) (off : c (capRoot A)=false) :
    (boundary G (fun x=>c (capMap A x))).card≤(boundary (atomCap G A p) c).card := by
  classical
  let m : (V×V)→CapV A×CapV A := fun z=>(capMap A z.1,capMap A z.2)
  have memA {x : V} (h : c (capMap A x)=true) : x∈A := by
    by_contra no
    rw [cap_map_neg no,off] at h
    contradiction
  have image_inside : ((boundary G (fun x=>c (capMap A x))).image m)⊆boundary (atomCap G A p) c := by
    intro z zm
    obtain ⟨⟨x,y⟩,xy,rfl⟩ := mem_image.mp zm
    obtain ⟨xt,yf,e⟩ := mem_boundary.mp xy
    refine mem_boundary.mpr ⟨xt,yf,?_⟩
    have hx : x∈A := memA xt
    by_cases hy : y∈A
    · rw [show (m (x,y)).1=Sum.inl ⟨x,hx⟩ from cap_map_pos hx,
          show (m (x,y)).2=Sum.inl ⟨y,hy⟩ from cap_map_pos hy]
      exact e
    · rw [show (m (x,y)).1=Sum.inl ⟨x,hx⟩ from cap_map_pos hx,
          show (m (x,y)).2=capRoot A from cap_map_neg hy]
      obtain ⟨i,eq,_⟩ := (seam.edge _ hx _ hy).mp e
      exact ⟨i,eq⟩
  have inj : Set.InjOn m (↑(boundary G (fun x=>c (capMap A x))) : Set (V×V)) := by
    rintro ⟨x,y⟩ xy ⟨v,w⟩ vw eq
    obtain ⟨xa,_,xe⟩ := mem_boundary.mp xy
    obtain ⟨va,_,ve⟩ := mem_boundary.mp vw
    have hx : x∈A := memA xa
    have hv : v∈A := memA va
    have fst : capMap A x=capMap A v := congrArg (fun z : CapV A×CapV A=>z.1) eq
    have snd : capMap A y=capMap A w := congrArg (fun z : CapV A×CapV A=>z.2) eq
    rw [cap_map_pos hx,cap_map_pos hv] at fst
    have xv : x=v := congrArg Subtype.val (Sum.inl.inj fst)
    subst v
    suffices y=w from Prod.ext rfl this
    by_cases hy : y∈A <;> by_cases hw : w∈A
    · rw [cap_map_pos hy,cap_map_pos hw] at snd
      exact congrArg Subtype.val (Sum.inl.inj snd)
    · rw [cap_map_pos hy,cap_map_neg hw] at snd
      cases snd
    · rw [cap_map_neg hy,cap_map_pos hw] at snd
      cases snd
    · obtain ⟨i,ip,iq⟩ := (seam.edge _ hx _ hy).mp xe
      obtain ⟨j,jp,jq⟩ := (seam.edge _ hx _ hw).mp ve
      have ij := seam.left_inj (ip.trans jp.symm)
      exact iq.symm.trans (ij ▸ jq)
  exact (card_image_of_injOn inj).symm.trans_le (card_le_card image_inside)

/-- A shore minimal among all oriented nontrivial three-cut shores has
a cyclic-four cap whenever its boundary is a matching. -/
theorem minimal_shore_cap_small {A : Finset V} {p q : Fin 3→V}
    (min : MinBoundaryThree G) (ma : MinimalShore G A)
    (seam : Seam (G:=G) A p q) :
    SmallTrivial (atomCap G A p) := by
  classical
  have cutfull (c : CapV A→Bool) (off : c (capRoot A)=false)
      (low : (boundary (atomCap G A p) c).card≤3) : TrivialCut c := by
    refine Classical.byContradiction ?_
    intro nt
    let h := fun x=>c (capMap A x)
    let B := univ.filter (fun x=>h x=true)
    have hh : colourOf B=h := by
      funext z
      by_cases yes : h z=true
      · have bz : z∈B := mem_filter.mpr ⟨mem_univ _,yes⟩
        exact (colour_true.mpr bz).trans yes.symm
      · have ff : h z=false := Bool.eq_false_iff.mpr yes
        have out : z∉B := fun m=>yes (mem_filter.mp m).2
        exact (colour_false.mpr out).trans ff.symm
    have Bsub : B⊆A := by
      intro z hz
      refine Classical.byContradiction ?_
      intro no
      have yes : c (capMap A z)=true := (mem_filter.mp hz).2
      rw [cap_map_neg no,off] at yes
      contradiction
    have non : ¬TrivialCut h := by
      intro simple
      rcases simple with t|f
      · apply nt
        left
        intro x y xt yt
        cases x with
        | inr e => cases e; rw [off] at xt; contradiction
        | inl x =>
          cases y with
          | inr e => cases e; rw [off] at yt; contradiction
          | inl y =>
            have X : h x.val=true := (congrArg c (cap_map_pos x.property)).trans xt
            have Y : h y.val=true := (congrArg c (cap_map_pos y.property)).trans yt
            exact congrArg Sum.inl (Subtype.ext (t _ _ X Y))
      · exact ma.1.2 (Or.inr fun x y xf yf=>
          f _ _ (by simpa [h,cap_map_neg (colour_false.mp xf)] using off)
                (by simpa [h,cap_map_neg (colour_false.mp yf)] using off))
    obtain ⟨yes,no⟩ := both_colours_of_nontrivial non
    have hi : (boundary G h).card≤3 := (bound_projected_cap_cut seam c off).trans low
    have lo := min h yes no
    have BS : ShoreThree G B := by
      unfold ShoreThree
      rw [hh]
      exact ⟨by omega,non⟩
    have strict : B⊂A := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Bsub,?_⟩
      intro eq
      apply nt
      right
      intro u v uf vf
      have root_only (z : CapV A) (zf : c z=false) : z=capRoot A := by
        cases z with
        | inr z => cases z; rfl
        | inl z =>
          have mem : z.val∈B := eq.symm ▸ z.property
          have yes : c (capMap A z.val)=true := (mem_filter.mp mem).2
          rw [cap_map_pos z.property,zf] at yes
          contradiction
      exact (root_only u uf).trans (root_only v vf).symm
    exact (ne_of_lt strict) (ma.2 _ BS Bsub)
  intro c low
  cases h : c (capRoot A)
  · exact cutfull c h low
  · have flip := cutfull (fun x=> !(c x)) (by simp [h])
        ((boundary_flip_card (atomCap G A p) c).trans_le low)
    refine Classical.byContradiction ?_
    intro nt
    exact (not_trivial_flip nt) flip

#print axioms minimal_shore_cap_small
end
end KelmansCactus.AtomicBridge.OddUncross
