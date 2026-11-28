import PaletteEvenCycle
import PaletteEarSeparation

namespace Graffiti384b.PositivePalette
open Finset SimpleGraph OneEar
open private TrianglePrune.skeleton TrianglePrune.scores TrianglePrune.triangle_iff from TrianglePrune384b
open private Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a triangle-supported graph a single triangular ear can join
all high vertices in a cut giving each of them two crossing neighbors. -/
theorem protect_ear (supported : ∀ {x y},G.Adj x y → ∃ z,G.Adj x z ∧ G.Adj y z)
    {e a b : V} (ear : G.neighborFinset e={a,b}) (ab : G.Adj a b) :
    Covered G (insert e (high G)) := by
  classical
  have ea : G.Adj e a := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_self ..)
  have eb : G.Adj e b := (G.mem_neighborFinset ..).mp (ear ▸ mem_insert_of_mem (mem_singleton_self _))
  by_cases reach : (opened G {e,a,b}).Reachable a b
  · obtain ⟨n,two,⟨p⟩⟩ := Prerequisites.route_of_reach G ear eb ab reach
    by_cases even : n%2=0
    · exact close_cycle p ea eb ab.ne even
    have head := p.step 0 (by omega)
    rw [p.start] at head
    obtain ⟨z,az,uz⟩ := supported head
    have ze : z≠e := by
      intro eq
      have m := (G.mem_neighborFinset ..).mpr (show G.Adj e (p.atIdx 1) from eq ▸ uz.symm)
      rw [ear,mem_insert,mem_singleton] at m
      rcases m with ua|ub
      · exact head.ne ua.symm
      · have idx := p.unique 1 (by omega) n le_rfl (ub.trans p.finish.symm)
        omega
    exact parity_detour p two ea eb ab.ne ze az uz
  · exact separated_anchors G ear ab reach

/-- In a triangle-supported graph, protecting one representative of each
positive score costs at most twice the number of available omissions. -/
theorem supported_bound (supported : ∀ {x y},G.Adj x y → ∃ z,G.Adj x z ∧ G.Adj y z) :
    2*gamma G+((types G).erase 0).card≤2*Fintype.card V := by
  classical
  have low {v : V} (vh : v∉high G) (pos : 0<trianglesAt G v) :
      trianglesAt G v=1 ∧ G.degree v=2 := by
    have small : G.degree v≤2 := by
      by_contra! large; exact vh (mem_filter.mpr ⟨mem_univ _,large⟩)
    have cap := (Repair.triangles_le_choose G v).trans (Nat.choose_le_choose 2 small)
    rw [Nat.choose_self] at cap
    obtain ⟨a,b,va,vb,ab⟩ := (TrianglePrune.triangle_iff G v).mp pos
    have dg := Prerequisites.deg2 G ab.ne va vb
    omega
  have finish {W : Finset V} (cov : Covered G W)
      (rep : ∀ v,0<trianglesAt G v → ∃ w∈W,trianglesAt G w=trianglesAt G v) :
      2*gamma G+((types G).erase 0).card≤2*Fintype.card V := by
    have inc : (types G).erase 0 ⊆ W.image (trianglesAt G) := by
      intro k km
      obtain ⟨ne,am⟩ := mem_erase.mp km
      obtain ⟨v,_,rfl⟩ := mem_image.mp am
      exact mem_image.mpr (rep v (Nat.pos_of_ne_zero ne))
    have num := (card_le_card inc).trans card_image_le
    have cost := count_covered G cov
    omega
  by_cases ex : ∃ e,e∉high G ∧ 0<trianglesAt G e
  · obtain ⟨e,eh,ep⟩ := ex
    obtain ⟨one,de⟩ := low eh ep
    obtain ⟨a,b,ear,_,_,ab⟩ := Prerequisites.ear_pair G de ep
    apply finish (protect_ear G supported ear ab)
    intro v vp
    by_cases vh : v∈high G
    · exact ⟨v,mem_insert_of_mem vh,rfl⟩
    · exact ⟨e,mem_insert_self ..,one.trans (low vh vp).1.symm⟩
  · have cov : Covered G (high G) := complete G (P:=∅) (Q:=∅) (by simp)
          (fun _ vh _ _ => (mem_filter.mp vh).2) (by simp) (by simp)
    apply finish cov
    intro v vp
    exact ⟨v,Classical.byContradiction (fun out => ex ⟨v,out,vp⟩),rfl⟩

/-- Every finite simple graph attains half its number of positive triangle
types in omissions, rounded up. Triangle support is obtained internally. -/
theorem positive_bound :
    2*gamma G+((types G).erase 0).card≤2*Fintype.card V := by
  classical
  by_cases ne : Nonempty V
  · let a := Classical.choice ne
    let J := TrianglePrune.skeleton G a ∅
    have sc (v : V) : trianglesAt J v=trianglesAt G v := TrianglePrune.scores G a ∅ v
    have saved : types J=types G := congrArg (fun f : V → ℕ => univ.image f)
      (funext sc)
    have sup : ∀ {x y},J.Adj x y → ∃ z,J.Adj x z ∧ J.Adj y z := by
      intro x y edge
      obtain ⟨xy,w⟩ := edge
      rcases w with ⟨z,xz,yz⟩|h|h
      · exact ⟨z,⟨xz,Or.inl ⟨y,xy,yz.symm⟩⟩,⟨yz,Or.inl ⟨x,xy.symm,xz.symm⟩⟩⟩
      · exact (Finset.not_mem_empty _ h.1).elim
      · exact (Finset.not_mem_empty _ h.1).elim
    have win := supported_bound J sup
    rw [saved] at win
    have mono := Prerequisites.gamma_mono G J (fun _ _ edge => edge.1)
    omega
  · haveI : IsEmpty V := not_nonempty_iff.mp ne
    have du : types G=∅ := by simp [types]
    have escape := high_bound G
    simp only [du,erase_empty,card_empty,add_zero,Fintype.card_eq_zero] at *
    omega

theorem even_bound (even : (types G).card%2=0) : gamma G≤bound G := by
  have win := positive_bound G
  by_cases realized : 0∈types G
  · rw [card_erase_of_mem realized] at win
    unfold bound; omega
  · rw [erase_eq_of_not_mem realized] at win
    unfold bound; omega

/-- A catalogue counterexample would need an odd number of types, including zero. -/
theorem failure_requires_odd_zero (fail : bound G<gamma G) :
    (types G).card%2=1 ∧ 0∈types G := by
  have win := positive_bound G
  constructor
  · by_contra! h
    exact (not_lt_of_ge (even_bound G (by omega))) fail
  · by_contra off
    rw [erase_eq_of_not_mem off] at win
    unfold bound at fail
    omega

/-- An explicit existence statement in the catalogue's two-neighbor convention. -/
theorem even_witness (even : (types G).card%2=0) :
    ∃ D : Finset V, TwoDominates G D ∧ D.card+(types G).card/2≤Fintype.card V := by
  obtain ⟨D,dom,sz⟩ := Nat.sInf_mem (show {k : ℕ | ∃ d,TwoDominates G d ∧ d.card=k}.Nonempty from
    ⟨_,univ,fun _ out => (out (mem_univ _)).elim,rfl⟩)
  have size : (types G).card≤Fintype.card V :=
    (card_image_le (s:=(univ:Finset V)) (f:=trianglesAt G)).trans_eq card_univ
  change D.card=gamma G at sz
  have win := even_bound G even
  unfold bound at win
  exact ⟨D,dom,by omega⟩

end Graffiti384b.PositivePalette
#print axioms Graffiti384b.PositivePalette.protect_ear
#print axioms Graffiti384b.PositivePalette.positive_bound
#print axioms Graffiti384b.PositivePalette.even_bound
#print axioms Graffiti384b.PositivePalette.failure_requires_odd_zero
#print axioms Graffiti384b.PositivePalette.even_witness
