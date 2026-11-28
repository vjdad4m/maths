import StarPalette

namespace Graffiti384b.OddStars
open Finset SimpleGraph PositivePalette
open private TrianglePrune.triangle_iff from TrianglePrune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

private theorem no_zero {W : Finset V} (eq : W.image (trianglesAt G)=(types G).erase 0)
    {z : V} (zm : z∈W) (zero : trianglesAt G z=0) : False := by
  have inside := mem_image_of_mem (trianglesAt G) zm
  rw [eq,zero] at inside
  exact not_mem_erase _ _ inside

/-- Repeated scores at least two already provide the additional omission. -/
theorem distinct_rich (fail : bound G<gamma G) {x y : V} (rich : 2≤trianglesAt G x)
    (same : trianglesAt G x=trianglesAt G y) : x=y := by
  obtain ⟨W,inc,cut,rep⟩ := representatives G x
  have result := rigid G (J:=patch G {x}) (fun _ _ h => h.1) rep cut fail
  exact result.2.1 (inc (rich_high G rich _)) (inc (rich_high G (same ▸ rich) _)) same

theorem zero_degree (fail : bound G<gamma G) {z : V} (zero : trianglesAt G z=0) :
    G.degree z≤2 := by
  by_contra! highZ
  obtain ⟨W,inc,cut,rep⟩ := representatives G z
  have result := rigid G (J:=patch G {z}) (fun _ _ h => h.1) rep cut fail
  have dg := center_degree G (mem_singleton_self z)
  exact no_zero G result.1 (inc (mem_filter.mpr ⟨mem_univ _,by omega⟩)) zero

/-- As soon as one count-one vertex has degree at least three, it must be
the unique count-one vertex in a failure. -/
theorem rich_one_unique (fail : bound G<gamma G) {x f : V} (dx : 3≤G.degree x)
    (sx : trianglesAt G x=1) (sf : trianglesAt G f=1) : x=f := by
  let J := patch G {x}
  let W := insert f (high J)
  have cut := cover_one G x sf
  have rep : Represents G W := represents_of_high G (S:={x}) (subset_insert ..) (fun _ =>
    ⟨f,mem_insert_self ..,sf⟩)
  have inj := (rigid G (J:=J) (fun _ _ h => h.1) rep cut fail).2.1
  have dg : J.degree x=G.degree x := center_degree G (mem_singleton_self x)
  exact inj (mem_insert_of_mem (mem_filter.mpr ⟨mem_univ _,dg ▸ dx⟩)) (mem_insert_self ..) (sx.trans sf.symm)

/-- For a degree-two zero to survive, score one must occur, and every
vertex of that score must still have degree two in the original graph. -/
theorem zero_two_forces_ears (fail : bound G<gamma G) {z : V} (zero : trianglesAt G z=0)
    (dz : G.degree z=2) :
    1∈types G ∧ ∀ f,trianglesAt G f=1 → G.degree f=2 := by
  have forbid (c : V) (rich : 1∈types G → ∃ f∈high (patch G {c,z}),trianglesAt G f=1) : False := by
    let J := patch G {c,z}
    have sz : z∈({c,z}:Finset V) := mem_insert_of_mem (mem_singleton_self _)
    have deg : J.degree z=2 := (center_degree G sz).trans dz
    have cut := cover_two G (S:={c,z}) (c:=c) (e:=z) Subset.rfl deg
    have rep := represents_of_high G (S:={c,z}) (W:=insert z (high J)) (subset_insert ..) (fun m => by
      obtain ⟨f,fm,h⟩ := rich m
      exact ⟨f,mem_insert_of_mem fm,h⟩)
    have both := rigid G (J:=J) (fun _ _ h => h.1) rep cut fail
    exact no_zero G both.1 (mem_insert_self ..) zero
  constructor
  · exact Classical.byContradiction fun off => forbid z (fun i => (off i).elim)
  · intro f sf
    have pos : 0<trianglesAt G f := by omega
    obtain ⟨a,b,fa,fb,ab⟩ := (TrianglePrune.triangle_iff G f).mp pos
    have low := Prerequisites.deg2 G ab.ne fa fb
    by_contra! ne
    have dg := center_degree G (S:={f,z}) (mem_insert_self ..)
    exact forbid f (fun _ => ⟨f,mem_filter.mpr ⟨mem_univ _,by omega⟩,sf⟩)

end Graffiti384b.OddStars
#print axioms Graffiti384b.OddStars.distinct_rich
#print axioms Graffiti384b.OddStars.zero_degree
#print axioms Graffiti384b.OddStars.rich_one_unique
#print axioms Graffiti384b.OddStars.zero_two_forces_ears