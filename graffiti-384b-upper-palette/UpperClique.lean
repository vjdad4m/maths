import FixedCubics
import ShoreCliquePivot
namespace Graffiti384b.OddStars.UpperClique
open Finset SimpleGraph LeafCritical CliquePivot33
open private OddStars.ShoreCounts.in_high from ShoreCounts
open private Repair.omit_set from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A five-clique rules out the entire upper triangle-skeleton branch. -/
theorem no_five (bad : bound G<gamma G) (size : (high (patch G ∅)).card+1=(types G).card) :
    ∀C,¬G.IsNClique 5 C := by
  classical
  let J := patch G ∅
  let H := high J
  let K := J.induce (H:Set V)
  have highN {v w : V} (vw : J.Adj v w) : w∈H := OddStars.ShoreCounts.in_high G bad size vw
  have closed (v : H) : (K.neighborFinset v).map (Function.Embedding.subtype _) = J.neighborFinset v.val := by
    ext w; constructor
    · intro m; obtain ⟨u,um,rfl⟩ := mem_map.mp m
      exact (J.mem_neighborFinset ..).mpr ((K.mem_neighborFinset ..).mp um)
    · intro m; have vw := (J.mem_neighborFinset ..).mp m
      exact mem_map.mpr ⟨⟨w,highN vw⟩,(K.mem_neighborFinset ..).mpr vw,rfl⟩
  have minD (v : H) : 3≤K.degree v := by
    have d := congrArg card (closed v)
    rw [card_map,card_neighborFinset_eq_degree,card_neighborFinset_eq_degree] at d
    exact d ▸ (mem_filter.mp v.property).2
  have keep : nonleaves J⊆H := by
    intro v vm
    have ge : 2≤J.degree v := (mem_filter.mp vm).2
    have d := skeleton_degree_bound G v; change J.degree v≤_ at d
    exact (PendantAudit.upper_branch G bad size).1 v (by omega)
  have sc (v : H) : trianglesAt K v=trianglesAt G v.val :=
    (Prune.counts_preserved J H keep v).trans (patch_scores G ∅ v.val)
  have rich (v : H) : 2≤trianglesAt K v := by
    have d : 3≤J.degree v.val := (mem_filter.mp v.property).2
    have b := skeleton_degree_bound G v.val
    change J.degree v.val≤_ at b
    rw [sc]; omega
  have inj : Function.Injective (trianglesAt K) := fun i j eq =>
    Subtype.ext (distinct_rich G bad (sc i ▸ rich i) ((sc i).symm.trans (eq.trans (sc j))))
  have tight : Tight K ∅ := by
    intro D rd
    have dom : TwoDominates K D := by intro v vo; simpa using rd v vo
    let emb : H ↪ V := Function.Embedding.subtype _
    let O := Dᶜ.map emb
    have val := Repair.omit_set G O (by
      intro v vm
      obtain ⟨w,wm,rfl⟩ := mem_map.mp vm
      have sub : (D.filter (K.Adj w)).map emb ⊆ Oᶜ.filter (G.Adj (emb w)) := by
        intro x xm; obtain ⟨y,ym,rfl⟩ := mem_map.mp xm
        refine mem_filter.mpr ⟨mem_compl.mpr ?_,((mem_filter.mp ym).2 : J.Adj w.val y.val).1⟩
        intro h; obtain ⟨u,um,eq⟩ := mem_map.mp h
        exact mem_compl.mp um (emb.injective eq ▸ (mem_filter.mp ym).1)
      have c := card_le_card sub
      rw [card_map] at c
      exact (dom w (mem_compl.mp wm)).trans c)
    change H.card+1=(types G).card at size
    have hcard : Fintype.card (H:Set V)=H.card := Fintype.card_coe H
    rw [hcard]
    simp only [O,card_map,card_compl] at val
    change gamma G≤Fintype.card V-(Fintype.card (H:Set V)-D.card) at val
    rw [hcard] at val
    unfold bound at bad; omega
  intro C cl
  have edge {x y : V} (xm : x∈C) (ym : y∈C) (ne : x≠y) : J.Adj x y := by
    have xy := cl.1 xm ym ne
    have c := card_insert_le x ({y}:Finset V)
    rw [card_singleton] at c
    obtain ⟨w,wm,off⟩ := exists_mem_not_mem_of_card_lt_card (s:=({x,y}:Finset V)) (t:=C) (by rw [cl.2]; omega)
    have sep : w≠x ∧ w≠y := by simpa using off
    exact ⟨xy,Or.inl ⟨w,cl.1 xm wm sep.1.symm,cl.1 ym wm sep.2.symm⟩⟩
  have inH {w : V} (wm : w∈C) : w∈H := by
    obtain ⟨x,xm,xw⟩ := exists_ne_of_one_lt_card (by rw [cl.2]; decide) w
    exact highN (edge xm wm xw)
  let C' := C.subtype (fun w => w∈H)
  have mapped : C'.map (Function.Embedding.subtype _)=C := subtype_map_of_mem (fun _ h => inH h)
  have clique : K.IsNClique 5 C' := ⟨fun i im j jm ne => edge (mem_subtype.mp im) (mem_subtype.mp jm)
    (fun eq => ne (Subtype.ext eq)),(card_map ..).symm.trans ((congrArg card mapped).trans cl.2)⟩
  have image := (three_cubics K ∅ (fun v => ⟨by have := minD v; omega,fun _ => minD v⟩)
    (fun v => by have := rich v; omega) inj tight clique).2.1
  have one : 1∈Icc (1:ℕ) 3 := by decide
  rw [←image] at one
  obtain ⟨v,_,eq⟩ := mem_image.mp one
  have r := rich v; omega

end Graffiti384b.OddStars.UpperClique
#print axioms Graffiti384b.OddStars.UpperClique.no_five
