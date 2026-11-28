import TriangleReturn
namespace Graffiti384b.SixFront
open Finset SimpleGraph Four29 LowSample Exterior FiveChoice
open private Repair.edge_info from Repair384b
open private Prune.links Prune.link_in_core from Prune384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A two-edge star between the two ear-neighbor pairs suffices. This
includes additional cross edges and puts no restriction on triangle contacts. -/
theorem fork (t : (types G).card=29) (q : (nonleaves G).card=29) (h : (high G).card=27)
    (l : Fin 6 ↪ V) (first : G.neighborFinset (l 4)={l 0,l 1})
    (second : G.neighborFinset (l 5)={l 2,l 3})
    (bc : G.Adj (l 1) (l 2)) (bd : G.Adj (l 1) (l 3)) : gamma G≤bound G := by
  classical
  apply Nat.le_of_not_gt
  intro bad
  let P : Finset V := {l 0,l 1,l 5}
  let Q : Finset V := {l 4,l 2,l 3}
  let X := pool G (l 4) (l 5)
  have ni {i j : Fin 6} (ne : i≠j) : l i≠l j := l.injective.ne ne
  have de : G.degree (l 4)=2 := by rw [←card_neighborFinset_eq_degree,first,card_pair (ni (by decide))]
  have df : G.degree (l 5)=2 := by rw [←card_neighborFinset_eq_degree,second,card_pair (ni (by decide))]
  have rootsEq : roots G (l 4) (l 5)={l 0,l 1}∪{l 2,l 3} := by rw [roots,first,second]
  have ea : G.Adj (l 4) (l 0) := (G.mem_neighborFinset ..).mp (first ▸ mem_insert_self ..)
  have eb : G.Adj (l 4) (l 1) := (G.mem_neighborFinset ..).mp (first ▸ mem_insert_of_mem (mem_singleton_self _))
  have fc : G.Adj (l 5) (l 2) := (G.mem_neighborFinset ..).mp (second ▸ mem_insert_self ..)
  have fd : G.Adj (l 5) (l 3) := (G.mem_neighborFinset ..).mp (second ▸ mem_insert_of_mem (mem_singleton_self _))
  have gap : Gap G P Q (l 0) := by
    constructor
    · simp [P,Q,l.injective.eq_iff]
    · simp [P]
    · exact card_pos.mpr ⟨l 4,mem_filter.mpr ⟨mem_insert_self ..,ea.symm⟩⟩
    · intro v vm ne
      rcases mem_insert.mp vm with rfl|m
      · exact (ne rfl).elim
      rcases mem_insert.mp m with rfl|m
      · exact PinnedColor34.two G (ni (by decide : (2:Fin 6)≠3)) bc bd (by simp [Q]) (by simp [Q])
      · obtain rfl := mem_singleton.mp m
        exact PinnedColor34.two G (ni (by decide : (2:Fin 6)≠3)) fc fd (by simp [Q]) (by simp [Q])
    · intro v vm
      rcases mem_insert.mp vm with rfl|m
      · exact PinnedColor34.two G (ni (by decide : (0:Fin 6)≠1)) ea eb (by simp [P]) (by simp [P])
      rcases mem_insert.mp m with rfl|m
      · exact PinnedColor34.two G (ni (by decide : (1:Fin 6)≠5)) bc.symm fc.symm (by simp [P]) (by simp [P])
      · obtain rfl := mem_singleton.mp m
        exact PinnedColor34.two G (ni (by decide : (1:Fin 6)≠5)) bd.symm fd.symm (by simp [P]) (by simp [P])
  have dis : Disjoint (P∪Q) X := disjoint_left.mpr (by
    intro u um ux
    obtain ⟨hi,nr⟩ := mem_sdiff.mp ux
    rw [rootsEq] at nr
    have highU := (mem_filter.mp hi).2
    simp only [P,Q,mem_union,mem_insert,mem_singleton] at um nr
    rcases um with (rfl|rfl|rfl)|(rfl|rfl|rfl)
    all_goals first | omega | exact nr (by simp))
  have D := data_of_failure G t h q bad de df (ni (by decide))
  have ep : l 4∈P∪Q := by simp [Q]
  have fp : l 5∈P∪Q := by simp [P]
  have rootsIn : roots G (l 4) (l 5)⊆P∪Q := by
    rw [rootsEq]; intro v vm
    rcases mem_union.mp vm with m|m
    · exact mem_union_left _ (show v∈P by simpa [P] using
        (show v=l 0 ∨ v=l 1 ∨ v=l 5 from by
          rcases mem_insert.mp m with rfl|k
          · exact Or.inl rfl
          · exact Or.inr (Or.inl (mem_singleton.mp k))))
    · exact mem_union_right _ (mem_insert_of_mem m)
  have ar : l 0∈roots G (l 4) (l 5) := rootsEq ▸ mem_union_left _ (mem_insert_self ..)
  have win := fun (E : Extension G P Q) => (not_lt_of_ge (extension_bound G D (by omega) ep fp E)) bad
  have direct (r : V) (rq : r∈Q) (re : l 4≠r) (edge : G.Adj (l 0) r) : False := by
    apply win
    refine ⟨P,Q,Subset.rfl,Subset.rfl,gap.apart,?_,gap.right⟩
    intro v vm
    by_cases eq : v=l 0
    · subst v; exact PinnedColor34.two G re ea.symm edge (by simp [Q]) rq
    · exact gap.left v vm eq
  have ac : ¬G.Adj (l 0) (l 2) := direct _ (by simp [Q]) (ni (by decide))
  have ad : ¬G.Adj (l 0) (l 3) := direct _ (by simp [Q]) (ni (by decide))
  have af : ¬G.Adj (l 0) (l 5) := by
    intro m
    have n := (G.mem_neighborFinset ..).mpr m.symm
    rw [second] at n
    simp [l.injective.eq_iff] at n
  have s := D.rich _ (D.highRoots ar)
  change 2≤(link G (l 0)).card at s
  obtain ⟨p,pm,other⟩ := exists_ne_of_one_lt_card (by omega : 1<(link G (l 0)).card) ({l 4,l 1}:Finset V)
  obtain ⟨sub,two,cl⟩ := Repair.edge_info G pm
  obtain ⟨x,y,ne,pair⟩ := card_eq_two.mp two
  have xm : x∈p := pair ▸ mem_insert_self ..
  have ym : y∈p := pair ▸ mem_insert_of_mem (mem_singleton_self _)
  have xy := cl x xm y ym ne
  have adj {u : V} (um : u∈p) : G.Adj (l 0) u := (G.mem_neighborFinset ..).mp (sub um)
  have notEar {u v : V} (_um : u∈p) (vm : v∈p) (uv : G.Adj u v) (eq : p={u,v}) : u≠l 4 := by
    rintro rfl
    have vn := (G.mem_neighborFinset ..).mpr uv
    rw [first,mem_insert,mem_singleton] at vn
    rcases vn with rfl|rfl
    · exact (G.loopless _ (adj vm))
    · exact other eq
  have classify {u : V} (um : u∈p) (ue : u≠l 4) : u=l 1 ∨ u∈X := by
    by_cases ur : u∈roots G (l 4) (l 5)
    · rw [rootsEq,mem_union,mem_insert,mem_singleton,mem_insert,mem_singleton] at ur
      rcases ur with (rfl|rfl)|(rfl|rfl)
      · exact (G.loopless _ (adj um)).elim
      · exact Or.inl rfl
      · exact (ac (adj um)).elim
      · exact (ad (adj um)).elim
    · right
      apply mem_sdiff.mpr ⟨?_,ur⟩
      by_contra hi
      have core := Prune.link_in_core G (show p∈Prune.links G (l 0) from pm) um
      have ear : u∈twos G := mem_sdiff.mpr ⟨core,hi⟩
      rw [D.earSet,mem_insert,mem_singleton] at ear
      exact ear.elim ue (fun eq => af (eq ▸ adj um))
  have cx := classify xm (notEar xm ym xy pair)
  have cy := classify ym (notEar ym xm xy.symm (pair.trans (pair_comm ..)))
  rcases cx with rfl|xp <;> rcases cy with rfl|yp
  · exact ne rfl
  · exact win (two_steps G gap dis yp (by simp [P]) (ni (by decide)) (adj ym) xy.symm)
  · exact win (two_steps G gap dis xp (by simp [P]) (ni (by decide)) (adj xm) xy)
  · exact (not_lt_of_ge (pool_triangle G t q h de df (ni (by decide)) P Q gap dis rootsIn ar ep fp xp yp
      (adj xm) (adj ym) xy)) bad

end Graffiti384b.SixFront
#print axioms Graffiti384b.SixFront.fork
