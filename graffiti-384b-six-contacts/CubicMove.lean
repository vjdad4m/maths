import TriangleReturn
namespace Graffiti384b.SixFront
open Finset SimpleGraph PinnedColor34 Exterior Four29 LowSample
open private Repair.nbr_mono Repair.full_nbr Repair.triangles_le_choose from Repair384b
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The single-vertex exchange needs spare degree only at neighbors of the vertex moved. -/
theorem safe_repair {P Q : Finset V} {u x m : V} (dis : Disjoint P Q) (q : (types G).card≤(nonleaves G).card)
    (degrees : ∀ v∈nonleaves G,v∉P → v∉Q → 3≤G.degree v)
    (safe : ∀v∈nonleaves G,v∉P → v∉Q → G.Adj v x → 4≤G.degree v)
    (lp : ∀ v∈P,v≠u → 2≤nbr G v Q) (rq : ∀ v∈Q,2≤nbr G v P)
    (one : 0<nbr G u Q) (up : u∈P) (xp : x∉P) (xq : x∉Q) (mq : m∉Q)
    (ux : G.Adj u x) (um : G.Adj u m) (xm : G.Adj x m) : gamma G≤bound G := by
  obtain ⟨A,pa,qb,la,rb⟩ := cut G P Q dis
  have left (v : V) (vn : v∈nonleaves G) (va : v∈A) (ne : v≠u) : 2≤nbr G v Aᶜ := by
    by_cases vp : v∈P
    · exact (lp v vp ne).trans (Repair.nbr_mono G v qb)
    · have dg := degrees v vn vp (fun h => mem_compl.mp (qb h) va)
      have bal := la v va vp
      have eq := Repair.full_nbr G v A
      omega
  have right (v : V) (vn : v∈nonleaves G) (vb : v∈Aᶜ) (vq : v∉Q) : 2≤nbr G v A := by
    have dg := degrees v vn (fun h => mem_compl.mp vb (pa h)) vq
    have bal := rb v vb vq
    have eq := Repair.full_nbr G v A
    omega
  by_cases good : 2≤nbr G u Aᶜ
  · apply both G A q
    · intro v vn va
      by_cases eq : v=u
      · exact eq ▸ good
      · exact left v vn va eq
    · intro v vn vb
      by_cases vq : v∈Q
      · exact (rq v vq).trans (Repair.nbr_mono G v pa)
      · exact right v vn vb vq
  obtain ⟨j,jm⟩ := card_pos.mp one
  obtain ⟨jq,uj⟩ := mem_filter.mp jm
  have same {v : V} (uv : G.Adj u v) (vq : v∉Q) : v∈A := by
    by_contra no
    exact good (two G (a:=v) (b:=j) (fun e => vq (e ▸ jq)) uv uj (mem_compl.mpr no) (qb jq))
  have xa := same ux xq
  have ma := same um mq
  have rest : P⊆A.erase x := fun i ip => mem_erase.mpr ⟨fun e => xp (e ▸ ip),pa ip⟩
  apply both G (A.erase x) q
  · intro v vn va
    rw [compl_erase]
    by_cases eq : v=u
    · subst v
      exact two G (a:=x) (b:=j) (fun e => xq (e ▸ jq)) ux uj (mem_insert_self ..) (mem_insert_of_mem (qb jq))
    · exact (left v vn (mem_erase.mp va).2 eq).trans (Repair.nbr_mono G v (subset_insert ..))
  · intro v vn vb
    rw [compl_erase,mem_insert] at vb
    rcases vb with rfl|vb
    · exact two G um.ne ux.symm xm (rest up) (mem_erase.mpr ⟨xm.ne.symm,ma⟩)
    by_cases vq : v∈Q
    · exact (rq v vq).trans (Repair.nbr_mono G v rest)
    · have base := right v vn vb vq
      by_cases vx : G.Adj v x
      · have dg := safe v vn (fun m => mem_compl.mp vb (pa m)) vq vx
        have bal := rb v vb vq
        have eq := Repair.full_nbr G v A
        have big : 3≤nbr G v A := by omega
        have inc : A.filter (G.Adj v)⊆insert x ((A.erase x).filter (G.Adj v)) := by
          intro i im
          by_cases e : i=x
          · exact mem_insert.mpr (Or.inl e)
          · exact mem_insert_of_mem (mem_filter.mpr ⟨mem_erase.mpr ⟨e,(mem_filter.mp im).1⟩,(mem_filter.mp im).2⟩)
        have bd := (card_le_card inc).trans (card_insert_le ..)
        change nbr G v A≤nbr G v (A.erase x)+1 at bd
        omega
      · have sub : A.filter (G.Adj v)⊆(A.erase x).filter (G.Adj v) := by
          intro i im
          exact mem_filter.mpr ⟨mem_erase.mpr ⟨fun eq => vx (eq ▸ (mem_filter.mp im).2),(mem_filter.mp im).1⟩,(mem_filter.mp im).2⟩
        exact base.trans (card_le_card sub)


/-- The score-two anchor accounts for one of the two possible high cubic
scores. There is at most one unpinned cubic. It either misses a movable
vertex or sees both movable vertices and provides a four-cycle. -/
theorem score_two_gap {P Q : Finset V} {e f a x y : V} (D : Data G e f)
    (quota : (types G).card≤(nonleaves G).card) (H : Gap G P Q a)
    (ep : e∈P∪Q) (fp : f∈P∪Q) (ah : a∈high G) (two : trianglesAt G a=2)
    (xo : x∉P∪Q) (yo : y∉P∪Q) (ax : G.Adj a x) (ay : G.Adj a y) (xy : G.Adj x y) :
    gamma G≤bound G := by
  classical
  have highFree (v : V) (vn : v∈nonleaves G) (vp : v∉P) (vq : v∉Q) : v∈high G := by
    by_contra hi
    have m : v∈twos G := mem_sdiff.mpr ⟨vn,hi⟩
    rw [D.earSet,mem_insert,mem_singleton] at m
    exact (mem_union.mp (m.elim (fun eq => eq ▸ ep) (fun eq => eq ▸ fp))).elim vp vq
  have deg (v : V) (vn : v∈nonleaves G) (vp : v∉P) (vq : v∉Q) :=
    (mem_filter.mp (highFree v vn vp vq)).2
  have cubic {v : V} (vn : v∈nonleaves G) (vp : v∉P) (vq : v∉Q) (d : G.degree v<4) :
      trianglesAt G v=3 := by
    have vh := highFree v vn vp vq
    have large := D.rich v vh
    have cap := Repair.triangles_le_choose G v
    have dg : G.degree v=3 := by have := deg v vn vp vq; omega
    rw [dg,show (3:ℕ).choose 2=3 by decide] at cap
    have neq : trianglesAt G v≠2 := fun eq => vp (D.scoreInj vh ah (eq.trans two.symm) ▸ H.pinned)
    omega
  let safe := fun s : V => ∀v∈nonleaves G,v∉P → v∉Q → G.Adj v s → 4≤G.degree v
  have move {s w : V} (so : s∉P∪Q) (wo : w∉P∪Q) (as' : G.Adj a s) (aw : G.Adj a w)
      (sw : G.Adj s w) (ok : safe s) : gamma G≤bound G :=
    safe_repair G H.apart quota deg ok H.left H.right H.one H.pinned
      (fun m => so (mem_union_left _ m)) (fun m => so (mem_union_right _ m))
      (fun m => wo (mem_union_right _ m)) as' aw sw
  by_cases sx : safe x
  · exact move xo yo ax ay xy sx
  by_cases sy : safe y
  · exact move yo xo ay ax xy.symm sy
  dsimp [safe] at sx sy
  push_neg at sx sy
  obtain ⟨u,un,up,uq,ux,du⟩ := sx
  obtain ⟨v,vn,vp,vq,vy,dv⟩ := sy
  have eq := D.scoreInj (highFree u un up uq) (highFree v vn vp vq)
    ((cubic un up uq du).trans (cubic vn vp vq dv).symm)
  subst v
  have um : u∈(P∪Q)ᶜ := mem_compl.mpr (fun m => (mem_union.mp m).elim up uq)
  apply extension_bound G D quota ep fp
  exact four_steps G H disjoint_compl_right (mem_compl.mpr xo) um (mem_compl.mpr yo)
    H.pinned xy.ne ax ux.symm vy ay.symm

end Graffiti384b.SixFront
#print axioms Graffiti384b.SixFront.safe_repair
#print axioms Graffiti384b.SixFront.score_two_gap
