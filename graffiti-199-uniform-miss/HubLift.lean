import CubicPairReduction
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {x y p : V}

theorem pathOn_of_induced_traceable {S : Set V} (tr : Traceable (G.induce S)) : Nonempty (PathOn G S) := by
  obtain ⟨a,b,w,hp,all⟩ := tr
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  refine ⟨⟨w.support.map f,by simp,(List.chain'_map _).mpr w.chain'_adj_support,
    hp.support_nodup.map f.injective,?_⟩⟩
  intro v
  exact ⟨fun h => by obtain ⟨w,_,rfl⟩ := List.mem_map.mp h; exact w.property,
    fun h => List.mem_map.mpr ⟨⟨v,h⟩,all _,rfl⟩⟩

/-- Replace a retained vertex by a three-vertex interval. At most one private
neighbor of the retained end suffices, including when it is a path endpoint. -/
theorem traceable_of_hub_pair_path [DecidableEq V]
    (P : PathOn G {v | v ≠ x ∧ v ≠ p}) (xy : x ≠ y)
    (xp : G.Adj x p) (py : G.Adj p y)
    (one : ∀ u v, u ≠ x → v ≠ x → G.Adj y u → G.Adj y v → ¬ G.Adj x u → ¬ G.Adj x v → u = v) :
    Traceable G := by
  classical
  obtain ⟨L,R,split⟩ := List.mem_iff_append.mp ((P.covers y).mpr ⟨xy.symm,py.ne.symm⟩)
  have ch := P.chain; rw [split] at ch
  have nd := P.nodup; rw [split] at nd
  have lc := ch.left_of_append
  have rc := ch.right_of_append.tail
  have left (u : V) (hu : u ∈ L.getLast?) : G.Adj u y :=
    (List.chain'_append.mp ch).2.2 u hu y (by simp)
  have right (v : V) (hv : v ∈ R.head?) : G.Adj y v :=
    (List.chain'_cons'.mp ch.right_of_append).1 v hv
  have compatible : (∀ u ∈ L.getLast?, G.Adj u x) ∨ ∀ v ∈ R.head?, G.Adj x v := by
    by_cases ok : ∀ u ∈ L.getLast?, G.Adj u x
    · exact Or.inl ok
    right
    intro v vr
    by_contra xv
    push_neg at ok
    obtain ⟨u,ul,ux⟩ := ok
    obtain ⟨h,e⟩ := List.mem_getLast?_eq_getLast ul
    have um : u ∈ L := by rw [e]; exact List.getLast_mem h
    have vm := List.mem_of_mem_head? vr
    have uo := ((P.covers u).mp (split.symm ▸ List.mem_append_left _ um)).1
    have vo := ((P.covers v).mp (split.symm ▸ List.mem_append_right _ (List.mem_cons_of_mem _ vm))).1
    have eq := one u v uo vo (left _ ul).symm (right _ vr) (fun e => ux e.symm) xv
    exact List.disjoint_left.mp (List.nodup_append.mp nd).2.2 um
      (List.mem_cons_of_mem _ (eq.symm ▸ List.mem_of_mem_head? vr))
  have insertPath {s t : V} (st : (s=x ∧ t=y) ∨ (s=y ∧ t=x))
      (ls : ∀ u ∈ L.getLast?, G.Adj u s) (tr' : ∀ v ∈ R.head?, G.Adj t v) : Traceable G := by
    have sp : G.Adj s p := by rcases st with ⟨rfl,_⟩|⟨rfl,_⟩; exact xp; exact py.symm
    have pt : G.Adj p t := by rcases st with ⟨_,rfl⟩|⟨_,rfl⟩; exact py; exact xp.symm
    let W := L ++ ([s,p,t] ++ R)
    have chain : W.Chain' G.Adj := by
      have mid : ([s,p,t] : List V).Chain' G.Adj := by simp [List.chain'_cons,sp,pt]
      apply lc.append (mid.append rc ?_) ?_
      · intro u hu v hv
        have eq : t = u := by simpa using hu
        exact eq ▸ tr' _ hv
      · intro u hu v hv
        have eq : s = v := by simpa using hv
        exact eq ▸ ls _ hu
    have perm : W.Perm (x :: p :: P.vertices) := by
      rw [split]
      rcases st with ⟨hs,ht⟩|⟨hs,ht⟩ <;> subst s <;> subst t
      · exact (List.perm_middle (a := x) (l₁ := L) (l₂ := p :: y :: R)).trans
          ((List.perm_middle (a := p) (l₁ := L) (l₂ := y :: R)).cons x)
      · have turn : ([y,p,x] : List V).Perm [x,p,y] := List.reverse_perm [x,p,y]
        exact ((turn.append_right R).append_left L).trans
          ((List.perm_middle (a := x) (l₁ := L) (l₂ := p :: y :: R)).trans
            ((List.perm_middle (a := p) (l₁ := L) (l₂ := y :: R)).cons x))
    have full (v : V) : v ∈ W := by
      apply perm.mem_iff.mpr
      by_cases vx : v=x
      · exact List.mem_cons.mpr (Or.inl vx)
      by_cases vp : v=p
      · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (Or.inl vp))
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ((P.covers v).mpr ⟨vx,vp⟩))
    have nd' : (x :: p :: P.vertices).Nodup := by
      simp [P.covers,xp.ne,P.nodup]
    apply traceable_iff_hamiltonian_walk.mpr
    apply pathOn_univ_iff_hamiltonian_walk.mp
    exact ⟨⟨W,by intro e; simpa [e] using full x,chain,perm.nodup_iff.mpr nd',fun v => ⟨fun _ => Set.mem_univ _,fun _ => full v⟩⟩⟩
  exact compatible.elim (fun h => insertPath (Or.inl ⟨rfl,rfl⟩) h right)
    (fun h => insertPath (Or.inr ⟨rfl,rfl⟩) left h)

#print axioms traceable_of_hub_pair_path
end Graffiti199Depleted.Catalogue.Incomplete




