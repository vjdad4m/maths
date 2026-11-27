import BoundaryRoute
import DoubleAdjacent
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
variable {X : Set V} {z r a b x y : V}

omit [DecidableRel G.Adj] in
private theorem exposed_pair_path (F : SingletonCut G X z r a b) (xX : x ∈ X) (yX : y ∈ X)
    (xy : G.Adj x y) (xa : G.Adj x a) (yb : G.Adj y b) {t : V}
    (mode : t = y ∨ G.Adj y a ∧ (t = a ∨ t = b)) :
    Traverses G (insert r (X \ {x,y}))ᶜ x t := by
  let W := insert r (X \ ({x,y} : Set V))
  have za := (F.cut.2 a).mpr (by simp)
  have zb := (F.cut.2 b).mpr (by simp)
  have zx : z ≠ x := fun e => F.zX (e.symm ▸ xX)
  have zy : z ≠ y := fun e => F.zX (e.symm ▸ yX)
  have ax := xa.ne.symm
  have by' := yb.ne.symm
  have ay : a ≠ y := fun e => F.offX a (by simp) (e.symm ▸ yX)
  have bx : b ≠ x := fun e => F.offX b (by simp) (e.symm ▸ xX)
  have part (t : V) : t ∈ Wᶜ ↔ t = z ∨ t = a ∨ t = b ∨ t = x ∨ t = y := by
    apply (F.complement_of_cone (M := {x,y}) (by
      rintro v (vx|vy)
      · exact vx.symm ▸ xX
      · exact (show v = y from vy).symm ▸ yX) t).trans
    simp
  rcases mode with h|⟨ya,h|h⟩ <;> subst t
  · let L := [x,a,z,b,y] 
    let P : PathOn G Wᶜ := ⟨L,by simp [L],by simp [L,List.chain'_cons,za,zb,za.symm,zb.symm,xy,xa,xa.symm,yb,yb.symm],
      by simp [L,za.ne,zb.ne,zx,zy,F.ab,xy.ne,ax,ay,bx,by',za.ne.symm,zb.ne.symm,zx.symm,zy.symm,F.ab.symm,xy.ne.symm,ax.symm,ay.symm,bx.symm,by'.symm],by
        intro t; rw [part]; simp [L,or_left_comm,or_comm,or_assoc]⟩
    exact ⟨P,rfl,rfl⟩
  · let L := [x,y,b,z,a] 
    let P : PathOn G Wᶜ := ⟨L,by simp [L],by simp [L,List.chain'_cons,za,zb,za.symm,zb.symm,xy,xa.symm,yb,yb.symm,ya],
      by simp [L,za.ne,zb.ne,zx,zy,F.ab,xy.ne,ax,ay,bx,by',za.ne.symm,zb.ne.symm,zx.symm,zy.symm,F.ab.symm,xy.ne.symm,ax.symm,ay.symm,bx.symm,by'.symm],by
        intro t; rw [part]; simp [L,or_left_comm,or_comm,or_assoc]⟩
    exact ⟨P,rfl,rfl⟩
  · let L := [x,y,a,z,b] 
    let P : PathOn G Wᶜ := ⟨L,by simp [L],by simp [L,List.chain'_cons,za,zb,za.symm,zb.symm,xy,xa.symm,yb,yb.symm,ya],
      by simp [L,za.ne,zb.ne,zx,zy,F.ab,xy.ne,ax,ay,bx,by',za.ne.symm,zb.ne.symm,zx.symm,zy.symm,F.ab.symm,xy.ne.symm,ax.symm,ay.symm,bx.symm,by'.symm],by
        intro t; rw [part]; simp [L,or_left_comm,or_comm,or_assoc]⟩
    exact ⟨P,rfl,rfl⟩

private theorem touchless_has_other_port (F : SingletonCut G X z r a b) (xX : x ∈ X) (yX : y ∈ X)
    (ry : ¬ G.Adj r y) (none : ¬ ∃ h ∈ X \ {x,y}, G.Adj y h) : G.Adj y a := by
  classical
  have deg := degree_of_small_deletion_preconnected (G := G)
    (by have := F.conn.1; omega : 4 ≤ Fintype.card V) (fun D hD => (F.conn.2 D hD).preconnected) y
  by_contra ya
  have sub : G.neighborFinset y ⊆ {x,b} := by
    intro s hs
    have ys := (G.mem_neighborFinset y s).mp hs
    rcases F.cover s with sX|sz|sr|sa|sb
    · by_cases sx : s=x
      · simp [sx]
      · exact (none ⟨s,⟨sX,by simp [sx,ys.ne.symm]⟩,ys⟩).elim
    · exact (F.offX y ((F.cut.2 y).mp (sz ▸ ys.symm)) yX).elim
    · exact (ry (sr ▸ ys.symm)).elim
    · exact (ya (sa ▸ ys)).elim
    · simp [sb]
  have lo := Finset.card_le_card sub
  have xb : x ≠ b := fun e => F.offX b (by simp) (e ▸ xX)
  rw [G.card_neighborFinset_eq_degree,Finset.card_pair xb] at lo
  omega

private theorem oriented_match (F : SingletonCut G X z r a b) (xX : x ∈ X) (yX : y ∈ X)
    (xy : G.Adj x y) (rx : ¬ G.Adj r x) (ry : ¬ G.Adj r y)
    (on : ∀ h ∈ X \ {x,y}, G.Adj r h) (xa : G.Adj x a) (yb : G.Adj y b)
    (touch : ∃ h ∈ X \ {x,y}, G.Adj x h) : Traceable G := by
  classical
  let H := X \ ({x,y} : Set V)
  have route := exposed_pair_path F xX yX xy xa yb (Or.inl rfl)
  obtain ⟨Q,q0,q1⟩ := route
  have close : G.Adj Q.last Q.first := q1.symm ▸ q0.symm ▸ xy.symm
  by_cases yt : ∃ h ∈ H, G.Adj y h
  · exact F.traceable_of_two_boundary_routes (fun (v : V) (h : v ∈ H) => h.1) on xX rx touch yt Q close
      ⟨Q,q0,q1⟩
  have ya := touchless_has_other_port F xX yX ry yt
  apply Classical.byContradiction
  intro no
  obtain ⟨C⟩ := F.three_cliques_of_cycle (H := H) (fun _ hv => hv.1) on
    (by obtain ⟨h,hH,_⟩ := touch; exact ⟨h,hH⟩) Q close no
  apply no (C.traceable_of_flexible_exit F (fun _ h => h.1) on xX rx touch ?_)
  intro s sw sx st
  obtain ⟨v,vH,sv⟩ := st
  have sub : ({x,y} : Set V) ⊆ X := by
    rintro v (vx|vy)
    · exact vx.symm ▸ xX
    · exact (show v=y from vy).symm ▸ yX
  rcases (F.complement_of_cone sub s).mp sw with sz|sa|sb|sm
  · exact (F.offX v ((F.cut.2 v).mp (sz ▸ sv)) vH.1).elim
  · exact exposed_pair_path F xX yX xy xa yb (Or.inr ⟨ya,Or.inl sa⟩)
  · exact exposed_pair_path F xX yX xy xa yb (Or.inr ⟨ya,Or.inr sb⟩)
  · exact exposed_pair_path F xX yX xy xa yb (Or.inl ((show s = x ∨ s = y from sm).resolve_left sx))

omit [DecidableRel G.Adj] in
private theorem swap_others (F : SingletonCut G X z r a b) : SingletonCut G X z r b a := by
  have eq : ({r,b,a} : Finset V) = {r,a,b} := by ext w; simp [or_comm]
  refine ⟨⟨F.conn,F.rb,F.ra,F.ab.symm,eq.symm ▸ F.offX,eq.symm ▸ F.boundX,F.connX⟩,
    F.budget,F.zX,eq.symm ▸ F.cut,?_⟩
  intro v; rcases F.cover v with h|h|h|h|h <;> tauto

/-- A port missing exactly an adjacent pair suffices if the two vertices
can be matched to the two other ports. No deletion path, neighbor-shore
connectivity, or condition on the other ports' nonneighbors is assumed. -/
theorem SingletonCut.traceable_of_matched_two_misses (F : SingletonCut G X z r a b) (xX : x ∈ X)
    (yX : y ∈ X) (xy : G.Adj x y) (rx : ¬ G.Adj r x) (ry : ¬ G.Adj r y)
    (on : ∀ h ∈ X \ {x,y}, G.Adj r h) (xa : G.Adj x a) (yb : G.Adj y b) : Traceable G := by
  classical
  let H := X \ ({x,y} : Set V)
  obtain ⟨h,hX,rh⟩ := F.toOneShore.contact (Finset.mem_insert_self r _)
  have hx : h ≠ x := fun e => rx (e ▸ rh)
  have hy : h ≠ y := fun e => ry (e ▸ rh)
  have hH : h ∈ H := ⟨hX,by simp [hx,hy]⟩
  obtain ⟨walk⟩ := F.connX.preconnected (⟨h,hX⟩ : X) ⟨x,xX⟩
  have off : x ∉ H := fun h => h.2 (Or.inl rfl)
  obtain ⟨i,ih,j,jh,edge⟩ := crossingOnWalk (U := {w : X | w.val ∈ H}) walk hH off
  have hits : j.val = x ∨ j.val = y := Classical.byContradiction fun h => jh ⟨j.property,h⟩
  rcases hits with jx|jy
  · exact oriented_match F xX yX xy rx ry on xa yb ⟨i.val,ih,jx ▸ edge.symm⟩
  · have eq : ({x,y} : Set V) = {y,x} := Set.pair_comm x y
    exact oriented_match (swap_others F) yX xX xy.symm ry rx (eq ▸ on) yb xa ⟨i.val,eq ▸ ih,jy ▸ edge.symm⟩

#print axioms SingletonCut.traceable_of_matched_two_misses
end Graffiti199Depleted.Catalogue.Incomplete
