import HubTorso
import HubLift
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] {r x y p : V}

theorem traceable_of_filled_hub (ry : r ≠ y) (xy : G.Adj x y)
    (rp : G.Adj r p) (xp : G.Adj x p) (py : G.Adj p y)
    (one : ∀ u v, u ≠ x → v ≠ x → G.Adj y u → G.Adj y v → ¬ G.Adj x u → ¬ G.Adj x v → u=v)
    (tr : Traceable ((hubFill G ry).induce (HubKeep x p))) : Traceable G := by
  classical
  obtain ⟨P⟩ := pathOn_of_induced_traceable tr
  by_cases real : P.vertices.Chain' G.Adj
  · let Q : PathOn G (HubKeep x p) := ⟨P.vertices,P.nonempty,real,P.nodup,P.covers⟩
    exact traceable_of_hub_pair_path Q xy.ne xp py one
  rw [List.chain'_iff_forall_rel_of_append_cons_cons] at real
  push_neg at real
  obtain ⟨u,v,L,R,split,fake⟩ := real
  have ch := P.chain; rw [split] at ch
  obtain ⟨first,e,last⟩ := List.chain'_append_cons_cons.mp ch
  have uv : (u=r ∧ v=y) ∨ (u=y ∧ v=r) := (show G.Adj u v ∨ _ from e).resolve_left fake
  have ne : u ≠ v := (hubFill G ry).ne_of_adj e
  have old := P.nodup; rw [split] at old
  have apart := List.disjoint_left.mp (List.nodup_append.mp old).2.2
  have vn : v ∉ L ++ [u] := by
    intro h
    rcases List.mem_append.mp h with hl|hr
    · exact apart hl (by simp)
    · exact ne (List.mem_singleton.mp hr).symm
  have un : u ∉ v :: R := (List.nodup_cons.mp (List.nodup_append.mp old).2.1).1
  have genuine {T : List V} (chain : T.Chain' (hubFill G ry).Adj) (off : u ∉ T ∨ v ∉ T) :
      T.Chain' G.Adj := by
    apply List.Chain'.imp _ (List.Chain'.iff_mem.mp chain)
    intro s t ⟨hs,ht,edge⟩
    rcases edge with ed|⟨es,et⟩|⟨es,et⟩
    · exact ed
    · rcases uv with ⟨hu,hv⟩|⟨hu,hv⟩ <;> rcases off with h|h <;> simp_all
    · rcases uv with ⟨hu,hv⟩|⟨hu,hv⟩ <;> rcases off with h|h <;> simp_all
  have fl := genuine first (Or.inr vn)
  have lr := genuine last (Or.inl un)
  have route : ∃ m n : V, ((m=p ∧ n=x) ∨ (m=x ∧ n=p)) ∧ G.Adj u m ∧ G.Adj m n ∧ G.Adj n v := by
    rcases uv with ⟨hu,hv⟩|⟨hu,hv⟩ <;> subst u <;> subst v
    · exact ⟨p,x,Or.inl ⟨rfl,rfl⟩,rp,xp.symm,xy⟩
    · exact ⟨x,p,Or.inr ⟨rfl,rfl⟩,xy.symm,xp,rp.symm⟩
  obtain ⟨m,n,ori,um,mn,nv⟩ := route
  let B := L ++ [u]
  let W := B ++ m :: n :: v :: R
  have chain : W.Chain' G.Adj := by
    apply fl.append (List.chain'_cons.mpr ⟨mn,List.chain'_cons.mpr ⟨nv,lr⟩⟩)
    intro w hw t ht
    have h : u=w := by simpa using hw
    have k : m=t := by simpa using ht
    exact h ▸ k ▸ um
  have perm : W.Perm (m :: n :: P.vertices) := by
    have eq : P.vertices = B ++ v :: R := by simp [B,split]
    rw [eq]
    exact (List.perm_middle (a:=m) (l₁:=B) (l₂:=n :: v :: R)).trans
      ((List.perm_middle (a:=n) (l₁:=B) (l₂:=v :: R)).cons m)
  have avoid {w : V} (e : w=x ∨ w=p) : w ∉ P.vertices := fun h =>
    e.elim ((P.covers _).mp h).1 ((P.covers _).mp h).2
  have mO : m ∉ P.vertices := avoid (ori.elim (fun h => Or.inr h.1) (fun h => Or.inl h.1))
  have nO : n ∉ P.vertices := avoid (ori.elim (fun h => Or.inl h.2) (fun h => Or.inr h.2))
  have nd : (m :: n :: P.vertices).Nodup := by simp [mn.ne,mO,nO,P.nodup]
  have cover (w : V) : w ∈ W := by
    apply perm.mem_iff.mpr
    by_cases wx : w=x
    · rcases ori with ⟨_,eq⟩|⟨eq,_⟩ <;> simp [wx,eq]
    by_cases wp : w=p
    · rcases ori with ⟨eq,_⟩|⟨_,eq⟩ <;> simp [wp,eq]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ((P.covers w).mpr ⟨wx,wp⟩))
  apply traceable_iff_hamiltonian_walk.mpr
  apply pathOn_univ_iff_hamiltonian_walk.mp
  exact ⟨⟨W,by intro h; simpa [h] using cover x,chain,perm.nodup_iff.mpr nd,
    fun w => ⟨fun _ => Set.mem_univ _,fun _ => cover w⟩⟩⟩

#print axioms traceable_of_filled_hub
end Graffiti199Depleted.Catalogue.Incomplete

