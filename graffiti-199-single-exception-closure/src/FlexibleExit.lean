import ThreeNeighborRoute
namespace Graffiti199Depleted.Catalogue.Incomplete
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V]
variable {X H : Set V} {z r a b x : V}

/-- In the three-clique case, flexibly routing from a single touching nonneighbor
to the other available contacts suffices. Three-connectivity supplies such a second contact. -/
theorem ThreeCliques.traceable_of_flexible_exit (C : ThreeCliques G H) (F : SingletonCut G X z r a b)
    (sub : H ⊆ X) (on : ∀ v ∈ H, G.Adj r v) (xX : x ∈ X) (rx : ¬ G.Adj r x)
    (touch : ∃ h ∈ H, G.Adj x h)
    (routes : ∀ t ∉ insert r H, t ≠ x → (∃ h ∈ H, G.Adj t h) →
      Traverses G (insert r H)ᶜ x t) : Traceable G := by
  classical
  obtain ⟨v,vH,xv⟩ := touch
  obtain ⟨i,vi⟩ := (C.cover _).mp vH
  have zr := (F.cut.2 r).mpr (by simp)
  have zx : z ≠ x := fun e => F.zX (e.symm ▸ xX)
  have xr : x ≠ r := fun e => F.offX r (by simp) (e ▸ xX)
  let D : Finset V := {r,x}
  have vh : v ∉ D := by
    simp only [D,Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨(on _ vH).ne.symm,xv.ne.symm⟩
  have zh : z ∉ D := by simp [D,zr.ne,zx]
  obtain ⟨walk⟩ := (F.conn.2 D (by simp [D,xr.symm])).preconnected ⟨v,vh⟩ ⟨z,zh⟩
  obtain ⟨w,wh,t,th,wt⟩ := crossingOnWalk (U := {v : Survives D | v.val ∈ H}) walk vH
    (fun h => F.zX (sub h))
  have edge : G.Adj w.val t.val := wt
  have tr : t.val ≠ r := fun e => t.property (by simp [D,e])
  have tx : t.val ≠ x := fun e => t.property (by simp [D,e])
  obtain ⟨j,wj⟩ := (C.cover _).mp wh
  have core := routes t.val (fun h => h.elim tr th) tx ⟨w.val,wh,edge.symm⟩
  by_cases same : i = j
  · obtain ⟨k,ki,all⟩ := C.complete_to_another F sub on xX rx vi xv
    obtain ⟨u,uk⟩ := C.nonempty k
    exact C.splice F sub on core (fun e => ki (e.trans same.symm)) uk wj (all _ uk).symm edge.symm
  · exact C.splice F sub on core same vi wj xv.symm edge.symm

end Graffiti199Depleted.Catalogue.Incomplete
