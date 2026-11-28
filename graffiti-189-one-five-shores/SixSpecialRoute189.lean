import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph Finset
variable {V : Type*} {G : SimpleGraph V} [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
set_option linter.unusedSectionVars false

/-- Four singles may miss at most one edge each among the six vertices.
If each special vertex sees a single, the six-set has a spanning
path with the two special vertices as endpoints. -/
theorem six_route_with_two_special_terminals
    (A : Finset V) (four : A.card=4) {m n : V} (mn : m≠n)
    (mA : m∉A) (nA : n∉A)
    (dense : ∀ u∈A,∀ v ∈ insert m (insert n A),∀ w∈insert m (insert n A),
      u≠v → u≠w → ¬G.Adj u v → ¬G.Adj u w → v=w)
    (mh : ∃ u∈A,G.Adj m u) (nh : ∃ v∈A,G.Adj n v) :
    RouteOn G (insert m (insert n A)) m n := by
  classical
  have outer {u v : V} (ua : u∈A) (va : v∈A) (uv : u≠v) (no : ¬G.Adj u v) :
      G.Adj m u ∧ G.Adj n u := by
    have m_ne : u≠m := fun h=>mA (h ▸ ua)
    have n_ne : u≠n := fun h=>nA (h ▸ ua)
    have vm : v≠m := fun h=>mA (h ▸ va)
    have vn : v≠n := fun h=>nA (h ▸ va)
    constructor
    · by_contra! h
      exact vm (dense u ua v (by simp [va]) m (by simp) uv m_ne no (fun e=>h e.symm))
    by_contra! h
    exact vn (dense u ua v (by simp [va]) n (by simp) uv n_ne no (fun e=>h e.symm))
  have pack {u v : V} (p : RouteOn G A u v) (mu : G.Adj m u) (nv : G.Adj n v) :
      RouteOn G (insert m (insert n A)) m n := by
    have q := (p.prefix mu mA).suffix nv.symm (by simp [mn.symm,nA])
    rw [insert_comm]
    exact q
  by_cases complete : CompleteOn G A
  · obtain ⟨u,ua,mu⟩ := mh
    obtain ⟨v,va,nv⟩ := nh
    by_cases uv : u=v
    · obtain ⟨w,wa,wu⟩ : ∃ w∈A,w≠u := by
        apply Classical.byContradiction
        intro h
        have sub : A⊆{u} := fun w wa=>mem_singleton.mpr
          (Classical.byContradiction (fun t=>h ⟨w,wa,t⟩))
        have c := card_le_card sub
        simp [four] at c
      have wBoth : G.Adj m w ∨ G.Adj n w := by
        apply Classical.byContradiction
        intro no
        exact mn (dense w wa m (by simp) n (by simp)
          (fun h=>mA (h ▸ wa)) (fun h=>nA (h ▸ wa))
          (fun e=>no (.inl e.symm)) (fun e=>no (.inr e.symm)))
      rcases wBoth with mw|nw
      · have wv : w≠v := fun h=>wu (h.trans uv.symm)
        obtain ⟨p,pp,ps⟩ := path_between_in_clique A complete wa va wv
        exact pack ⟨p,pp,ps⟩ mw nv
      obtain ⟨p,pp,ps⟩ := path_between_in_clique A complete ua wa wu.symm
      exact pack ⟨p,pp,ps⟩ mu nw
    obtain ⟨p,pp,ps⟩ := path_between_in_clique A complete ua va uv
    exact pack ⟨p,pp,ps⟩ mu nv
  have missing : ∃ u∈A,∃ v∈A,u≠v ∧ ¬G.Adj u v := by
    apply Classical.byContradiction
    intro h
    apply complete
    intro u ua v va uv
    exact Classical.byContradiction (fun no=>h ⟨u,ua,v,va,uv,no⟩)
  obtain ⟨u,ua,v,va,uv,no⟩ := missing
  let B := (A.erase u).erase v
  have b2 : B.card=2 := by
    change ((A.erase u).erase v).card=2
    rw [card_erase_of_mem (mem_erase.mpr ⟨uv.symm,va⟩),card_erase_of_mem ua,four]
  obtain ⟨w,z,wz,be⟩ := card_eq_two.mp b2
  have wB : w∈B := by simp [be]
  have zB : z∈B := by simp [be]
  have wa : w∈A := mem_of_mem_erase (mem_of_mem_erase wB)
  have za : z∈A := mem_of_mem_erase (mem_of_mem_erase zB)
  have wu : w≠u := (mem_erase.mp (mem_of_mem_erase wB)).1
  have wv : w≠v := (mem_erase.mp wB).1
  have zu : z≠u := (mem_erase.mp (mem_of_mem_erase zB)).1
  have zv : z≠v := (mem_erase.mp zB).1
  have uw : G.Adj u w := Classical.byContradiction (fun e=>wv
    (dense u ua w (by simp [wa]) v (by simp [va]) wu.symm uv e no))
  have uz : G.Adj u z := Classical.byContradiction (fun e=>zv
    (dense u ua z (by simp [za]) v (by simp [va]) zu.symm uv e no))
  have vw : G.Adj v w := Classical.byContradiction (fun e=>wu
    (dense v va w (by simp [wa]) u (by simp [ua]) wv.symm uv.symm e (fun h=>no h.symm)))
  have vz : G.Adj v z := Classical.byContradiction (fun e=>zu
    (dense v va z (by simp [za]) u (by simp [ua]) zv.symm uv.symm e (fun h=>no h.symm)))
  have aeq : insert u (insert v B)=A := by
    change insert u (insert v ((A.erase u).erase v))=A
    rw [insert_erase (mem_erase.mpr ⟨uv.symm,va⟩),insert_erase ua]
  by_cases edge : G.Adj w z
  · have p := (RouteOn.three uw edge zu.symm).suffix vz.symm (by simp [uv.symm,wv.symm,zv.symm])
    have eq : insert v ({u,w,z} : Finset V)=A := by
      rw [←aeq,be]
      ext t
      simp [or_comm,or_left_comm,or_assoc]
    exact pack (eq ▸ p) (outer ua va uv no).1 (outer va ua uv.symm (fun h=>no h.symm)).2
  have p := (RouteOn.three uz vz.symm uv).suffix vw (by simp [wu,wz,wv])
  have eq : insert w ({u,z,v} : Finset V)=A := by
    rw [←aeq,be]
    ext t
    simp [or_comm,or_left_comm,or_assoc]
  exact pack (eq ▸ p) (outer ua va uv no).1 (outer wa za wz edge).2

#print axioms six_route_with_two_special_terminals
end Graffiti189LongestPath.CrossSaturation
