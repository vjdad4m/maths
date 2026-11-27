import CoreTransfer

open private three_names_exhaust_neighbors from DepletedFootprint

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

omit [DecidableEq V] [DecidableRel G.Adj] [Fintype V] in
theorem embed_ordinary_block (p : PathOn G {v | v ≠ z})
    (L S R : List V) (split : p.vertices = L ++ S ++ R) :
    ∃ f : Fin (S.length+1) ↪ V, f (Fin.last S.length) = z ∧ block f = S := by
  have pathNd : (L ++ S ++ R).Nodup := split ▸ p.nodup
  have nd : S.Nodup := (List.nodup_append.mp (List.nodup_append.mp pathNd).1).2.1
  have off : z ∉ S := by
    intro h
    have hz : z ∈ p.vertices := by rw [split]; simp [h]
    exact (p.covers z).mp hz rfl
  have full : (S ++ [z]).Nodup := by
    exact List.nodup_append.mpr ⟨nd,by simp,by simpa using off⟩
  let f : Fin (S.length+1) ↪ V :=
    ⟨fun i => (S ++ [z]).get (i.cast (by simp)),
      by
        intro i j e
        have eq := List.nodup_iff_injective_get.mp full e
        exact Fin.ext (congrArg (fun u : Fin (S ++ [z]).length => u.val) eq)⟩
  refine ⟨f,?_,?_⟩
  · change (S ++ [z])[S.length]'(by simp) = z
    simp
  · refine List.ext_getElem (block_length f) ?_
    intro i il ir
    let t : Fin (S.length+1) := ⟨i,by omega⟩
    rw [block_get f t ir]
    change (S ++ [z])[i]'(by simp; omega) = S[i]
    rw [List.getElem_append_left ir]

omit [DecidableRel G.Adj] [Fintype V] in
theorem extend_ends (p : PathOn G {v | v ≠ z}) (noTrace : ¬ Catalogue.Traceable G)
    {L S R : List V} (split : p.vertices = L ++ S ++ R) {a c : V}
    (head : S.head? = some a) (tail : S.getLast? = some c)
    (za : G.Adj z a) (zc : G.Adj z c) :
    ∃ U l r T, p.vertices = U ++ ([l] ++ S ++ [r]) ++ T := by
  have h := omission_constraints noTrace p
  have ln : L ≠ [] := by
    rintro rfl
    have pHead : p.vertices.head? = some a := by simp [split,List.head?_append,head]
    rw [List.head?_eq_head p.nonempty] at pHead
    have e : p.first = a := Option.some.inj pHead
    exact h.firstOff (e.symm ▸ za)
  have rn : R ≠ [] := by
    rintro rfl
    have pTail : p.vertices.getLast? = some c := by simp [split,List.getLast?_append,tail]
    rw [List.getLast?_eq_getLast p.nonempty] at pTail
    have e : p.last = c := Option.some.inj pTail
    exact h.lastOff (e.symm ▸ zc)
  have leftForm : ∃ U l, L = U ++ [l] :=
    ⟨L.dropLast,L.getLast ln,(List.dropLast_append_getLast ln).symm⟩
  obtain ⟨U,l,rfl⟩ := leftForm
  obtain ⟨r,T,rfl⟩ := List.exists_cons_of_ne_nil rn
  exact ⟨U,l,r,T,by simpa [List.append_assoc] using split⟩

omit [DecidableEq V] in
theorem cubic_slot {n : ℕ} (b : Layout n) (f : Fin (n+1) ↪ V)
    (dz : G.degree (f (Fin.last n)) = 3)
    (za : ∀ i, G.Adj (f (Fin.last n)) (f (b.port i))) {w : V}
    (zw : G.Adj (f (Fin.last n)) w) (dw : G.degree w = 3) :
    ∃ m, G.degree (f (b.port m)) = 3 := by
  obtain ⟨i,hi,eq⟩ := three_names_exhaust_neighbors f
    (b.port.injective.ne (by decide : (0 : Fin 3) ≠ 1))
    (b.port.injective.ne (by decide : (0 : Fin 3) ≠ 2))
    (b.port.injective.ne (by decide : (1 : Fin 3) ≠ 2)) dz (za 0) (za 1) (za 2) w zw
  have hm : i ∈ b.ports := hi
  obtain ⟨m,rfl⟩ := List.mem_ofFn.mp hm
  exact ⟨m,eq.symm ▸ dw⟩

end Graffiti199Depleted.WiderOmission
