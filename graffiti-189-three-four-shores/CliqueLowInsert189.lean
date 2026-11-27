import TerminalOreClosure189
import DegreeFiveRouteBasic189

namespace Graffiti189LongestPath.CrossSaturation
open SimpleGraph SimpleGraph.Walk Finset
variable {V : Type*} [Fintype V] [DecidableEq V] {J : SimpleGraph V} [DecidableRel J.Adj]
set_option linter.unusedSectionVars false

/-- In a high clique with one extra vertex z, any two chosen endpoints
avoid obstruction as long as they are not precisely the selected two
neighbors of z. -/
theorem clique_path_via_low
    (H : SimpleGraph V) (A : Finset V) (complete : CompleteOn H A)
    {z x t u v : V} (zn : z∉A)
    (xa : x∈A) (ta : t∈A) (xt : x≠t) (ua : u∈A) (va : v∈A)
    (uv : u≠v) (zu : H.Adj z u) (zv : H.Adj z v)
    (different : ¬((x=u ∧ t=v) ∨ (x=v ∧ t=u))) :
    RouteOn H (insert z A) x t := by
  classical
  have orient {x t q r : V} (xa : x∈A) (ta : t∈A) (xt : x≠t) (qa : q∈A) (ra : r∈A) (qr : q≠r)
      (zq : H.Adj z q) (zr : H.Adj z r) (qT : q≠t) (rT : r≠t) :
      RouteOn H (insert z A) x t := by
    by_cases xq : x=q
    · have xtDiff : x≠r := fun e=>qr (xq.symm.trans e)
      have sub : CompleteOn H (A.erase x) := by
        intro a ma b mb ab
        exact complete a (mem_of_mem_erase ma) b (mem_of_mem_erase mb) ab
      have rr : r∈A.erase x := mem_erase.mpr ⟨xtDiff.symm,ra⟩
      have tt : t∈A.erase x := mem_erase.mpr ⟨xt.symm,ta⟩
      obtain ⟨p,pp,ps⟩ := path_between_in_clique _ sub rr tt rT
      have P : RouteOn H (A.erase x) r t := ⟨p,pp,ps⟩
      have zx : H.Adj z x := xq.symm ▸ zq
      have full := (P.prefix zr (fun h=>zn (mem_of_mem_erase h))).prefix zx.symm
        (by simp [show x≠z from fun h=>zn (h ▸ xa)])
      have eq : insert x (insert z (A.erase x))=insert z A := by
        rw [insert_comm x z,insert_erase xa]
      exact eq ▸ full
    let S := (A.erase r).erase t
    have sx : x∈A.erase r ∨ x=r := by
      by_cases h : x=r
      · exact .inr h
      exact .inl (mem_erase.mpr ⟨h,xa⟩)
    rcases sx with h|h
    · have xs : x∈S := mem_erase.mpr ⟨xt,h⟩
      have qs : q∈S := mem_erase.mpr ⟨qT,mem_erase.mpr ⟨qr,qa⟩⟩
      have sub : CompleteOn H S := by
        intro a aS b bS ab
        exact complete a (mem_of_mem_erase (mem_of_mem_erase aS))
          b (mem_of_mem_erase (mem_of_mem_erase bS)) ab
      obtain ⟨p,pp,ps⟩ := path_between_in_clique S sub xs qs xq
      have P : RouteOn H S x q := ⟨p,pp,ps⟩
      have notZ : z∉S := fun h=>zn (mem_of_mem_erase (mem_of_mem_erase h))
      have notR : r∉S := fun h=>(mem_erase.mp (mem_of_mem_erase h)).1 rfl
      have tr : t≠z := fun e=>zn (e ▸ ta)
      have notT : t∉S := by simp [S]
      have full := ((P.suffix zq.symm notZ).suffix zr
        (by simp [show r≠z from fun e=>zn (e ▸ ra),notR])).suffix
          (complete r ra t ta rT) (by simp [rT.symm,tr,notT])
      have eq : insert t (insert r (insert z S))=insert z A := by
        have er : insert t S=A.erase r := insert_erase (mem_erase.mpr ⟨rT.symm,ta⟩)
        have all : insert r (insert t S)=A := by rw [er,insert_erase ra]
        rw [←all]
        ext w
        simp [or_comm,or_left_comm,or_assoc]
      exact eq ▸ full
    -- If x=r, use the first orientation with q/r exchanged, directly.
    have xR : x=r := h
    have xqne : x≠q := fun e=>qr (e.symm.trans xR)
    have sub : CompleteOn H (A.erase x) := by
      intro a ma b mb ab
      exact complete a (mem_of_mem_erase ma) b (mem_of_mem_erase mb) ab
    have qq : q∈A.erase x := mem_erase.mpr ⟨xqne.symm,qa⟩
    have tt : t∈A.erase x := mem_erase.mpr ⟨xt.symm,ta⟩
    obtain ⟨p,pp,ps⟩ := path_between_in_clique _ sub qq tt qT
    have P : RouteOn H (A.erase x) q t := ⟨p,pp,ps⟩
    have zx : H.Adj z x := xR.symm ▸ zr
    have full := (P.prefix zq (fun h=>zn (mem_of_mem_erase h))).prefix zx.symm
      (by simp [show x≠z from fun h=>zn (h ▸ xa)])
    have eq : insert x (insert z (A.erase x))=insert z A := by
      rw [insert_comm x z,insert_erase xa]
    exact eq ▸ full
  by_cases tu : t=u
  · have nxv : x≠v := fun e=>different (.inr ⟨e,tu⟩)
    exact (orient ta xa xt.symm ua va uv zu zv (fun e=>xt (e.symm.trans tu.symm)) nxv.symm).reverse
  by_cases tv : t=v
  · have nxu : x≠u := fun e=>different (.inl ⟨e,tv⟩)
    exact (orient ta xa xt.symm ua va uv zu zv nxu.symm (fun e=>xt (e.symm.trans tv.symm))).reverse
  exact orient xa ta xt ua va uv zu zv (fun e=>tu e.symm) (fun e=>tv e.symm)

#print axioms clique_path_via_low
end Graffiti189LongestPath.CrossSaturation
