import Conclusion23

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

/-- The specified two gaps between visits to the independent neighbors
of an omitted cubic vertex with a cubic neighbor force traceability. -/
theorem traceable_of_gaps_two_three (budget : Catalogue.treeNumber G ≤ 5)
    {z w a x b y v c : V}
    (p : PathOn G {v | v ≠ z}) (L R : List V)
    (split : p.vertices = L ++ [a,x,b,y,v,c] ++ R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (ab : ¬ G.Adj a b) (ac : ¬ G.Adj a c) (bc : ¬ G.Adj b c)
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w) :
    Catalogue.Traceable G := by
  classical
  by_contra noTrace
  obtain ⟨U,l,r,T,extended⟩ := extend_ends p noTrace split (by rfl) (by rfl) za zc
  let S : List V := [l,a,x,b,y,v,c,r]
  have seg : p.vertices = U ++ S ++ T := extended
  obtain ⟨f,hz,hb⟩ := embed_ordinary_block p U S T seg
  subst z
  have fa : f (layout23.port 0) = a := by
    simpa only [hb] using (block_get f (layout23.port 0) (by change 1 < 8; decide)).symm
  have fb : f (layout23.port 1) = b := by
    simpa only [hb] using (block_get f (layout23.port 1) (by change 3 < 8; decide)).symm
  have fc : f (layout23.port 2) = c := by
    simpa only [hb] using (block_get f (layout23.port 2) (by change 6 < 8; decide)).symm
  have ports (i : Fin 3) : G.Adj (f (Fin.last 8)) (f (layout23.port i)) := by
    fin_cases i
    · exact fa.symm ▸ za
    · exact fb.symm ▸ zb
    · exact fc.symm ▸ zc
  have e01 : ¬ G.Adj (f (layout23.port 0)) (f (layout23.port 1)) := by rw [fa,fb]; exact ab
  have e02 : ¬ G.Adj (f (layout23.port 0)) (f (layout23.port 2)) := by rw [fa,fc]; exact ac
  have e12 : ¬ G.Adj (f (layout23.port 1)) (f (layout23.port 2)) := by rw [fb,fc]; exact bc
  have independent (i j : Fin 3) : ¬ G.Adj (f (layout23.port i)) (f (layout23.port j)) := by
    fin_cases i <;> fin_cases j <;> first
    | exact G.loopless _
    | exact e01
    | exact e02
    | exact e12
    | exact fun h => e01 h.symm
    | exact fun h => e02 h.symm
    | exact fun h => e12 h.symm
  have cubic := cubic_slot layout23 f dz ports zw dw
  exact noTrace (traceable_of_layout23 budget f p (by simpa only [hb] using seg) ports independent dz cubic)

#print axioms traceable_of_gaps_two_three

/-- The same exclusion with the longer gap first on the original path. -/
theorem traceable_of_gaps_three_two (budget : Catalogue.treeNumber G ≤ 5)
    {z w a x b y v c : V}
    (p : PathOn G {v | v ≠ z}) (L R : List V)
    (split : p.vertices = L ++ [c,v,y,b,x,a] ++ R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (ab : ¬ G.Adj a b) (ac : ¬ G.Adj a c) (bc : ¬ G.Adj b c)
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w) :
    Catalogue.Traceable G := by
  have flip : p.rev.vertices = R.reverse ++ [a,x,b,y,v,c] ++ L.reverse := by
    change p.vertices.reverse = _
    rw [split]
    simp [List.reverse_append,List.reverse_cons,List.append_assoc]
  exact traceable_of_gaps_two_three budget p.rev R.reverse L.reverse flip za zb zc ab ac bc dz dw zw

#print axioms traceable_of_gaps_three_two

end Graffiti199Depleted.WiderOmission
