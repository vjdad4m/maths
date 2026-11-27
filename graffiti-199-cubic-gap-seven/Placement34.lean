import Conclusion34

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}
variable [DecidableEq V] [DecidableRel G.Adj] [Fintype V]

/-- The specified two gaps between visits to the independent neighbors
of an omitted cubic vertex with a cubic neighbor force traceability. -/
theorem traceable_of_gaps_three_four (budget : Catalogue.treeNumber G ≤ 5)
    {z w a x y b u v t c : V}
    (p : PathOn G {v | v ≠ z}) (L R : List V)
    (split : p.vertices = L ++ [a,x,y,b,u,v,t,c] ++ R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (ab : ¬ G.Adj a b) (ac : ¬ G.Adj a c) (bc : ¬ G.Adj b c)
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w) :
    Catalogue.Traceable G := by
  classical
  by_contra noTrace
  obtain ⟨U,l,r,T,extended⟩ := extend_ends p noTrace split (by rfl) (by rfl) za zc
  let S : List V := [l,a,x,y,b,u,v,t,c,r]
  have seg : p.vertices = U ++ S ++ T := extended
  obtain ⟨f,hz,hb⟩ := embed_ordinary_block p U S T seg
  subst z
  have fa : f (layout34.port 0) = a := by
    simpa only [hb] using (block_get f (layout34.port 0) (by change 1 < 10; decide)).symm
  have fb : f (layout34.port 1) = b := by
    simpa only [hb] using (block_get f (layout34.port 1) (by change 4 < 10; decide)).symm
  have fc : f (layout34.port 2) = c := by
    simpa only [hb] using (block_get f (layout34.port 2) (by change 8 < 10; decide)).symm
  have ports (i : Fin 3) : G.Adj (f (Fin.last 10)) (f (layout34.port i)) := by
    fin_cases i
    · exact fa.symm ▸ za
    · exact fb.symm ▸ zb
    · exact fc.symm ▸ zc
  have e01 : ¬ G.Adj (f (layout34.port 0)) (f (layout34.port 1)) := by rw [fa,fb]; exact ab
  have e02 : ¬ G.Adj (f (layout34.port 0)) (f (layout34.port 2)) := by rw [fa,fc]; exact ac
  have e12 : ¬ G.Adj (f (layout34.port 1)) (f (layout34.port 2)) := by rw [fb,fc]; exact bc
  have independent (i j : Fin 3) : ¬ G.Adj (f (layout34.port i)) (f (layout34.port j)) := by
    fin_cases i <;> fin_cases j <;> first
    | exact G.loopless _
    | exact e01
    | exact e02
    | exact e12
    | exact fun h => e01 h.symm
    | exact fun h => e02 h.symm
    | exact fun h => e12 h.symm
  have cubic := cubic_slot layout34 f dz ports zw dw
  exact noTrace (traceable_of_layout34 budget f p (by simpa only [hb] using seg) ports independent dz cubic)

#print axioms traceable_of_gaps_three_four


/-- The same exclusion with the longer gap first. -/
theorem traceable_of_gaps_four_three (budget : Catalogue.treeNumber G ≤ 5)
    {z w a x y b u v t c : V}
    (p : PathOn G {v | v ≠ z}) (L R : List V)
    (split : p.vertices = L ++ [c,t,v,u,b,y,x,a] ++ R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (ab : ¬ G.Adj a b) (ac : ¬ G.Adj a c) (bc : ¬ G.Adj b c)
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w) :
    Catalogue.Traceable G := by
  have flip : p.rev.vertices = R.reverse ++ [a,x,y,b,u,v,t,c] ++ L.reverse := by
    change p.vertices.reverse = _
    rw [split]
    simp [List.reverse_append,List.reverse_cons,List.append_assoc]
  exact traceable_of_gaps_three_four budget p.rev R.reverse L.reverse flip za zb zc ab ac bc dz dw zw

#print axioms traceable_of_gaps_four_three

end Graffiti199Depleted.WiderOmission
