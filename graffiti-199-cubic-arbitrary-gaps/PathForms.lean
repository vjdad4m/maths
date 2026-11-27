import LabeledClosure

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

universe u
variable {W : Type u} {G : SimpleGraph W}
variable [DecidableEq W] [DecidableRel G.Adj] [Fintype W]

set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

theorem traceable_of_separated_fragments (budget : Catalogue.treeNumber G ≤ 5)
    {z w a x q b y r c : W}
    (p : PathOn G {v | v ≠ z}) (L U V R : List W)
    (split : p.vertices = L ++ ([a,x] ++ U ++ [q,b,y] ++ V ++ [r,c]) ++ R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (ab : ¬ G.Adj a b) (ac : ¬ G.Adj a c) (bc : ¬ G.Adj b c)
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w) :
    Catalogue.Traceable G := by
  classical
  by_contra noTrace
  obtain ⟨A,l,s,T,enlarged⟩ := extend_ends p noTrace split (by rfl)
    (by rw [List.getLast?_append_of_ne_nil _ (by simp : [r,c] ≠ [])]; rfl) za zc
  have full : p.vertices = A ++ ([l,a,x] ++ U ++ [q,b,y] ++ V ++ [r,c,s]) ++ T := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using enlarged
  let D : List W := [l,a,x,q,b,y,r,c,s]
  have sub : D.Sublist p.vertices := by
    rw [full]
    have core := (((((List.Sublist.refl [l,a,x]).append (List.nil_sublist U)).append (List.Sublist.refl [q,b,y])).append (List.nil_sublist V)).append (List.Sublist.refl [r,c,s]))
    have big := ((List.nil_sublist A).append core).append (List.nil_sublist T)
    simpa only [D,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using big
  have embed : ∃ f : Fin 10 ↪ W, f (Fin.last 9) = z ∧ block f = D :=
    embed_ordinary_sublist p D sub
  obtain ⟨f,hZ,hD⟩ := embed
  subst z
  have f0 : f 0 = l := by
    simpa only [hD] using (block_get f 0 (by change 0 < 9; decide)).symm
  have f1 : f 1 = a := by
    simpa only [hD] using (block_get f 1 (by change 1 < 9; decide)).symm
  have f2 : f 2 = x := by
    simpa only [hD] using (block_get f 2 (by change 2 < 9; decide)).symm
  have f3 : f 3 = q := by
    simpa only [hD] using (block_get f 3 (by change 3 < 9; decide)).symm
  have f4 : f 4 = b := by
    simpa only [hD] using (block_get f 4 (by change 4 < 9; decide)).symm
  have f5 : f 5 = y := by
    simpa only [hD] using (block_get f 5 (by change 5 < 9; decide)).symm
  have f6 : f 6 = r := by
    simpa only [hD] using (block_get f 6 (by change 6 < 9; decide)).symm
  have f7 : f 7 = c := by
    simpa only [hD] using (block_get f 7 (by change 7 < 9; decide)).symm
  have f8 : f 8 = s := by
    simpa only [hD] using (block_get f 8 (by change 8 < 9; decide)).symm
  have ports (i : Fin 3) : G.Adj (f (Fin.last 9)) (f (layoutSeparated.port i)) := by
    fin_cases i
    · exact f1.symm ▸ za
    · exact f4.symm ▸ zb
    · exact f7.symm ▸ zc
  have hAB : ¬ G.Adj (f (layoutSeparated.port 0)) (f (layoutSeparated.port 1)) := by
    change ¬ G.Adj (f 1) (f 4)
    rwa [f1,f4]
  have hAC : ¬ G.Adj (f (layoutSeparated.port 0)) (f (layoutSeparated.port 2)) := by
    change ¬ G.Adj (f 1) (f 7)
    rwa [f1,f7]
  have hBC : ¬ G.Adj (f (layoutSeparated.port 1)) (f (layoutSeparated.port 2)) := by
    change ¬ G.Adj (f 4) (f 7)
    rwa [f4,f7]
  have ind (i j : Fin 3) : ¬ G.Adj (f (layoutSeparated.port i)) (f (layoutSeparated.port j)) := by
    fin_cases i <;> fin_cases j <;> first
    | exact G.loopless _
    | exact hAB
    | exact hAC
    | exact hBC
    | exact fun h => hAB h.symm
    | exact fun h => hAC h.symm
    | exact fun h => hBC h.symm
  have cubic := cubic_slot layoutSeparated f dz ports zw dw
  exact noTrace (traceable_separated_labeled budget f p (L := A) (R := T)
    (U := U) (V := V) (by simpa only [f0,f1,f2,f3,f4,f5,f6,f7,f8] using full)
    ports ind dz cubic)

#print axioms traceable_of_separated_fragments
theorem traceable_of_short_fragments (budget : Catalogue.treeNumber G ≤ 5)
    (smaller : Catalogue.SmallerAtThree.{u} (Fintype.card W))
    (conn : Catalogue.ConnectivityAtLeast G 3) (cross : CrossingBetweenSurvivingEdges G)
    {z w a x b u v r c : W}
    (p : PathOn G {v | v ≠ z}) (L U R : List W)
    (split : p.vertices = L ++ ([a,x,b,u,v] ++ U ++ [r,c]) ++ R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (ab : ¬ G.Adj a b) (ac : ¬ G.Adj a c) (bc : ¬ G.Adj b c)
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w) :
    Catalogue.Traceable G := by
  classical
  by_contra noTrace
  obtain ⟨A,l,s,T,enlarged⟩ := extend_ends p noTrace split (by rfl)
    (by rw [List.getLast?_append_of_ne_nil _ (by simp : [r,c] ≠ [])]; rfl) za zc
  have full : p.vertices = A ++ ([l,a,x,b,u,v] ++ U ++ [r,c,s]) ++ T := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using enlarged
  let D : List W := [l,a,x,b,u,v,r,c,s]
  have sub : D.Sublist p.vertices := by
    rw [full]
    have core := (((List.Sublist.refl [l,a,x,b,u,v]).append (List.nil_sublist U)).append (List.Sublist.refl [r,c,s]))
    have big := ((List.nil_sublist A).append core).append (List.nil_sublist T)
    simpa only [D,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using big
  have embed : ∃ f : Fin 10 ↪ W, f (Fin.last 9) = z ∧ block f = D :=
    embed_ordinary_sublist p D sub
  obtain ⟨f,hZ,hD⟩ := embed
  subst z
  have f0 : f 0 = l := by
    simpa only [hD] using (block_get f 0 (by change 0 < 9; decide)).symm
  have f1 : f 1 = a := by
    simpa only [hD] using (block_get f 1 (by change 1 < 9; decide)).symm
  have f2 : f 2 = x := by
    simpa only [hD] using (block_get f 2 (by change 2 < 9; decide)).symm
  have f3 : f 3 = b := by
    simpa only [hD] using (block_get f 3 (by change 3 < 9; decide)).symm
  have f4 : f 4 = u := by
    simpa only [hD] using (block_get f 4 (by change 4 < 9; decide)).symm
  have f5 : f 5 = v := by
    simpa only [hD] using (block_get f 5 (by change 5 < 9; decide)).symm
  have f6 : f 6 = r := by
    simpa only [hD] using (block_get f 6 (by change 6 < 9; decide)).symm
  have f7 : f 7 = c := by
    simpa only [hD] using (block_get f 7 (by change 7 < 9; decide)).symm
  have f8 : f 8 = s := by
    simpa only [hD] using (block_get f 8 (by change 8 < 9; decide)).symm
  have ports (i : Fin 3) : G.Adj (f (Fin.last 9)) (f (layoutShort.port i)) := by
    fin_cases i
    · exact f1.symm ▸ za
    · exact f3.symm ▸ zb
    · exact f7.symm ▸ zc
  have hAB : ¬ G.Adj (f (layoutShort.port 0)) (f (layoutShort.port 1)) := by
    change ¬ G.Adj (f 1) (f 3)
    rwa [f1,f3]
  have hAC : ¬ G.Adj (f (layoutShort.port 0)) (f (layoutShort.port 2)) := by
    change ¬ G.Adj (f 1) (f 7)
    rwa [f1,f7]
  have hBC : ¬ G.Adj (f (layoutShort.port 1)) (f (layoutShort.port 2)) := by
    change ¬ G.Adj (f 3) (f 7)
    rwa [f3,f7]
  have ind (i j : Fin 3) : ¬ G.Adj (f (layoutShort.port i)) (f (layoutShort.port j)) := by
    fin_cases i <;> fin_cases j <;> first
    | exact G.loopless _
    | exact hAB
    | exact hAC
    | exact hBC
    | exact fun h => hAB h.symm
    | exact fun h => hAC h.symm
    | exact fun h => hBC h.symm
  have cubic := cubic_slot layoutShort f dz ports zw dw
  exact noTrace (traceable_short_labeled budget f smaller conn cross p (L := A) (R := T)
    (U := U) (by simpa only [f0,f1,f2,f3,f4,f5,f6,f7,f8] using full)
    ports ind dz cubic)

#print axioms traceable_of_short_fragments

end Graffiti199Depleted.WiderOmission
