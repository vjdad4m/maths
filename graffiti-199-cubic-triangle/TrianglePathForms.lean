import TriangleCompactLabeled
import TriangleShortLabeled
import TriangleSeparatedLabeled

open private three_names_exhaust_neighbors from DepletedFootprint

namespace Graffiti199Depleted.WiderOmission

open SimpleGraph

universe u
variable {W : Type u} {G : SimpleGraph W}
variable [DecidableEq W] [DecidableRel G.Adj] [Fintype W]
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000

omit [DecidableEq W] in
private theorem choose_triangle_port {n : ℕ} (b : Layout n) (f : Fin (n+1) ↪ W) {w : W}
    (ports : ∀ i, G.Adj (f (Fin.last n)) (f (b.port i)))
    (dz : G.degree (f (Fin.last n)) = 3) (dw : G.degree w = 3) (zw : G.Adj (f (Fin.last n)) w)
    (tri : ∀ x y, x ≠ y → x ≠ w → y ≠ w → G.Adj (f (Fin.last n)) x →
      G.Adj (f (Fin.last n)) y → G.Adj x y) :
    ∃ m : Fin 3, G.degree (f (b.port m)) = 3 ∧
      ∀ i j, i ≠ j → i ≠ m → j ≠ m → G.Adj (f (b.port i)) (f (b.port j)) := by
  obtain ⟨t,ht,eq⟩ := three_names_exhaust_neighbors f
    (b.port.injective.ne (by decide : (0 : Fin 3) ≠ 1))
    (b.port.injective.ne (by decide : (0 : Fin 3) ≠ 2))
    (b.port.injective.ne (by decide : (1 : Fin 3) ≠ 2)) dz (ports 0) (ports 1) (ports 2) w zw
  obtain ⟨m,rfl⟩ := List.mem_ofFn.mp (show t ∈ b.ports from ht)
  refine ⟨m,eq.symm ▸ dw,?_⟩
  intro i j ij im jm
  exact tri _ _ (f.injective.ne (b.port.injective.ne ij))
    (fun h => im (b.port.injective (f.injective (h.trans eq.symm))))
    (fun h => jm (b.port.injective (f.injective (h.trans eq.symm)))) (ports _) (ports _)

theorem traceable_triangle_compact_fragments (budget : Catalogue.treeNumber G ≤ 5)
    (conn : Catalogue.ConnectivityAtLeast G 3)
    {z w a x b y c : W} (p : PathOn G {v | v ≠ z}) (L R : List W)
    (split : p.vertices = L ++ ([a,x,b,y,c]) ++ R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w)
    (tri : ∀ x y, x ≠ y → x ≠ w → y ≠ w → G.Adj z x → G.Adj z y → G.Adj x y) :
    Catalogue.Traceable G := by
  classical
  by_contra noTrace
  obtain ⟨A,l,s,T,enlarged⟩ := extend_ends p noTrace split (by rfl)
    (by rfl) za zc
  have full : p.vertices = A ++ ([l,a,x,b,y,c,s]) ++ T := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using enlarged
  let D : List W := [l,a,x,b,y,c,s]
  have sub : D.Sublist p.vertices := by
    rw [full]
    have core := (List.Sublist.refl [l,a,x,b,y,c,s])
    have big := ((List.nil_sublist A).append core).append (List.nil_sublist T)
    simpa only [D,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using big
  have embed : ∃ f : Fin 8 ↪ W, f (Fin.last 7) = z ∧ block f = D :=
    embed_ordinary_sublist p D sub
  obtain ⟨f,hZ,hD⟩ := embed
  subst z
  have f0 : f 0 = l := by
    simpa only [hD] using (block_get f 0 (by change 0 < 7; decide)).symm
  have f1 : f 1 = a := by
    simpa only [hD] using (block_get f 1 (by change 1 < 7; decide)).symm
  have f2 : f 2 = x := by
    simpa only [hD] using (block_get f 2 (by change 2 < 7; decide)).symm
  have f3 : f 3 = b := by
    simpa only [hD] using (block_get f 3 (by change 3 < 7; decide)).symm
  have f4 : f 4 = y := by
    simpa only [hD] using (block_get f 4 (by change 4 < 7; decide)).symm
  have f5 : f 5 = c := by
    simpa only [hD] using (block_get f 5 (by change 5 < 7; decide)).symm
  have f6 : f 6 = s := by
    simpa only [hD] using (block_get f 6 (by change 6 < 7; decide)).symm
  have ports (i : Fin 3) : G.Adj (f (Fin.last 7)) (f (layoutTriCompact.port i)) := by
    fin_cases i
    · exact f1.symm ▸ za
    · exact f3.symm ▸ zb
    · exact f5.symm ▸ zc
  obtain ⟨m,dm,triM⟩ := choose_triangle_port layoutTriCompact f ports dz dw zw tri
  exact noTrace (traceable_triangle_compact_labeled budget conn f p (L := A) (R := T)
     (by simpa only [f0,f1,f2,f3,f4,f5,f6] using full)
    ports dz m dm triM)

theorem traceable_triangle_short_fragments (budget : Catalogue.treeNumber G ≤ 5)
    (conn : Catalogue.ConnectivityAtLeast G 3)
    {z w a x b y r c : W} (p : PathOn G {v | v ≠ z}) (L U R : List W)
    (split : p.vertices = L ++ ([a,x,b,y] ++ U ++ [r,c]) ++ R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w)
    (tri : ∀ x y, x ≠ y → x ≠ w → y ≠ w → G.Adj z x → G.Adj z y → G.Adj x y) :
    Catalogue.Traceable G := by
  classical
  by_contra noTrace
  obtain ⟨A,l,s,T,enlarged⟩ := extend_ends p noTrace split (by rfl)
    (by rw [List.getLast?_append_of_ne_nil _ (by simp : [r,c] ≠ [])]; rfl) za zc
  have full : p.vertices = A ++ ([l,a,x,b,y] ++ U ++ [r,c,s]) ++ T := by
    simpa only [List.append_assoc,List.cons_append,List.nil_append] using enlarged
  let D : List W := [l,a,x,b,y,r,c,s]
  have sub : D.Sublist p.vertices := by
    rw [full]
    have core := (((List.Sublist.refl [l,a,x,b,y])).append (List.nil_sublist U)).append (List.Sublist.refl [r,c,s])
    have big := ((List.nil_sublist A).append core).append (List.nil_sublist T)
    simpa only [D,List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using big
  have embed : ∃ f : Fin 9 ↪ W, f (Fin.last 8) = z ∧ block f = D :=
    embed_ordinary_sublist p D sub
  obtain ⟨f,hZ,hD⟩ := embed
  subst z
  have f0 : f 0 = l := by
    simpa only [hD] using (block_get f 0 (by change 0 < 8; decide)).symm
  have f1 : f 1 = a := by
    simpa only [hD] using (block_get f 1 (by change 1 < 8; decide)).symm
  have f2 : f 2 = x := by
    simpa only [hD] using (block_get f 2 (by change 2 < 8; decide)).symm
  have f3 : f 3 = b := by
    simpa only [hD] using (block_get f 3 (by change 3 < 8; decide)).symm
  have f4 : f 4 = y := by
    simpa only [hD] using (block_get f 4 (by change 4 < 8; decide)).symm
  have f5 : f 5 = r := by
    simpa only [hD] using (block_get f 5 (by change 5 < 8; decide)).symm
  have f6 : f 6 = c := by
    simpa only [hD] using (block_get f 6 (by change 6 < 8; decide)).symm
  have f7 : f 7 = s := by
    simpa only [hD] using (block_get f 7 (by change 7 < 8; decide)).symm
  have ports (i : Fin 3) : G.Adj (f (Fin.last 8)) (f (layoutTriShort.port i)) := by
    fin_cases i
    · exact f1.symm ▸ za
    · exact f3.symm ▸ zb
    · exact f6.symm ▸ zc
  obtain ⟨m,dm,triM⟩ := choose_triangle_port layoutTriShort f ports dz dw zw tri
  exact noTrace (traceable_triangle_short_labeled budget conn f p (L := A) (R := T)
    (U := U) (by simpa only [f0,f1,f2,f3,f4,f5,f6,f7] using full)
    ports dz m dm triM)

theorem traceable_triangle_separated_fragments (budget : Catalogue.treeNumber G ≤ 5)
    {z w a x q b y r c : W} (p : PathOn G {v | v ≠ z}) (L U V R : List W)
    (split : p.vertices = L ++ ([a,x] ++ U ++ [q,b,y] ++ V ++ [r,c]) ++ R)
    (za : G.Adj z a) (zb : G.Adj z b) (zc : G.Adj z c)
    (dz : G.degree z = 3) (dw : G.degree w = 3) (zw : G.Adj z w)
    (tri : ∀ x y, x ≠ y → x ≠ w → y ≠ w → G.Adj z x → G.Adj z y → G.Adj x y) :
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
    have core := (((((List.Sublist.refl [l,a,x])).append (List.nil_sublist U)).append (List.Sublist.refl [q,b,y])).append (List.nil_sublist V)).append (List.Sublist.refl [r,c,s])
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
  have ports (i : Fin 3) : G.Adj (f (Fin.last 9)) (f (layoutTriSeparated.port i)) := by
    fin_cases i
    · exact f1.symm ▸ za
    · exact f4.symm ▸ zb
    · exact f7.symm ▸ zc
  obtain ⟨m,dm,triM⟩ := choose_triangle_port layoutTriSeparated f ports dz dw zw tri
  exact noTrace (traceable_triangle_separated_labeled budget f p (L := A) (R := T)
    (U := U) (V := V) (by simpa only [f0,f1,f2,f3,f4,f5,f6,f7,f8] using full)
    ports dz m dm triM)

#print axioms traceable_triangle_compact_fragments
#print axioms traceable_triangle_short_fragments
#print axioms traceable_triangle_separated_fragments

end Graffiti199Depleted.WiderOmission
