import TinyFourOrder14OneModel

namespace FourOrder14One
open Finset

theorem baseEdge_mono (i j : ℕ) (m : Marks) (e f g h t : Bool) (u v : Vertex)
    (H : edge i j m false false false false false u v=true) :
      edge i j m e f g h t u v=true := by
  unfold edge dir at H ⊢
  simp only [Bool.and_false, Bool.or_false] at H
  simp only [Bool.or_eq_true] at H ⊢
  tauto

theorem endpointEdges (i j : ℕ) (ip : 1≤i) (sep : i+3≤j) (jp : j≤11)
    (m : Marks) (e f g h t : Bool) (u v : Vertex)
    (eu : u=0 ∨ u=12) :
    edge i j m e f g h t u v=edge i j m false false false false false u v := by
  have z : (0:Vertex).val=0 := rfl
  have zt : (12:Vertex).val=12 := rfl
  have zi : 0≠i := by omega
  have zj : 0≠j := by omega
  have zjm : 0≠j-1 := by omega
  have zjp : 0≠j+1 := by omega
  have zip : 0≠i+1 := by omega
  have ti : 12≠i := by omega
  have tj : 12≠j := by omega
  have tim : 12≠i-1 := by omega
  have tip : 12≠i+1 := by omega
  have tjm : 12≠j-1 := by omega
  rcases eu with a|a <;> subst u
  · by_cases q : i=1
    · simp [edge,dir,z,zi,zj,zjm,zjp,zip,q]
    · have zim : 0≠i-1 := by omega
      simp [edge,dir,z,zi,zj,zjm,zjp,zip,q,zim]
  · by_cases q : j=11
    · simp [edge,dir,zt,ti,tj,tim,tip,tjm,q]
    · have tjp : 12≠j+1 := by omega
      simp [edge,dir,zt,ti,tj,tim,tip,tjm,q,tjp]

theorem baseD2_subset (i j : ℕ) (ip : 1≤i) (sep : i+3≤j) (jp : j≤11)
    (m : Marks) (e f g h t : Bool) (u : Vertex) (hu : u=0 ∨ u=12) :
    d2Set i j m false false false false false u ⊆ d2Set i j m e f g h t u := by
  intro v H
  obtain ⟨hne,hn,w,uw,wv⟩ := (mem_filter.mp H).2
  refine mem_filter.mpr ⟨mem_univ _,hne,?_,w,baseEdge_mono i j m e f g h t u w uw,
    baseEdge_mono i j m e f g h t w v wv⟩
  rwa [endpointEdges i j ip sep jp m e f g h t u v hu]

#print axioms baseD2_subset
end FourOrder14One
