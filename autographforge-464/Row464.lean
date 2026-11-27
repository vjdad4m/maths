import Drawing

open SimpleGraph HallRainbow1121
namespace PlanarRainbow464

/-- The entire connected planar bipartite family, with both optimizers attained. -/
theorem family {m : ℕ} (hm : 2 ≤ m) :
    Fintype.card (V m) = 3*m+2 ∧ (graph m).Connected ∧ (graph m).Colorable 2 ∧
    (graph m).CliqueFree 4 ∧ Planar (graph m) ∧
    vertexCliqueCover (graph m) = 2*m ∧ rainbowNumber (graph m) 3 = m+2 :=
  ⟨order m,connected (by omega),bipartite m,k4free m,planar m,cover_exact hm,rainbow_exact hm⟩

theorem unbounded (d : ℕ) : ∃ (U : Type) (_ : Fintype U) (G : SimpleGraph U),
    G.Connected ∧ G.Colorable 2 ∧ G.CliqueFree 4 ∧ Planar G ∧
    vertexCliqueCover G = rainbowNumber G 3 + d := by
  let m := d+2
  obtain ⟨_,hc,hb,h4,hp,cover,rain⟩ := family (m:=m) (by dsimp [m]; omega)
  exact ⟨V m,inferInstance,graph m,hc,hb,h4,hp,by rw [cover,rain]; dsimp [m]; omega⟩

/-- Each member attains the value in the sharp bipartite-planar counting bound. -/
theorem sharp_value {m : ℕ} (hm : 2 ≤ m) :
    vertexCliqueCover (graph m) = rainbowNumber (graph m) 3 + (rainbowNumber (graph m) 3-4) := by
  rw [cover_exact hm,rainbow_exact hm]
  omega

/-- Physical row 464, generated ID f488855f. -/
theorem row464_false : ¬ (∀ (U : Type) [Fintype U] (G : SimpleGraph U),
    2 ≤ Fintype.card U → G.CliqueFree 4 → Planar G →
    vertexCliqueCover G ≤ rainbowNumber G 3) := by
  intro claim
  obtain ⟨size,_,_,h4,hp,cover,rain⟩ := family (m:=3) (by decide)
  have impossible := claim (V 3) (graph 3) (by omega) h4 hp
  rw [cover,rain] at impossible
  omega

#print axioms planar
#print axioms cover_exact
#print axioms rainbow_exact
#print axioms sharp_value
#print axioms family
#print axioms unbounded
#print axioms row464_false
end PlanarRainbow464
