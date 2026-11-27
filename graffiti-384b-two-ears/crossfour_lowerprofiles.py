"""Split an older finite table by its original outer index or indices."""

def split_table(module, source):
    if module == "LowerProfiles384b":
        return lower_profiles(source)
    indices = {"Dense33_384b": (31, 32), "Dense31Boundary384b": (29, 30)}
    if module not in indices:
        return None
    a, b = indices[module]
    start = source.index("set_option maxRecDepth")
    end = source.index("\nprivate theorem mono", start)
    options, body = source[start:end].split("private theorem rows : ", 1)
    statement, proof = body.split(" := by\n", 1)
    prefix = f"∀ h ∈ ({{{a},{b}}} : Finset ℕ), "
    assert statement.startswith(prefix)
    rows = [f"{options}private theorem checked{h} : " + statement[len(prefix):].replace("Row h f", f"Row {h} f") + " := by\n" + proof.rstrip() for h in (a, b)]
    rows.append("private theorem rows : " + statement + " := by\n  intro h hm\n  simp only [Finset.mem_insert, Finset.mem_singleton] at hm\n  rcases hm with rfl | rfl\n  · exact checked" + str(a) + "\n  · exact checked" + str(b) + "\n")
    return source[:start] + "\n\n".join(rows) + source[end:]


def lower_profiles(source):
    start = source.index("set_option maxRecDepth")
    end = source.index("\ntheorem saturated_profiles", start)
    table = source[start:end]
    options, declaration = table.split("private theorem table : ", 1)
    statement, proof = declaration.split(" := by\n", 1)
    assert statement.strip() == (
        "∀ q ∈ ({34,35} : Finset ℕ), ∀ h ∈ ({33,34} : Finset ℕ),\n"
        "    ∀ f ∈ levels.powerset, residual q h f ∨ numeric q h f"
    )
    parts = []
    for q in (34, 35):
        for h in (33, 34):
            parts.append(
                f"{options}private theorem checked{q}_{h} : "
                f"∀ f ∈ levels.powerset, residual {q} {h} f ∨ numeric {q} {h} f := by\n"
                + proof.rstrip()
            )
    parts.append(
        "private theorem table : " + statement + " := by\n"
        "  intro q qm h hm\n"
        "  simp only [Finset.mem_insert, Finset.mem_singleton] at qm hm\n"
        "  rcases qm with rfl | rfl <;> rcases hm with rfl | rfl <;>\n"
        "    first | exact checked34_33 | exact checked34_34 | exact checked35_33 | exact checked35_34\n"
    )
    return source[:start] + "\n\n".join(parts) + source[end:]

