import Mathlib
import PEqualNP.Defs

theorem mask14500150567228511850_upper : (PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 8 => (14500150567228511850 : ℕ).testBit (8 * u.val + v.val)) 27) := by
  let C : PEqualNP.CircuitLowerBounds.Circuit := ⟨[
    ⟨.or, [10, 0]⟩,
    ⟨.or, [16, 12]⟩,
    ⟨.and, [12, 6]⟩,
    ⟨.or, [13, 2]⟩,
    ⟨.or, [17, 6]⟩,
    ⟨.or, [9, 4]⟩,
    ⟨.or, [15, 7]⟩,
    ⟨.or, [21, 22]⟩,
    ⟨.or, [22, 16]⟩,
    ⟨.or, [1, 18]⟩,
    ⟨.or, [25, 11]⟩,
    ⟨.or, [14, 3]⟩,
    ⟨.and, [26, 23]⟩,
    ⟨.or, [28, 8]⟩,
    ⟨.or, [21, 19]⟩,
    ⟨.or, [24, 19]⟩,
    ⟨.and, [31, 27]⟩,
    ⟨.or, [32, 5]⟩,
    ⟨.or, [29, 33]⟩,
    ⟨.or, [27, 22]⟩,
    ⟨.and, [7, 15]⟩,
    ⟨.or, [30, 26]⟩,
    ⟨.or, [30, 35]⟩,
    ⟨.and, [37, 20]⟩,
    ⟨.or, [36, 34]⟩,
    ⟨.and, [38, 40]⟩,
    ⟨.or, [39, 41]⟩], 42⟩
  refine ⟨C, ?_, by decide, ?_⟩
  · intro g hg
    simp only [C, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide +kernel

#print axioms mask14500150567228511850_upper
