import PEqualNP.Defs

namespace L_meta_1167_Proof

open PEqualNP.CircuitLowerBounds

/-- The witness circuit for the edge function of the 8-vertex graph with edges
01 02 03 04 05 06 17. Wires 0–7 are the inputs; the gates produce wires 8–15:
wire 8 = OR(1,2), wire 9 = OR(8,3), wire 10 = OR(9,4), wire 11 = OR(10,5),
wire 12 = OR(11,6), wire 13 = AND(0,12), wire 14 = AND(1,7), wire 15 = OR(13,14).
The output is wire 15. -/
def witness : Circuit where
  gates :=
    [ ⟨GateOp.or, [1, 2]⟩
    , ⟨GateOp.or, [8, 3]⟩
    , ⟨GateOp.or, [9, 4]⟩
    , ⟨GateOp.or, [10, 5]⟩
    , ⟨GateOp.or, [11, 6]⟩
    , ⟨GateOp.and, [0, 12]⟩
    , ⟨GateOp.and, [1, 7]⟩
    , ⟨GateOp.or, [13, 14]⟩ ]
  output := 15

set_option maxRecDepth 10000 in
theorem L_meta_1167 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 8 ∧
      ∀ x : Fin 8 → Bool, C.eval (List.ofFn x) =
        (fun x : Fin 8 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) ||
          (x 0 && x 4) || (x 0 && x 5) || (x 0 && x 6) || (x 1 && x 7)) x := by
  refine ⟨witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      refine ⟨by simp, by decide⟩
  · decide
  · decide

end L_meta_1167_Proof
