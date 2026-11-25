import Mathlib.Tactic.FinCases
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10031

-- Each block uses five different two-element subsets of four labels.
-- Rectangle k contains the rows whose incident column has its label,
-- and the columns of its block without that label.
def rowMask (k : Fin 24) := ([7576807, 27060025, 10824010, 21648020, 20771271, 29826681, 5842570, 10668340, 26693511, 15331577, 19535146, 5548628, 29997863, 8277465, 9622090, 19211444, 15623783, 20167577, 21285034, 10032468, 32767, 33521695, 1016800, 32537600] : List ℕ).getD k.val 0
def colMask (k : Fin 24) := ([24, 6, 21, 11, 768, 192, 672, 352, 24576, 6144, 21504, 11264, 786432, 196608, 688128, 360448, 25165824, 6291456, 22020096, 11534336, 805306368, 201326592, 704643072, 369098752] : List ℕ).getD k.val 0
def entry (i : Fin 25) (j : Fin 30) := (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val
def box (k : Fin 24) : Finset (Fin 25) × Finset (Fin 30) :=
  (Finset.univ.filter (fun i => (rowMask k).testBit i.val),
   Finset.univ.filter (fun j => (colMask k).testBit j.val))

theorem row0 : ∀ j : Fin 30, entry 0 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 0 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row1 : ∀ j : Fin 30, entry 1 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 1 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row2 : ∀ j : Fin 30, entry 2 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 2 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row3 : ∀ j : Fin 30, entry 3 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 3 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row4 : ∀ j : Fin 30, entry 4 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 4 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row5 : ∀ j : Fin 30, entry 5 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 5 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row6 : ∀ j : Fin 30, entry 6 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 6 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row7 : ∀ j : Fin 30, entry 7 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 7 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row8 : ∀ j : Fin 30, entry 8 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 8 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row9 : ∀ j : Fin 30, entry 9 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 9 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row10 : ∀ j : Fin 30, entry 10 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 10 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row11 : ∀ j : Fin 30, entry 11 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 11 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row12 : ∀ j : Fin 30, entry 12 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 12 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row13 : ∀ j : Fin 30, entry 13 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 13 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row14 : ∀ j : Fin 30, entry 14 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 14 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row15 : ∀ j : Fin 30, entry 15 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 15 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row16 : ∀ j : Fin 30, entry 16 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 16 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row17 : ∀ j : Fin 30, entry 17 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 17 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row18 : ∀ j : Fin 30, entry 18 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 18 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row19 : ∀ j : Fin 30, entry 19 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 19 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row20 : ∀ j : Fin 30, entry 20 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 20 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row21 : ∀ j : Fin 30, entry 21 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 21 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row22 : ∀ j : Fin 30, entry 22 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 22 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row23 : ∀ j : Fin 30, entry 23 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 23 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem row24 : ∀ j : Fin 30, entry 24 j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit 24 = true ∧ (colMask k).testBit j.val = true := by decide +kernel

theorem checkRow (i : Fin 25) (j : Fin 30) : entry i j = false ↔
    ∃ k : Fin 24, (rowMask k).testBit i.val = true ∧ (colMask k).testBit j.val = true := by
  fin_cases i
  · exact row0 j
  · exact row1 j
  · exact row2 j
  · exact row3 j
  · exact row4 j
  · exact row5 j
  · exact row6 j
  · exact row7 j
  · exact row8 j
  · exact row9 j
  · exact row10 j
  · exact row11 j
  · exact row12 j
  · exact row13 j
  · exact row14 j
  · exact row15 j
  · exact row16 j
  · exact row17 j
  · exact row18 j
  · exact row19 j
  · exact row20 j
  · exact row21 j
  · exact row22 j
  · exact row23 j
  · exact row24 j

end PEqualNP.Outside.L_meta_10031

open PEqualNP.Outside.L_meta_10031 in
theorem PEqualNP.Outside.L_meta_10031 : ∃ L : List (Finset (Fin 25) × Finset (Fin 30)), L.length ≤ 24 ∧ (∀ r ∈ L, ∀ i ∈ r.1, ∀ j ∈ r.2, (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false) ∧ ∀ (i : Fin 25) (j : Fin 30), (([34636833, 35719234, 37884036, 42213640, 50872848, 69345793, 71581730, 76022852, 83921032, 68227344, 138938625, 142643714, 151068708, 135413832, 136578192, 276906113, 285345026, 269748740, 271061032, 272670800, 553914433, 538452098, 539017476, 541132296, 545392688] : List ℕ).getD i.val 0).testBit j.val = false → ∃ r ∈ L, i ∈ r.1 ∧ j ∈ r.2 := by
  refine ⟨(List.finRange 24).map box, by simp, ?_, ?_⟩
  · intro r hr i hi j hj
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hr
    exact (checkRow i j).mpr ⟨k, (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2⟩
  · intro i j h
    obtain ⟨k, hi, hj⟩ := (checkRow i j).mp h
    exact ⟨box k, List.mem_map.mpr ⟨k, by simp, rfl⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
