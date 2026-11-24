import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.Girth
import PEqualNP.Defs

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

-- A vertex cover builds a circuit by assigning its incident edges to stars.
-- Deleting a cubic cover vertex saves three edges and one center.
-- This removes the star bound cases from the gate structure analysis.
theorem PEqualNP.Outside.R_meta_4117_43
  (graph_upper : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A T : Finset (Fin n)), (∃ i j, G.Adj i j) →
    (∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) →
    HasCircuitSize n (graphFun G A) (A.card + G.edgeFinset.card + T.card - 1))
  (small_case : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit), x5.size < x4.card + x2.edgeFinset.card + x2.vertexCoverNum.toNat - 1 →   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains x7;   have x8 : Fin x1 → ℕ → Finset ℕ := fun (x8 : Fin x1) (x9 : ℕ) => {x10 ∈ Finset.range x5.gates.length | x10 ≠ x9 ∧ (x7 (↑x8) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true ∨ x9 < x10 ∧ x7 (x1 + x9) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true)};   have x9 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : Fin x1) => List.filter (x7 ↑x9) x5.gates;   (∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ x16 ∉ x4, (x9 x16).length ≤ (3 : ℕ) ∧ ((x9 x16).length = (3 : ℕ) → ∀ x19 ∈ x9 x16, x19.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x17 ∉ x4, (x9 x17).length ≤ (1 : ℕ) ∧ ∀ x18 ∈ x9 x17, ∀ (x20 : Fin x1), x20 ≠ x17 → x18.inputs.Perm [↑x17, ↑x20] → x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → (¬∃ x18 ∉ x4, ∃ x19 < x5.gates.length, x7 (↑x18) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19) = Bool.true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ (x8 x18 x19).card) → ∃ x19 ∉ x4, ∃ (x20 : ℕ), x20 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x21 : Fin x1 → Bool) => x6 (Function.update x21 x19 Bool.false)) x20) :
  ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : Finset (Fin x1)) (x5 : PEqualNP.CircuitLowerBounds.Circuit),   have x6 : (Fin x1 → Bool) → Bool := PEqualNP.MetaComplexity.NestedCover.graphFun x2 x4;   have x7 : ℕ → PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x7 : ℕ) (x8 : PEqualNP.CircuitLowerBounds.Gate) => (List.take (bif x8.op.eval [Bool.false] then (1 : ℕ) else (2 : ℕ)) x8.inputs).contains x7;   have x8 : Fin x1 → ℕ → Finset ℕ := fun (x8 : Fin x1) (x9 : ℕ) => {x10 ∈ Finset.range x5.gates.length | x10 ≠ x9 ∧ (x7 (↑x8) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true ∨ x9 < x10 ∧ x7 (x1 + x9) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x10) = Bool.true)};   have x9 : Fin x1 → List PEqualNP.CircuitLowerBounds.Gate := fun (x9 : Fin x1) => List.filter (x7 ↑x9) x5.gates;   (∀ x10 ∉ x4, (x2.neighborSet x10).ncard = (3 : ℕ)) → (7 : ℕ∞) ≤ x2.egirth → (∀ (x12 x13 : Fin x1), x2.Adj x12 x13 → x12 ∉ x4) → (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14) → PEqualNP.MetaComplexity.IsMinimalCircuit x1 x5 → PEqualNP.MetaComplexity.circuitFun x1 x5 = x6 → (∀ x16 ∉ x4, (x9 x16).length ≤ (3 : ℕ) ∧ ((x9 x16).length = (3 : ℕ) → ∀ x19 ∈ x9 x16, x19.op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∃ x17 ∉ x4, (x9 x17).length ≤ (1 : ℕ) ∧ ∀ x18 ∈ x9 x17, ∀ (x20 : Fin x1), x20 ≠ x17 → x18.inputs.Perm [↑x17, ↑x20] → x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.and ∧ x18.op ≠ PEqualNP.CircuitLowerBounds.GateOp.or) → (¬∃ x18 ∉ x4, ∃ x19 < x5.gates.length, x7 (↑x18) (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19) = Bool.true ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x5 x19).op ≠ PEqualNP.CircuitLowerBounds.GateOp.or ∧ (3 : ℕ) ≤ (x8 x18 x19).card) → ∃ x19 ∉ x4, ∃ (x20 : ℕ), x20 + (4 : ℕ) ≤ x5.size ∧ PEqualNP.MetaComplexity.HasCircuitSize x1 (fun (x21 : Fin x1 → Bool) => x6 (Function.update x21 x19 Bool.false)) x20 := by
  classical
  have restrict_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A : Finset (Fin n)) (v : Fin n) (hv : v ∉ A) [DecidableRel (G.deleteIncidenceSet v).Adj] :
      (fun x => graphFun G A (Function.update x v false)) = graphFun (G.deleteIncidenceSet v) A := by
    classical
    funext x
    rw [Bool.eq_iff_iff]
    delta graphFun
    simp only [Bool.or_eq_true,decide_eq_true_eq,SimpleGraph.deleteIncidenceSet_adj]
    constructor
    · rintro (⟨a,ha,on⟩ | ⟨a,b,ab,on1,on2⟩)
      · refine Or.inl ⟨a,ha,?_⟩
        simpa [Function.update_of_ne (show a ≠ v from fun e => hv (e ▸ ha))] using on
      · have av : a ≠ v := by rintro rfl; simp at on1
        have bv : b ≠ v := by rintro rfl; simp at on2
        exact Or.inr ⟨a,b,⟨ab,av,bv⟩,by simpa [Function.update_of_ne av] using on1,
          by simpa [Function.update_of_ne bv] using on2⟩
    · rintro (⟨a,ha,on⟩ | ⟨a,b,⟨ab,av,bv⟩,on1,on2⟩)
      · exact Or.inl ⟨a,ha,by simpa [Function.update_of_ne (show a ≠ v from fun e => hv (e ▸ ha))] using on⟩
      · exact Or.inr ⟨a,b,ab,by simpa [Function.update_of_ne av] using on1,
          by simpa [Function.update_of_ne bv] using on2⟩
  have cover_saving {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (A T : Finset (Fin n)) (v : Fin n) (hv : v ∉ A) (ht : v ∈ T)
      (cover : ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T)
      (degree : G.degree v = 3) (remains : ∃ i j, (G.deleteIncidenceSet v).Adj i j)
      (s : ℕ) (threshold : A.card + G.edgeFinset.card + T.card - 1 ≤ s) :
      ∃ k, k+4 ≤ s ∧ HasCircuitSize n (fun x => graphFun G A (Function.update x v false)) k := by
    classical
    let H := G.deleteIncidenceSet v
    have subcover : ∀ i j, H.Adj i j → i ∈ T.erase v ∨ j ∈ T.erase v := by
      intro i j adj
      obtain ⟨edge,iv,jv⟩ := SimpleGraph.deleteIncidenceSet_adj.mp adj
      exact (cover i j edge).imp (fun h => Finset.mem_erase.mpr ⟨iv,h⟩)
        (fun h => Finset.mem_erase.mpr ⟨jv,h⟩)
    have ub := graph_upper H A (T.erase v) remains subcover
    obtain ⟨i,j,ij⟩ := remains
    have hp : 0 < H.edgeFinset.card := Finset.card_pos.mpr ⟨s(i,j),by simpa [H] using ij⟩
    have hc : H.edgeFinset.card = G.edgeFinset.card - 3 := by
      simpa [H,degree] using G.card_edgeFinset_deleteIncidenceSet v
    have htcard := Finset.card_erase_of_mem ht
    have tpos := Finset.card_pos.mpr ⟨v,ht⟩
    refine ⟨A.card + H.edgeFinset.card + (T.erase v).card - 1,?_,?_⟩
    · exact (show A.card + H.edgeFinset.card + (T.erase v).card - 1 + 4 ≤ s by omega)
    · rw [restrict_graph G A v hv]
      exact ub
  have exists_off {n : ℕ} (G : SimpleGraph (Fin n)) {u v : Fin n}
      (deg : (G.neighborSet u).ncard = 3) : ∃ w, G.Adj u w ∧ w ≠ v := by
    classical
    by_contra! allSame
    have sub : G.neighborSet u ⊆ {v} := fun w h => allSame w h
    have le := Set.ncard_le_ncard sub (Set.finite_singleton v)
    rw [deg,Set.ncard_singleton] at le
    omega
  have covered_case {n} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A T : Finset (Fin n))
      (cubic : ∀ u ∉ A, (G.neighborSet u).ncard = 3)
      (pure : ∀ i j, G.Adj i j → i ∉ A)
      (nonempty : ∃ i j, G.Adj i j)
      (cover : ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T)
      (s : ℕ) (threshold : A.card + G.edgeFinset.card + T.card - 1 ≤ s) :
      ∃ v ∉ A, ∃ k, k + 4 ≤ s ∧ HasCircuitSize n (fun x => graphFun G A (Function.update x v false)) k := by
    classical
    obtain ⟨i,j,edge⟩ := nonempty
    have select (v w : Fin n) (vw : G.Adj v w) (vt : v ∈ T) :
        ∃ u ∉ A, ∃ k, k + 4 ≤ s ∧
          HasCircuitSize n (fun x => graphFun G A (Function.update x u false)) k := by
      have hv := pure v w vw
      obtain ⟨z,wz,zv⟩ := exists_off G (v := v) (cubic w (pure w v vw.symm))
      have remains : ∃ i j, (G.deleteIncidenceSet v).Adj i j :=
        ⟨w,z,SimpleGraph.deleteIncidenceSet_adj.mpr ⟨wz,(G.ne_of_adj vw).symm,zv⟩⟩
      exact ⟨v,hv,cover_saving G A T v hv vt cover
        (by simpa [SimpleGraph.ncard_neighborSet] using cubic v hv) remains s threshold⟩
    rcases cover i j edge with left | right
    · exact select i j edge left
    · exact select j i edge.symm right
  intro n G inst A C
  by_cases small : C.size < A.card + G.edgeFinset.card + G.vertexCoverNum.toNat - 1
  · exact small_case n G A C small
  dsimp only
  intro cubic _ pure edge _ _ _ _ _
  obtain ⟨S,card,cover⟩ := G.vertexCoverNum_exists
  have sc : S.toFinset.card = G.vertexCoverNum.toNat := by
    rw [← card, ← Set.ncard_eq_toFinset_card']
    rfl
  apply covered_case G A S.toFinset cubic pure edge
  · intro i j ij
    simpa using cover ij
  · rw [sc]
    omega
