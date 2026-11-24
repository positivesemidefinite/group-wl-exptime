import GroupWL.MachinePrograms.GroupImageExpansion
import GroupWL.MachinePrograms.GroupMapSemantics

/-! Validate the complete map obtained from proposed generator images. -/
namespace GroupWL.MachinePrograms.GroupImageTest
open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

abbrev Reg := GroupImageExpansion.Reg ⊕ GroupMapPrograms.Reg
abbrev Arr := GroupImageExpansion.Arr ⊕ GroupMapPrograms.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def test : Code := sequence [
  GroupImageExpansion.expand.map Sum.inl Sum.inl,
  .atom (.copyArray (.inr .images) (.inl GroupImageExpansion.imageArray)),
  GroupMapPrograms.validate.map Sum.inr Sum.inr]

def Valid {n m k : ℕ} (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n) (b : Fin k→Fin m) : Prop :=
  (∀x y,NumericGroupImages.expand op op' identity identity' a b (op x y)=
    op' (NumericGroupImages.expand op op' identity identity' a b x)
      (NumericGroupImages.expand op op' identity identity' a b y)) ∧
    Function.Injective (NumericGroupImages.expand op op' identity identity' a b)
instance {n m k : ℕ} (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n) (b : Fin k→Fin m) :
    Decidable (Valid op op' identity identity' a b) := inferInstanceAs (Decidable ((∀x y,_) ∧ ∀x y,_))

structure Ready {n m : ℕ} (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (S : State) : Prop where
  expansion : GroupImageExpansion.Ready identity identity'
    (GroupInitial.tableWord (ProductGroupTable.productOp op op')) S.left
  sourceOrder : S.scalar (.inr .sourceOrder)=n
  targetOrder : S.scalar (.inr .targetOrder)=m
  sourceTable : S.array (.inr .source)=GroupInitial.tableWord op
  targetTable : S.array (.inr .target)=GroupInitial.tableWord op'

theorem test_runs {n m k : ℕ} (S : State) (M : ℕ)
    (op : Fin n→Fin n→Fin n) (op' : Fin m→Fin m→Fin m)
    (identity : Fin n) (identity' : Fin m) (a : Fin k→Fin n) (b : Fin k→Fin m)
    (hb : S.Bounded M) (hready : Ready op op' identity identity' S)
    (ha : S.array (.inl (.inl .left))=List.ofFn (fun i => (a i).val))
    (hb' : S.array (.inl (.inl .right))=List.ofFn (fun i => (b i).val))
    (hroom : (n*m)*(n*m)≤M) :
    ∃t≤10*(n*m)^3+8*(n*m)+13*k+n*(9*m+13)+19*n*n+35,∃T,
      Runs (storageBound Reg Arr M) test S t T ∧ T.Bounded M ∧
      (T.scalar (.inr .result)=1 ↔ Valid op op' identity identity' a b) := by
  have hn : 0<n := Nat.zero_lt_of_lt identity.isLt
  have hm : 0<m := Nat.zero_lt_of_lt identity'.isLt
  have hnn : n*n≤M := (Nat.mul_le_mul (by nlinarith : n≤n*m) (by nlinarith : n≤n*m)).trans hroom
  have hmm : m*m≤M := (Nat.mul_le_mul (by nlinarith : m≤n*m) (by nlinarith : m≤n*m)).trans hroom
  obtain ⟨t,ht,U,expand,hU,ho⟩ := GroupImageExpansion.expand_runs S.left M identity identity' op op' a b
    (GroupInitial.tableWord (ProductGroupTable.productOp op op')) hb.left hready.expansion ha hb'
    (by simp) (by intro i; simp [GroupInitial.tableWord]) hroom
  let V := U.join S.right
  have hV : V.Bounded M := hU.join hb.right
  let W := (Atom.copyArray (Sum.inr GroupMapPrograms.Arr.images) (Sum.inl GroupImageExpansion.imageArray)).apply V
  have hW : W.Bounded M := Atom.apply_bounded hV _ trivial
  have copy := atom_runs hV (.copyArray (.inr .images) (.inl GroupImageExpansion.imageArray)) trivial trivial
  let f := NumericGroupImages.expand op op' identity identity' a b
  have himages : W.right.array .images=List.ofFn (fun x : Fin n => (f x).val) := by
    simpa [W,Atom.apply,Store.right,V,f] using ho
  have hsource : W.right.array .source=GroupInitial.tableWord op := by
    simpa [W,Atom.apply,Store.right,V] using hready.sourceTable
  have htarget : W.right.array .target=GroupInitial.tableWord op' := by
    simpa [W,Atom.apply,Store.right,V] using hready.targetTable
  obtain ⟨u,hu,X,validate,hX,hout⟩ := GroupMapPrograms.validate_correct W.right M op op' f hW.right
    (by simpa [W,Atom.apply,Store.right,V] using hready.sourceOrder)
    (by simpa [W,Atom.apply,Store.right,V] using hready.targetOrder) hn hm
    (by simp [hsource]) (by simp [htarget]) (by simp [himages])
    (by intro z hz; rw [hsource,GroupInitial.tableWord] at hz
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz; exact (op _ _).isLt)
    (by intro z hz; rw [himages] at hz
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hz; exact (f i).isLt)
    (by intro x y; simpa [GroupTablePrograms.operation,GroupTablePrograms.read,hsource,Nat.add_comm,Nat.mul_comm]
        using GroupInitial.tableWord_read op x y)
    (by intro x y; simpa [GroupTablePrograms.operation,GroupTablePrograms.read,htarget,Nat.add_comm,Nat.mul_comm]
        using GroupInitial.tableWord_read op' x y)
    (by intro x; simp [GroupTablePrograms.read,himages]) hnn hmm
  have validated := validate.right_bounded hW
  refine ⟨t+(1+(u+0)),by nlinarith,W.left.join X,
    .seq (expand.left_bounded hb) (.seq copy (.seq validated (.skip validated.end_bound))),hW.left.join hX,?_⟩
  exact hout

theorem ready_frame {n m : ℕ} {op : Fin n→Fin n→Fin n} {op' : Fin m→Fin m→Fin m}
    {identity : Fin n} {identity' : Fin m} {B S T t} (h : Runs B test S t T)
    (hs : Ready op op' identity identity' S) : Ready op op' identity identity' T := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact ⟨(h.scalar_eq_of_not_mem _ (by decide)).trans hs.expansion.pairCols,
      (h.scalar_eq_of_not_mem _ (by decide)).trans hs.expansion.seedOrder,
      (h.scalar_eq_of_not_mem _ (by decide)).trans hs.expansion.seedIdentity,
      (h.scalar_eq_of_not_mem _ (by decide)).trans hs.expansion.closureOrder,
      (h.array_eq_of_not_mem _ (by decide)).trans hs.expansion.table_eq,
      (h.scalar_eq_of_not_mem _ (by decide)).trans hs.expansion.imageRows,
      (h.scalar_eq_of_not_mem _ (by decide)).trans hs.expansion.imageCols,
      (h.scalar_eq_of_not_mem _ (by decide)).trans hs.expansion.imageIdentity⟩
  · exact (h.scalar_eq_of_not_mem _ (by decide)).trans hs.sourceOrder
  · exact (h.scalar_eq_of_not_mem _ (by decide)).trans hs.targetOrder
  · exact (h.array_eq_of_not_mem _ (by decide)).trans hs.sourceTable
  · exact (h.array_eq_of_not_mem _ (by decide)).trans hs.targetTable

theorem sourceTuple_frame {B S T t} (h : Runs B test S t T) :
    T.array (.inl (.inl .left))=S.array (.inl (.inl .left)) := h.array_eq_of_not_mem _ (by decide)

end GroupWL.MachinePrograms.GroupImageTest
