import GroupWL.MachinePrograms.NatArrayComponents
import GroupWL.MachinePrograms.ArraySlice
import GroupWL.MachinePrograms.IdentityMatrix
import GroupWL.MachinePrograms.PivotSearch
import GroupWL.MachinePrograms.PivotInverse

/-! A single finite-register program for reverse-row Gaussian elimination.
Every operation is a previously verified concrete array-language client. -/
namespace GroupWL.MachinePrograms.KernelProgram
open NatArrayLanguage

inductive WorkReg where
  | rows | ambient | width | remaining | modulus | one
  deriving DecidableEq,Fintype
inductive WorkArr where
  | input | lift | lowerTranspose
  deriving DecidableEq,Fintype
abbrev ClientReg := MatrixArithmetic.Reg ⊕ (PivotSearch.Reg ⊕
  (PivotMatrix.Reg ⊕ (ArraySlice.Reg ⊕ IdentityMatrix.Reg)))
abbrev ClientArr := MatrixArithmetic.Arr ⊕ (PivotSearch.Arr ⊕
  (PivotMatrix.Arr ⊕ (ArraySlice.Arr ⊕ IdentityMatrix.Arr)))
abbrev Reg := WorkReg ⊕ ClientReg
abbrev Arr := WorkArr ⊕ ClientArr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

abbrev wr : WorkReg → Reg := Sum.inl
abbrev wa : WorkArr → Arr := Sum.inl
abbrev mr (r : MatrixArithmetic.Reg) : Reg := .inr (.inl r)
abbrev ma (a : MatrixArithmetic.Arr) : Arr := .inr (.inl a)
abbrev sr (r : PivotSearch.Reg) : Reg := .inr (.inr (.inl r))
abbrev sa (a : PivotSearch.Arr) : Arr := .inr (.inr (.inl a))
abbrev pr (r : PivotMatrix.Reg) : Reg := .inr (.inr (.inr (.inl r)))
abbrev pa (a : PivotMatrix.Arr) : Arr := .inr (.inr (.inr (.inl a)))
abbrev cr (r : ArraySlice.Reg) : Reg := .inr (.inr (.inr (.inr (.inl r))))
abbrev ca (a : ArraySlice.Arr) : Arr := .inr (.inr (.inr (.inr (.inl a))))
abbrev ir (r : IdentityMatrix.Reg) : Reg := .inr (.inr (.inr (.inr (.inr r))))
abbrev ia (a : IdentityMatrix.Arr) : Arr := .inr (.inr (.inr (.inr (.inr a))))

def multiply : Code := MatrixArithmetic.multiply.map mr ma
def search : Code := PivotSearch.program.map sr sa
def pivot (p : ℕ) : Code := (PivotMatrix.withInverse p).map pr pa
def slice : Code := ArraySlice.program.map cr ca
def identity : Code := IdentityMatrix.program.map ir ia

def setup : Code := .seq (atoms [
  .const (wr .one) 1,.copy (wr .width) (wr .ambient),
  .copy (wr .remaining) (wr .rows),.copy (ir .dimension) (wr .ambient)])
  (.seq identity (atoms [.copyArray (wa .lift) (ia .output),
    .copyArray (wa .lowerTranspose) (ia .output)]))

def rowSetup : List (Atom Reg Arr) := [
  .binary .sub (wr .remaining) (wr .remaining) (wr .one),
  .binary .mul (cr .offset) (wr .remaining) (wr .ambient),
  .copy (cr .length) (wr .ambient),.copyArray (ca .input) (wa .input)]
def rowMultiplySetup : List (Atom Reg Arr) := [
  .const (mr .rows) 1,.copy (mr .inner) (wr .ambient),.copy (mr .cols) (wr .width),
  .copy (mr .modulus) (wr .modulus),.copyArray (ma .left) (ca .output),
  .copyArray (ma .right) (wa .lift)]
def pivotSetup : List (Atom Reg Arr) := [
  .copy (pr .width) (wr .width),.copy (pr .pivot) (sr .pivot),
  .copy (pr .modulus) (wr .modulus),.copyArray (pa .row) (sa .row)]
def liftMultiplySetup : List (Atom Reg Arr) := [
  .copy (mr .rows) (wr .ambient),.copy (mr .inner) (wr .width),
  .binary .sub (mr .cols) (wr .width) (wr .one),
  .copy (mr .modulus) (wr .modulus),.copyArray (ma .left) (wa .lift),
  .copyArray (ma .right) (pa .lift)]
def lowerMultiplySetup : List (Atom Reg Arr) := [
  .copyArray (wa .lift) (ma .output),
  .copyArray (ma .left) (wa .lowerTranspose),.copyArray (ma .right) (pa .lowerTranspose)]
def update (p : ℕ) : Code := .seq (atoms pivotSetup)
  (.seq (pivot p) (.seq (atoms liftMultiplySetup)
    (.seq multiply (.seq (atoms lowerMultiplySetup)
      (.seq multiply (atoms [.copyArray (wa .lowerTranspose) (ma .output),
        .binary .sub (wr .width) (wr .width) (wr .one)]))))))
def step (p : ℕ) : Code := .seq (atoms rowSetup)
  (.seq slice (.seq (atoms rowMultiplySetup)
    (.seq multiply (.seq (.atom (.copyArray (sa .row) (ma .output)))
      (.seq search (.branch (sr .found) (update p) .skip))))))
def program (p : ℕ) : Code := .seq setup (.while (wr .remaining) (step p))

def matrixProduct (A B : List ℕ) (rows inner cols p : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (rows*cols) =>
    MatrixArithmetic.partialDot A B inner cols (i.val/cols) (i.val%cols) p inner)

structure Data where
  width : ℕ
  lift : List ℕ
  lowerTranspose : List ℕ
  deriving DecidableEq

def initial (n : ℕ) : Data :=
  ⟨n,IdentityMatrix.diagonalPrefix n n,IdentityMatrix.diagonalPrefix n n⟩

def equation (A : List ℕ) (n i p : ℕ) (D : Data) : List ℕ :=
  matrixProduct (List.ofFn (fun j : Fin n => ArraySlice.value A (i*n) j))
    D.lift 1 n D.width p

def eliminate (p n : ℕ) (h : List ℕ) (D : Data) : Data :=
  match PivotSearch.first h h.length with
  | none => D
  | some j =>
      let neg := (-((h[j]?.getD 0:ℕ):ZMod p)⁻¹).val
      let L := List.ofFn (fun i : Fin (D.width*(D.width-1)) =>
        PivotMatrix.liftValue h (D.width-1) j neg p i)
      let R := List.ofFn (fun i : Fin (D.width*(D.width-1)) =>
        PivotMatrix.lowerValue (D.width-1) j i)
      ⟨D.width-1,matrixProduct D.lift L n D.width (D.width-1) p,
        matrixProduct D.lowerTranspose R n D.width (D.width-1) p⟩

def executeRows (A : List ℕ) (p n : ℕ) : ℕ → Data → Data
  | 0,D => D
  | i+1,D => executeRows A p n i (eliminate p n (equation A n i p D) D)

theorem multiply_client {M t : ℕ} {S : State} {T : MatrixArithmetic.State}
    (h : Runs (storageBound MatrixArithmetic.Reg MatrixArithmetic.Arr M)
      MatrixArithmetic.multiply S.right.left t T) (bounded : S.Bounded M) :
    Runs (storageBound Reg Arr M) multiply S t (S.left.join (T.join S.right.right)) := by
  have h₁ := h.left_bounded bounded.right
  have h₂ := h₁.right_bounded bounded
  simpa only [multiply,Program.map_map,Function.comp_def,mr,ma] using h₂

theorem search_client {M t : ℕ} {S : State} {T : PivotSearch.State}
    (h : Runs (storageBound PivotSearch.Reg PivotSearch.Arr M)
      PivotSearch.program S.right.right.left t T) (bounded : S.Bounded M) :
    Runs (storageBound Reg Arr M) search S t
      (S.left.join (S.right.left.join (T.join S.right.right.right))) := by
  have h₁ := h.left_bounded bounded.right.right
  have h₂ := h₁.right_bounded bounded.right
  have h₃ := h₂.right_bounded bounded
  simpa only [search,Program.map_map,Function.comp_def,sr,sa] using h₃

theorem pivot_client {M t p : ℕ} {S : State} {T : PivotMatrix.State}
    (h : Runs (storageBound PivotMatrix.Reg PivotMatrix.Arr M)
      (PivotMatrix.withInverse p) S.right.right.right.left t T) (bounded : S.Bounded M) :
    Runs (storageBound Reg Arr M) (pivot p) S t
      (S.left.join (S.right.left.join (S.right.right.left.join (T.join S.right.right.right.right)))) := by
  have h₁ := h.left_bounded bounded.right.right.right
  have h₂ := h₁.right_bounded bounded.right.right
  have h₃ := h₂.right_bounded bounded.right
  have h₄ := h₃.right_bounded bounded
  simpa only [pivot,Program.map_map,Function.comp_def,pr,pa] using h₄

theorem slice_client {M t : ℕ} {S : State} {T : ArraySlice.State}
    (h : Runs (storageBound ArraySlice.Reg ArraySlice.Arr M)
      ArraySlice.program S.right.right.right.right.left t T) (bounded : S.Bounded M) :
    Runs (storageBound Reg Arr M) slice S t
      (S.left.join (S.right.left.join (S.right.right.left.join
        (S.right.right.right.left.join (T.join S.right.right.right.right.right))))) := by
  have h₁ := h.left_bounded bounded.right.right.right.right
  have h₂ := h₁.right_bounded bounded.right.right.right
  have h₃ := h₂.right_bounded bounded.right.right
  have h₄ := h₃.right_bounded bounded.right
  have h₅ := h₄.right_bounded bounded
  simpa only [slice,Program.map_map,Function.comp_def,cr,ca] using h₅

theorem identity_client {M t : ℕ} {S : State} {T : IdentityMatrix.State}
    (h : Runs (storageBound IdentityMatrix.Reg IdentityMatrix.Arr M)
      IdentityMatrix.program S.right.right.right.right.right t T) (bounded : S.Bounded M) :
    Runs (storageBound Reg Arr M) identity S t
      (S.left.join (S.right.left.join (S.right.right.left.join
        (S.right.right.right.left.join (S.right.right.right.right.left.join T))))) := by
  have h₁ := h.right_bounded bounded.right.right.right.right
  have h₂ := h₁.right_bounded bounded.right.right.right
  have h₃ := h₂.right_bounded bounded.right.right
  have h₄ := h₃.right_bounded bounded.right
  have h₅ := h₄.right_bounded bounded
  simpa only [identity,Program.map_map,Function.comp_def,ir,ia] using h₅

end GroupWL.MachinePrograms.KernelProgram
