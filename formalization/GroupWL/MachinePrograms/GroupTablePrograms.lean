import GroupWL.MachinePrograms.NatArrayProofs
import GroupWL.MachinePrograms.NatArrayFrames
import GroupWL.MachinePrograms.NatArrayCountedLoops
import GroupWL.VerifiedGroupTable

/-! Materialized finite group tables. The programs read and compare actual
array entries; no primitive instruction evaluates a group operation. -/
namespace GroupWL.MachinePrograms.GroupTablePrograms

open NatArrayLanguage
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

inductive Reg where
  | order | identity | one | x | y | z | index | xy | yz | xz
  | left | right | flag | equal | result | position | todo | total | quotient
  deriving DecidableEq, Fintype

inductive Arr where
  | table
  deriving DecidableEq, Fintype

abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def read (xs : List ℕ) (i : ℕ) : ℕ := xs[i]?.getD 0

def operation (n : ℕ) (xs : List ℕ) (x y : ℕ) : ℕ := read xs (x*n+y)

def lookupAtoms (left right destination : Reg) : List (Atom Reg Arr) := [
  .binary .mul .index left .order,
  .binary .add .index .index right,
  .read destination .table .index]

def lookup (left right destination : Reg) : Code := atoms (lookupAtoms left right destination)

theorem lookup_runs (S : State) (M : ℕ) (left right destination : Reg)
    (hbound : S.Bounded M) (hleft : left ≠ .index) (hright : right ≠ .index)
    (index_lt : S.scalar left*S.scalar .order+S.scalar right < (S.array .table).length) :
    Runs (storageBound Reg Arr M) (lookup left right destination) S 3
      (applyAtoms (lookupAtoms left right destination) S) ∧
    (applyAtoms (lookupAtoms left right destination) S).Bounded M ∧
    (applyAtoms (lookupAtoms left right destination) S).scalar destination =
      operation (S.scalar .order) (S.array .table) (S.scalar left) (S.scalar right) := by
  have hlength := hbound.2.1 Arr.table
  have hv : ValidAtoms M (lookupAtoms left right destination) S := by
    simp [lookupAtoms, ValidAtoms, Atom.Valid, Atom.SmallResult, Atom.apply, BinaryOp.eval,
      Store.setScalar, Function.update_apply, hright]
    exact ⟨by omega, by omega, index_lt⟩
  obtain ⟨hr,hb⟩ := atoms_runs hbound (lookupAtoms left right destination) hv
  refine ⟨hr,hb,?_⟩
  simp [applyAtoms,lookupAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,
    Function.update_apply,hright,operation,read]

def checkTripleAtoms : List (Atom Reg Arr) :=
  lookupAtoms .identity .x .left ++ [
    .binary .eq .flag .left .x, .binary .mul .result .result .flag] ++
  lookupAtoms .x .identity .left ++ [
    .binary .eq .flag .left .x, .binary .mul .result .result .flag] ++
  lookupAtoms .x .y .xy ++ lookupAtoms .y .z .yz ++
  lookupAtoms .xy .z .left ++ lookupAtoms .x .yz .right ++ [
    .binary .eq .flag .left .right, .binary .mul .result .result .flag] ++
  lookupAtoms .x .z .xz ++ [
    .binary .eq .flag .xy .xz, .binary .eq .equal .y .z,
    .binary .le .flag .flag .equal, .binary .mul .result .result .flag]

def checkTriple : Code := atoms checkTripleAtoms

def tripleValid (n identity : ℕ) (xs : List ℕ) (x y z : ℕ) : Prop :=
  operation n xs identity x = x ∧ operation n xs x identity = x ∧
  operation n xs (operation n xs x y) z = operation n xs x (operation n xs y z) ∧
  (operation n xs x y = operation n xs x z → y=z)

instance (n identity : ℕ) (xs : List ℕ) (x y z : ℕ) :
    Decidable (tripleValid n identity xs x y z) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ (_ → _)))

theorem operation_lt {n : ℕ} {xs : List ℕ} (hn : 0<n)
    (hxs : ∀ v∈xs, v<n) (x y : ℕ) : operation n xs x y < n := by
  unfold operation read
  cases h : xs[x*n+y]? with
  | none => exact hn
  | some v => exact hxs v (List.mem_of_getElem? h)

theorem table_index_lt {n x y : ℕ} (hx : x<n) (hy : y<n) : x*n+y<n*n := by
  nlinarith

private theorem combineChecks (a b c d e : Prop) [Decidable a] [Decidable b]
    [Decidable c] [Decidable d] [Decidable e] (r : ℕ) :
    r*(if a then 1 else 0)*(if b then 1 else 0)*(if c then 1 else 0)*
      (if (if d then 1 else 0) ≤ (if e then 1 else 0) then 1 else 0) =
      r*(if a ∧ b ∧ c ∧ (d → e) then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;>
    by_cases hd : d <;> by_cases he : e <;> simp [ha,hb,hc,hd,he]

theorem checkTriple_runs (S : State) (n M e x y z : ℕ)
    (hb : S.Bounded M) (hn : S.scalar .order=n) (he : S.scalar .identity=e)
    (hx : S.scalar .x=x) (hy : S.scalar .y=y) (hz : S.scalar .z=z)
    (helt : e<n) (hxlt : x<n) (hylt : y<n) (hzlt : z<n)
    (hlen : (S.array .table).length=n*n) (hvals : ∀ v∈S.array .table, v<n)
    (hresult : S.scalar .result≤1) (hroom : n*n≤M) :
    Runs (storageBound Reg Arr M) checkTriple S 31 (applyAtoms checkTripleAtoms S) ∧
      (applyAtoms checkTripleAtoms S).Bounded M ∧
      (applyAtoms checkTripleAtoms S).scalar .result =
        S.scalar .result * (if tripleValid n e (S.array .table) x y z then 1 else 0) := by
  have hpos : 0<n := by omega
  have hM : 1≤M := by nlinarith
  have hop (a b : ℕ) : (S.array .table)[a*n+b]?.getD 0<n := operation_lt hpos hvals a b
  have hindex {a b : ℕ} (ha : a<n) (hb : b<n) : a*n+b<n*n := table_index_lt ha hb
  have hmul {a : ℕ} (ha : a<n) : a*n≤M := by nlinarith
  have hle {a b : ℕ} (ha : a<n) (hb : b<n) : a*n+b≤M := by
    exact (Nat.le_of_lt (hindex ha hb)).trans hroom
  have hv : ValidAtoms M checkTripleAtoms S := by
    simp [checkTripleAtoms,lookupAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,
      Atom.apply,BinaryOp.eval,Store.setScalar,hn,he,hx,hy,hz,hlen]
    repeat' apply And.intro
    all_goals first
      | exact hindex (hop _ _) hzlt
      | exact hindex hxlt (hop _ _)
      | exact hindex helt hxlt
      | exact hindex hxlt helt
      | exact hindex hxlt hylt
      | exact hindex hylt hzlt
      | exact hindex hxlt hzlt
      | exact hmul helt
      | exact hmul hxlt
      | exact hmul hylt
      | exact hmul (hop _ _)
      | exact hle helt hxlt
      | exact hle hxlt helt
      | exact hle hxlt hylt
      | exact hle hylt hzlt
      | exact hle (hop _ _) hzlt
      | exact hle hxlt (hop _ _)
      | exact hle hxlt hzlt
      | (split_ifs <;> omega)
  obtain ⟨hr,hbounded⟩ := atoms_runs hb checkTripleAtoms hv
  refine ⟨hr,hbounded,?_⟩
  simpa [applyAtoms,checkTripleAtoms,lookupAtoms,Atom.apply,BinaryOp.eval,
    Store.setScalar,hn,he,hx,hy,hz,tripleValid,operation,read] using
    combineChecks
      (operation n (S.array .table) e x=x) (operation n (S.array .table) x e=x)
      (operation n (S.array .table) (operation n (S.array .table) x y) z =
        operation n (S.array .table) x (operation n (S.array .table) y z))
      (operation n (S.array .table) x y=operation n (S.array .table) x z) (y=z)
      (S.scalar .result)

theorem tripleValid_iff {n : ℕ} (hn : 0<n) (identity : Fin n)
    (op : Fin n → Fin n → Fin n) (xs : List ℕ)
    (hread : ∀ x y : Fin n, operation n xs x.val y.val = (op x y).val) :
    (∀ x y z : Fin n, tripleValid n identity.val xs x.val y.val z.val) ↔
      VerifiedGroupTable.Valid identity op := by
  simp only [tripleValid,hread,VerifiedGroupTable.Valid]
  constructor
  · intro h
    refine ⟨?_,?_,?_,?_⟩
    · intro x; exact Fin.ext (h x ⟨0,hn⟩ ⟨0,hn⟩).1
    · intro x; exact Fin.ext (h x ⟨0,hn⟩ ⟨0,hn⟩).2.1
    · intro x y z; exact Fin.ext (h x y z).2.2.1
    · intro x y z he
      exact Fin.ext ((h x y z).2.2.2 (congrArg Fin.val he))
  · intro h x y z
    exact ⟨congrArg Fin.val (h.1 x),congrArg Fin.val (h.2.1 x),
      congrArg Fin.val (h.2.2.1 x y z),fun he => congrArg Fin.val (h.2.2.2 x (Fin.ext he))⟩

end GroupWL.MachinePrograms.GroupTablePrograms
