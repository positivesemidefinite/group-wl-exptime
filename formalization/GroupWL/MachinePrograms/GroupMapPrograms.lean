import GroupWL.MachinePrograms.GroupTablePrograms

/-! Direct multiplication and injectivity checks of a materialized function.
Every operation reads the supplied numeric multiplication tables. -/
namespace GroupWL.MachinePrograms.GroupMapPrograms

open NatArrayLanguage GroupTablePrograms
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

inductive Reg where
  | sourceOrder | targetOrder | one | x | y | index | sourceProduct
  | targetX | targetY | targetProduct | imageProduct | equal | flag | result
  | position | todo | total
  deriving DecidableEq, Fintype
inductive Arr where
  | source | target | images
  deriving DecidableEq, Fintype
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr

def pairAtoms : List (Atom Reg Arr) := [
  .binary .mul .index .x .sourceOrder,.binary .add .index .index .y,
  .read .sourceProduct .source .index,.read .imageProduct .images .sourceProduct,
  .read .targetX .images .x,.read .targetY .images .y,
  .binary .mul .index .targetX .targetOrder,.binary .add .index .index .targetY,
  .read .targetProduct .target .index,
  .binary .eq .equal .imageProduct .targetProduct,.binary .mul .result .result .equal,
  .binary .eq .equal .targetX .targetY,.binary .eq .flag .x .y,
  .binary .le .flag .equal .flag,.binary .mul .result .result .flag]
def checkPair : Code := atoms pairAtoms

def pairValid (n m : ℕ) (source target images : List ℕ) (x y : ℕ) : Prop :=
  read images (operation n source x y)=operation m target (read images x) (read images y) ∧
  (read images x=read images y → x=y)
instance (n m : ℕ) (source target images : List ℕ) (x y : ℕ) :
    Decidable (pairValid n m source target images x y) :=
  inferInstanceAs (Decidable (_ ∧ (_ → _)))

private theorem combine (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] (r : ℕ) :
    r*(if a then 1 else 0)*(if (if b then 1 else 0)≤(if c then 1 else 0) then 1 else 0)=
      r*(if a ∧ (b → c) then 1 else 0) := by
  by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> simp [ha,hb,hc]

theorem checkPair_runs (S : State) (n m M x y : ℕ)
    (hb : S.Bounded M) (hn : S.scalar .sourceOrder=n) (hm : S.scalar .targetOrder=m)
    (hx : S.scalar .x=x) (hy : S.scalar .y=y) (hxlt : x<n) (hylt : y<n) (hmpos : 0<m)
    (hsource : (S.array .source).length=n*n) (htarget : (S.array .target).length=m*m)
    (himages : (S.array .images).length=n)
    (hsourceVals : ∀ v∈S.array .source,v<n) (himageVals : ∀ v∈S.array .images,v<m)
    (hresult : S.scalar .result≤1) (hroom : n*n≤M) (hroom' : m*m≤M) :
    Runs (storageBound Reg Arr M) checkPair S 15 (applyAtoms pairAtoms S) ∧
      (applyAtoms pairAtoms S).Bounded M ∧
      (applyAtoms pairAtoms S).scalar .result=S.scalar .result*
        (if pairValid n m (S.array .source) (S.array .target) (S.array .images) x y then 1 else 0) := by
  have hpos : 0<n := by omega
  have hM : 1≤M := by nlinarith
  have hop (a b : ℕ) : (S.array .source)[a*n+b]?.getD 0<n := operation_lt hpos hsourceVals a b
  have him (a : ℕ) : (S.array .images)[a]?.getD 0<m := by
    cases h : (S.array .images)[a]? with
    | none => exact hmpos
    | some v => exact himageVals v (List.mem_of_getElem? h)
  have hindex {a b r : ℕ} (ha : a<r) (hb : b<r) : a*r+b<r*r := table_index_lt ha hb
  have hmul {a r : ℕ} (ha : a<r) (hr : r*r≤M) : a*r≤M := by nlinarith
  have hle {a b r : ℕ} (ha : a<r) (hb : b<r) (hr : r*r≤M) : a*r+b≤M := by nlinarith
  have hv : ValidAtoms M pairAtoms S := by
    simp [pairAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,
      Store.setScalar,hn,hm,hx,hy,hsource,htarget,himages]
    repeat' apply And.intro
    all_goals first
      | exact hxlt
      | exact hylt
      | exact hop _ _
      | exact hindex hxlt hylt
      | exact hindex (him _) (him _)
      | exact hmul hxlt hroom
      | exact hmul (him _) hroom'
      | exact hle hxlt hylt hroom
      | exact hle (him _) (him _) hroom'
      | (split_ifs <;> omega)
  obtain ⟨hr,hT⟩ := atoms_runs hb pairAtoms hv
  refine ⟨hr,hT,?_⟩
  simpa [applyAtoms,pairAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,hn,hm,hx,hy,
    pairValid,GroupTablePrograms.read,operation] using
    combine (read (S.array .images) (operation n (S.array .source) x y)=
      operation m (S.array .target) (read (S.array .images) x) (read (S.array .images) y))
      (read (S.array .images) x=read (S.array .images) y) (x=y) (S.scalar .result)

def decodeAtoms : List (Atom Reg Arr) := [.divmod .x .y .position .sourceOrder]
def checkPosition : Code := .seq (atoms decodeAtoms) checkPair

theorem checkPosition_runs (S : State) (n m M i : ℕ)
    (hb : S.Bounded M) (hn : S.scalar .sourceOrder=n) (hm : S.scalar .targetOrder=m)
    (hi : S.scalar .position=i) (hiLt : i<n*n) (hmpos : 0<m)
    (hsource : (S.array .source).length=n*n) (htarget : (S.array .target).length=m*m)
    (himages : (S.array .images).length=n)
    (hsourceVals : ∀ v∈S.array .source,v<n) (himageVals : ∀ v∈S.array .images,v<m)
    (hresult : S.scalar .result≤1) (hroom : n*n≤M) (hroom' : m*m≤M) :
    ∃ T,Runs (storageBound Reg Arr M) checkPosition S 16 T ∧ T.Bounded M ∧
      T.scalar .result=S.scalar .result*
        (if pairValid n m (S.array .source) (S.array .target) (S.array .images) (i/n) (i%n) then 1 else 0) := by
  have hnpos : 0<n := by nlinarith
  have hv : ValidAtoms M decodeAtoms S := by
    simp [decodeAtoms,ValidAtoms,Atom.Valid,Atom.SmallResult,hn,hnpos]
  obtain ⟨pre,hU⟩ := atoms_runs hb decodeAtoms hv
  let U := applyAtoms decodeAtoms S
  obtain ⟨run,hT,ho⟩ := checkPair_runs U n m M (i/n) (i%n) hU
    (by simp [U,applyAtoms,decodeAtoms,Atom.apply,Store.setScalar,hn])
    (by simp [U,applyAtoms,decodeAtoms,Atom.apply,Store.setScalar,hm])
    (by simp [U,applyAtoms,decodeAtoms,Atom.apply,Store.setScalar,hi,hn])
    (by simp [U,applyAtoms,decodeAtoms,Atom.apply,Store.setScalar,hi,hn])
    (Nat.div_lt_of_lt_mul hiLt) (Nat.mod_lt _ hnpos) hmpos hsource htarget himages
    hsourceVals himageVals (by simpa [U,applyAtoms,decodeAtoms,Atom.apply,Store.setScalar] using hresult)
    hroom hroom'
  refine ⟨_,.seq pre run,hT,?_⟩
  simpa [U,applyAtoms,decodeAtoms,Atom.apply,Store.setScalar] using ho

end GroupWL.MachinePrograms.GroupMapPrograms
