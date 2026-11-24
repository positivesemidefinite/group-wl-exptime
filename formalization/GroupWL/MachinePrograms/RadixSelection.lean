import GroupWL.MachinePrograms.NatArrayRadix
import GroupWL.MachinePrograms.ArrayTabulate
import GroupWL.MachinePrograms.NatArrayPowers
import GroupWL.MachinePrograms.NatArrayComponents

/-! Enumerate a subset of tuple states whose coordinates lie in an initial segment. -/
namespace GroupWL.MachinePrograms.RadixSelection
open NatArrayLanguage
abbrev Reg := NatArrayRadix.Reg ⊕ Fin 8
abbrev Arr := Unit ⊕ Unit
abbrev Code := Program Reg Arr
set_option maxRecDepth 4096

def word (n N k offset : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin (n^k) => offset+NatArrayRadix.recode n N i.val k)

def setupPoint : List (Atom Reg Arr) := [.copy (.inl 2) (.inr 3),.copy (.inl 3) (.inr 0)]
def point : Code := .seq (atoms setupPoint) (.seq (NatArrayRadix.convert.map Sum.inl Sum.inl)
  (.atom (.binary .add (.inr 7) (.inr 1) (.inl 5))))
def fill : Code := ArrayTabulate.tabulate (.inr 3) (.inr 4) (.inr 2) (.inr 5) (.inr 6) (.inr 7) (.inr ()) point

structure Context (n N k offset : ℕ) (S : Store Reg Arr) : Prop where
  base_eq : S.scalar (.inl 0)=n
  target_eq : S.scalar (.inl 1)=N
  width_eq : S.scalar (.inr 0)=k
  offset_eq : S.scalar (.inr 1)=offset

theorem point_runs (n N k offset : ℕ) (hnpos : 0<n) (hle : n≤N) (i : Fin (n^k))
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B) (hP : Context n N k offset S)
    (hi : S.scalar (.inr 3)=i.val) (hroom : offset+N^k≤B) :
    ∃ T,Runs (storageBound Reg Arr B) point S (7*k+7) T ∧ T.Bounded B ∧ Context n N k offset T ∧
      (∀ j : Fin 8,j≠7 → T.scalar (.inr j)=S.scalar (.inr j)) ∧
      T.array (.inr ())=S.array (.inr ()) ∧ T.scalar (.inr 7)=offset+NatArrayRadix.recode n N i.val k := by
  have valid : ValidAtoms B setupPoint S := by simp [setupPoint,ValidAtoms,Atom.Valid,Atom.SmallResult]
  obtain ⟨first,hU⟩ := atoms_runs hS setupPoint valid
  let U := applyAtoms setupPoint S
  obtain ⟨V,middle,hV,hvalue,_,_,_⟩ := NatArrayRadix.convert_runs n N i.val k U.left B hU.left
    (by simp [U,applyAtoms,setupPoint,Atom.apply,Store.left,Store.setScalar,hP.base_eq])
    (by simp [U,applyAtoms,setupPoint,Atom.apply,Store.left,Store.setScalar,hP.target_eq])
    (by simp [U,applyAtoms,setupPoint,Atom.apply,Store.left,Store.setScalar,hi])
    (by simp [U,applyAtoms,setupPoint,Atom.apply,Store.left,Store.setScalar,hP.width_eq])
    hnpos hle i.isLt (by omega)
  let W := V.join U.right
  have lifted := middle.left_bounded hU
  have hW : W.Bounded B := hV.join hU.right
  have hoff : W.scalar (.inr 1)=offset := hP.offset_eq
  have small : (Atom.binary .add (.inr 7) (.inr 1) (.inl 5)).SmallResult B W := by
    change W.scalar (.inr 1)+V.scalar 5≤B
    rw [hoff,hvalue]
    have := NatArrayRadix.recode_lt n N i.val k hnpos hle i.isLt
    omega
  have last := atom_runs hW (.binary .add (.inr 7) (.inr 1) (.inl 5)) trivial small
  let T := (Atom.binary .add (.inr 7) (.inr 1) (.inl 5)).apply W
  have hT : T.Bounded B := Atom.apply_bounded hW _ small
  have frames (j : NatArrayRadix.Reg) (hj : j=0 ∨ j=1) : V.scalar j=U.left.scalar j := by
    apply middle.scalar_eq_of_not_mem
    rcases hj with rfl|rfl <;>
      simp [NatArrayRadix.convert,NatArrayRadix.prelude,NatArrayRadix.loop,NatArrayRadix.body,
        NatArrayRadix.bodyAtoms,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites]
  have hPT : Context n N k offset T := by
    constructor
    · simpa [T,W,U,applyAtoms,setupPoint,Atom.apply,Store.left,Store.setScalar,hP.base_eq] using frames 0 (Or.inl rfl)
    · simpa [T,W,U,applyAtoms,setupPoint,Atom.apply,Store.left,Store.setScalar,hP.target_eq] using frames 1 (Or.inr rfl)
    · simpa [T,W,Atom.apply,Store.setScalar] using hP.width_eq
    · simpa [T,W,Atom.apply,Store.setScalar] using hP.offset_eq
  refine ⟨T,?_,hT,hPT,?_,rfl,?_⟩
  · convert Runs.seq first (Runs.seq lifted last) using 1 <;> simp [setupPoint] <;> omega
  · intro j hj;simp [T,W,Atom.apply,Store.setScalar,hj];rfl
  · simp [T,Atom.apply,BinaryOp.eval,W,hoff,hvalue]

theorem fill_runs (n N k offset : ℕ) (hnpos : 0<n) (hle : n≤N)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B) (hP : Context n N k offset S)
    (hcount : S.scalar (.inr 2)=n^k) (hone : S.scalar (.inr 5)=1) (hzero : S.scalar (.inr 6)=0)
    (hroom : offset+N^k≤B) :
    ∃ t≤n^k*(7*k+11)+4,∃ T,Runs (storageBound Reg Arr B) fill S t T ∧ T.Bounded B ∧
      Context n N k offset T ∧ T.array (.inr ())=word n N k offset := by
  apply ArrayTabulate.tabulate_runs (.inr 3) (.inr 4) (.inr 2) (.inr 5) (.inr 6) (.inr 7) (.inr ()) point
    (fun i => offset+NatArrayRadix.recode n N i.val k) (Context n N k offset) B (7*k+7)
  · intro U v hU;exact ⟨by simpa using hU.base_eq,by simpa using hU.target_eq,by simpa using hU.width_eq,by simpa using hU.offset_eq⟩
  · intro U v hU;exact ⟨by simpa using hU.base_eq,by simpa using hU.target_eq,by simpa using hU.width_eq,by simpa using hU.offset_eq⟩
  · intro U xs hU;exact ⟨hU.base_eq,hU.target_eq,hU.width_eq,hU.offset_eq⟩
  · decide
  · decide
  · decide
  · intro i U hp hb hi htodo hone
    obtain ⟨V,run,hV,hPV,frames,harray,hvalue⟩ := point_runs n N k offset hnpos hle i U B hb hp hi hroom
    exact ⟨7*k+7,le_rfl,V,run,hV,hPV,(frames 3 (by decide)).trans hi,
      (frames 4 (by decide)).trans htodo,(frames 5 (by decide)).trans hone,hvalue,harray⟩
  · exact hS
  · exact hP
  · exact hcount
  · exact hone
  · exact hzero

def powerRegisters : Fin 5 ↪ NatArrayRadix.Reg :=
  ⟨![0,3,4,7,8],by decide⟩
def afterPower : List (Atom Reg Arr) := [.copy (.inr 2) (.inl 4),.const (.inr 5) 1,.const (.inr 6) 0]
def generate : Code := .seq (.atom (.copy (.inl 3) (.inr 0)))
  (.seq ((power powerRegisters).map Sum.inl Sum.inl) (.seq (atoms afterPower) fill))

theorem generate_runs (n N k offset : ℕ) (hnpos : 0<n) (hle : n≤N)
    (S : Store Reg Arr) (B : ℕ) (hS : S.Bounded B) (hP : Context n N k offset S)
    (hroom : offset+N^k≤B) :
    ∃ t≤n^k*(7*k+11)+3*k+12,∃ T,Runs (storageBound Reg Arr B) generate S t T ∧ T.Bounded B ∧
      Context n N k offset T ∧ T.array (.inr ())=word n N k offset := by
  have h1 : 1≤B := (one_le_pow₀ (lt_of_lt_of_le hnpos hle)).trans (by omega : N^k≤B)
  have first := atom_runs hS (.copy (.inl 3) (.inr 0)) trivial trivial
  let U := (Atom.copy (.inl 3) (.inr 0)).apply S
  have hU : U.Bounded B := Atom.apply_bounded hS _ trivial
  obtain ⟨V,middle,hV,hcount⟩ := power_runs powerRegisters U.left n k B hU.left hnpos
    (by simpa [powerRegisters,U,Atom.apply,Store.left,Store.setScalar] using hP.base_eq)
    (by simp [powerRegisters,U,Atom.apply,Store.left,Store.setScalar,hP.width_eq])
    ((Nat.pow_le_pow_left hle k).trans (by omega : N^k≤B))
  have lifted := middle.left_bounded hU
  let W := V.join U.right
  have hW : W.Bounded B := hV.join hU.right
  have valid : ValidAtoms B afterPower W := by simp [afterPower,ValidAtoms,Atom.Valid,Atom.SmallResult,h1]
  obtain ⟨prep,hX⟩ := atoms_runs hW afterPower valid
  let X := applyAtoms afterPower W
  have frames (j : NatArrayRadix.Reg) (hj : j=0 ∨ j=1) : V.scalar j=U.left.scalar j := by
    apply middle.scalar_eq_of_not_mem
    rcases hj with rfl|rfl <;> simp [power,powerRegisters,powerLoop,powerBody,atoms,
      NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites]
  have hPX : Context n N k offset X := by
    constructor
    · simpa [X,applyAtoms,afterPower,W,U,Atom.apply,Store.left,Store.setScalar,hP.base_eq] using frames 0 (Or.inl rfl)
    · simpa [X,applyAtoms,afterPower,W,U,Atom.apply,Store.left,Store.setScalar,hP.target_eq] using frames 1 (Or.inr rfl)
    · simp [X,applyAtoms,afterPower,W,U,Atom.apply,Store.right,Store.setScalar,hP.width_eq]
    · simp [X,applyAtoms,afterPower,W,U,Atom.apply,Store.right,Store.setScalar,hP.offset_eq]
  obtain ⟨t,ht,T,last,hT,hPT,hword⟩ := fill_runs n N k offset hnpos hle X B hX hPX
    (by simpa [X,applyAtoms,afterPower,W,Atom.apply,Store.setScalar,powerRegisters] using hcount)
    (by simp [X,applyAtoms,afterPower,Atom.apply,Store.setScalar])
    (by simp [X,applyAtoms,afterPower,Atom.apply,Store.setScalar]) hroom
  refine ⟨1+((3*k+4)+(3+t)),by omega,T,Runs.seq first (Runs.seq lifted (Runs.seq prep last)),hT,hPT,hword⟩
end GroupWL.MachinePrograms.RadixSelection
