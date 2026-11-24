import GroupWL.MachinePrograms.KernelToTensor
import GroupWL.MachinePrograms.CircuitParserCost
import GroupWL.GateCoordinateEncoding

/-! Decode a circuit and compact the owners and port numbers of its gates. -/
namespace GroupWL.MachinePrograms.CircuitRecordPipeline.Packed
open NatArrayLanguage AddressedCircuit CircuitComparisonCodes
open NatArrayLowering (bitNat)
set_option maxRecDepth 8192

section Chaining
variable {R A U V : Type} [DecidableEq R] [DecidableEq A] [DecidableEq U] [DecidableEq V]
  [Fintype R] [Fintype A] [Fintype U] [Fintype V]

theorem chain (p : NatArrayLanguage.Program R A) (s : U → Ports.Scalar R A) (a : V → Option A) (q : NatArrayLanguage.Program U V)
    (S : Store (R⊕U) (A⊕V)) (m x y : ℕ) (bp : Store R A → Prop) (bq : Store U V → Prop)
    (hs : S.Bounded m) (small : ∀i k,s i=.literal k → k≤m)
    (first : ∃t≤x,∃P,Runs (storageBound R A m) p S.left t P ∧ P.Bounded m ∧ bp P)
    (second : ∀ P, bp P → (Ports.target s a P).Bounded m → ∃t≤y,∃Q,
      Runs (storageBound U V m) q (Ports.target s a P) t Q ∧ Q.Bounded m ∧ bq Q) :
    ∃t≤x+(Fintype.card U+Fintype.card V+y),∃T,
      Runs (storageBound (R⊕U) (A⊕V) m) (Ports.thenRun p s a q) S t T ∧ T.Bounded m ∧
      bp T.left ∧ bq T.right := by
  obtain ⟨t,ht,P,hp,bp',out⟩ := first
  have wire := Ports.code_runs s a P S.right m (bp'.join hs.right) small
  obtain ⟨u,hu,Q,hq,bq',res⟩ := second P out wire.2
  have run := Ports.thenRun_runs p s a q S.left P S.right Q m t u hs.left bp' hs.right small hp hq
  rw [Store.join_left_right] at run
  exact ⟨_,Nat.add_le_add ht (Nat.add_le_add_left hu _),P.join Q,run,bp'.join bq',out,res⟩
end Chaining

def gateInit : List (Atom GateCandidates.Reg GateCandidates.Arr) :=
  [.const .two 2,.arrayLength .length .kinds,.binary .add .length .length .length]
def gate (f : GateCandidates.Field) := NatArrayLanguage.Program.seq (atoms gateInit) (GateCandidates.program f)

variable {T : Type} [FiniteCode T] {r : ℕ}

theorem gate_runs (C : Circuit T r) (f : GateCandidates.Field) (S : GateCandidates.State) (M : ℕ)
    (hs : S.Bounded M) (h2 : 2≤M) (hsize : 2*FiniteCode.size T≤M) (input : S.array .kinds=kinds C) :
    ∃t≤20*FiniteCode.size T+9,∃U,Runs (storageBound GateCandidates.Reg GateCandidates.Arr M) (gate f) S t U ∧
      U.Bounded M ∧ U.array .kinds=kinds C ∧ U.array .output=candidates C f := by
  have valid : ValidAtoms M gateInit S := by
    simp [gateInit,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,BinaryOp.eval,h2,input]
    omega
  obtain ⟨run,hV⟩ := atoms_runs hs gateInit valid
  let V := applyAtoms gateInit S
  have pre : GateCandidates.Inputs (kinds C) V := ⟨input,by simp [V,gateInit,applyAtoms,Atom.apply,Store.setScalar]⟩
  have len : V.scalar .length=2*(kinds C).length := by
    simp [V,gateInit,applyAtoms,Atom.apply,Store.setScalar,BinaryOp.eval,input,two_mul]
  obtain ⟨t,ht,U,exec,hU,data,out⟩ := GateCandidates.program_runs f (kinds C) V M hV pre (kinds_binary C) len
  rw [kinds_length] at ht
  exact ⟨3+t,by omega,U,run.seq exec,hU,data.input,by simpa [candidates] using out⟩

abbrev PairReg := GateCandidates.Reg ⊕ GateCandidates.Reg
abbrev PairArr := GateCandidates.Arr ⊕ GateCandidates.Arr
abbrev CountReg := PairReg ⊕ FilterRanks.Reg
abbrev CountArr := PairArr ⊕ FilterRanks.Arr
abbrev Reg := CountReg ⊕ SelectArray.Reg
abbrev Arr := CountArr ⊕ SelectArray.Arr

def gatePorts : GateCandidates.Arr → Option GateCandidates.Arr
  | .kinds => some .kinds | _ => none

def countPorts : FilterRanks.Arr → Option PairArr
  | .flags => some (.inl .output) | _ => none

def selectRegs : SelectArray.Reg → Ports.Scalar CountReg CountArr
  | .selected => .scalar (.inr .count) | _ => .literal 0

def selectPorts : SelectArray.Arr → Option CountArr
  | .flags => some (.inl (.inl .output)) | .values => some (.inl (.inr .output)) | _ => none

noncomputable def pair (f : GateCandidates.Field) : NatArrayLanguage.Program PairReg PairArr :=
  Ports.thenRun (gate .flag) (fun _=>.literal 0) gatePorts (gate f)
noncomputable def counted (f : GateCandidates.Field) : NatArrayLanguage.Program CountReg CountArr :=
  Ports.thenRun (pair f) (fun _=>.literal 0) countPorts FilterRanks.program
noncomputable def program (f : GateCandidates.Field) : NatArrayLanguage.Program Reg Arr :=
  Ports.thenRun (counted f) selectRegs selectPorts SelectArray.program

def pairTime (n : ℕ) := (20*n+9)+(Fintype.card GateCandidates.Reg+Fintype.card GateCandidates.Arr+(20*n+9))
def countTime (n : ℕ) := pairTime n+(Fintype.card FilterRanks.Reg+Fintype.card FilterRanks.Arr+(6*(2*n)+8))
def time (n : ℕ) := countTime n+(Fintype.card SelectArray.Reg+Fintype.card SelectArray.Arr+(8*(2*n)+8))

structure Words (C : Circuit T r) (f : GateCandidates.Field) (P : Store PairReg PairArr) : Prop where
  flags : P.left.array .output=candidates C .flag
  values : P.right.array .output=candidates C f

theorem pair_runs (C : Circuit T r) (f : GateCandidates.Field) (S : Store PairReg PairArr) (M : ℕ)
    (hs : S.Bounded M) (h2 : 2≤M) (hsize : 2*FiniteCode.size T≤M) (input : S.left.array .kinds=kinds C) :
    ∃t≤pairTime (FiniteCode.size T),∃U,Runs (storageBound PairReg PairArr M) (pair f) S t U ∧
      U.Bounded M ∧ Words C f U := by
  have run := chain (gate .flag) (fun _=>.literal 0) gatePorts (gate f) S M _ _
    (fun P => P.array .kinds=kinds C ∧ P.array .output=candidates C .flag)
    (fun Q => Q.array .kinds=kinds C ∧ Q.array .output=candidates C f) hs
    (by intro i k hk; cases hk; omega) (gate_runs C .flag S.left M hs.left h2 hsize input)
    (fun P hp hP => gate_runs C f _ M hP h2 hsize hp.1)
  obtain ⟨t,ht,U,run,hU,l,r⟩ := run
  exact ⟨t,ht,U,run,hU,l.2,r.2⟩

structure Counted (C : Circuit T r) (f : GateCandidates.Field) (P : Store CountReg CountArr) : Prop where
  words : Words C f P.left
  count : P.right.scalar .count=portCount C

theorem count_runs (C : Circuit T r) (f : GateCandidates.Field) (S : Store CountReg CountArr) (M : ℕ)
    (hs : S.Bounded M) (h2 : 2≤M) (hsize : 2*FiniteCode.size T≤M) (input : S.left.left.array .kinds=kinds C) :
    ∃t≤countTime (FiniteCode.size T),∃U,Runs (storageBound CountReg CountArr M) (counted f) S t U ∧
      U.Bounded M ∧ Counted C f U := by
  have run := chain (pair f) (fun _=>.literal 0) countPorts FilterRanks.program S M _ (6*(2*FiniteCode.size T)+8)
    (Words C f) (fun Q => Q.scalar .count=portCount C) hs
    (by intro i k hk; cases hk; omega) (pair_runs C f S.left M hs.left h2 hsize input) ?_
  · obtain ⟨t,ht,U,hRun,hU,hWords,hCount⟩ := run; exact ⟨t,ht,U,hRun,hU,hWords,hCount⟩
  · intro P hp hP
    let X : FilterRanks.State := Ports.target (fun _=>.literal 0) countPorts P
    have hflags : X.array .flags=candidates C .flag := hp.flags
    obtain ⟨t,ht,Q,run,hQ,c,_⟩ := FilterRanks.program_runs X M hP (by omega) (by rw [hflags];exact flags_binary C)
    rw [hflags,candidates_length] at ht c
    exact ⟨t,ht,Q,run,hQ,c.trans (selected_count C)⟩

abbrev kindsArray : Arr := .inl (.inl (.inl .kinds))
abbrev output : Arr := .inr .output

theorem program_runs (C : Circuit T r) (f : GateCandidates.Field) (S : Store Reg Arr) (M : ℕ)
    (hs : S.Bounded M) (h2 : 2≤M) (hsize : 2*FiniteCode.size T≤M) (input : S.array kindsArray=kinds C) :
    ∃t≤time (FiniteCode.size T),∃U,Runs (storageBound Reg Arr M) (program f) S t U ∧
      U.Bounded M ∧ U.array output=packed C f := by
  have run := chain (counted f) selectRegs selectPorts SelectArray.program S M _ (8*(2*FiniteCode.size T)+8)
    (Counted C f) (fun Q => Q.array .output=packed C f) hs ?_ (count_runs C f S.left M hs.left h2 hsize input) ?_
  · obtain ⟨t,ht,U,hRun,hU,_,out⟩ := run
    exact ⟨t,ht,U,hRun,hU,out⟩
  · intro i k hk; cases i <;> first | contradiction | cases hk; omega
  · intro P hp hP
    let X := Ports.target selectRegs selectPorts P
    have hf : X.array .flags=candidates C .flag := hp.words.flags
    have hv : X.array .values=candidates C f := hp.words.values
    have hc : X.scalar .selected=portCount C := hp.count
    obtain ⟨t,ht,Q,run,bQ,out,_⟩ := SelectArray.program_runs X M hP (by omega)
      (by rw [hf,hv];simp) (by rw [hf];exact flags_binary C)
      (by rw [hc,hf,candidates_length,selected_count])
    rw [hf,candidates_length] at ht
    rw [hf,hv,candidates_length] at out
    exact ⟨t,ht,Q,run,bQ,out⟩
end GroupWL.MachinePrograms.CircuitRecordPipeline.Packed
