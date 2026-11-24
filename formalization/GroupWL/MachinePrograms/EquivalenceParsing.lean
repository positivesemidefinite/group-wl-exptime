import GroupWL.MachinePrograms.IdentificationParsing

/-! Parsing two tensor descriptions and their shared WL dimension. -/
namespace GroupWL.MachinePrograms.EquivalenceParsing
open NatArrayLanguage
open NatArrayLowering (bitNat)
set_option maxRecDepth 4096

abbrev Reg := ValidatedTensorProgram.Reg ⊕ Fin 2
abbrev Arr := ValidatedTensorProgram.Arr ⊕ Unit
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr

def r (i : Fin 13) : Reg := .inl (ValidatedTensorProgram.r i)
def input : Arr := .inl ValidatedTensorProgram.input
def output : Arr := .inl ValidatedTensorProgram.output
def saved : Arr := .inr ()

def parseTensor (p : ℕ) : Code := (ValidatedTensorProgram.program p).map Sum.inl Sum.inl

def dimension (e : Statement.DimensionEncoding) : Code := (IdentificationParsing.dimension e).map Sum.inl Sum.inl

def snapshot : List (Atom Reg Arr) := [.copy (.inr 0) (r 11),.copy (.inr 1) (r 12),.copyArray saved output]
def initializeInput : List (Atom Reg Arr) := [.arrayLength (r 1) input,.const (r 0) 0,.const (r 3) 1]

def program (p : ℕ) (e : Statement.DimensionEncoding) : Code := .seq (atoms initializeInput)
  (.seq (parseTensor p) (.branch (r 3)
    (.seq (atoms snapshot) (.seq (parseTensor p) (.branch (r 3) (dimension e) .skip))) .skip))

def EncodesFirst (p : ℕ) [Fact p.Prime] (S : State) (T : Statement.TensorDescription p) : Prop :=
  S.scalar (.inr 0)=T.inputDimension ∧ S.scalar (.inr 1)=T.outputDimension ∧
    S.array saved=TensorSerialization.coefficientList (T.coefficient p)

theorem parseTensor_runs (p : ℕ) [Fact p.Prime] (S : State) (w : List Bool) (pos M : ℕ)
    (bounded : S.Bounded M) (room : (w.length+1)^3≤M) (fieldRoom : p^3+p≤M)
    (powerRoom : p^w.length≤M) (position : S.scalar (r 0)=pos) (posBound : pos≤w.length)
    (length : S.scalar (r 1)=w.length) (valid : S.scalar (r 3)=1)
    (inputEq : S.array input=w.map bitNat) :
    ∃T t,t≤ValidatedTensorProgram.scanCost p w.length ∧
      Runs (storageBound Reg Arr M) (parseTensor p) S t T ∧
      T.Bounded M ∧ T.scalar (r 0)≤w.length ∧ T.scalar (r 1)=w.length ∧
      T.scalar (r 3)≤1 ∧ T.array input=w.map bitNat ∧ T.right=S.right ∧
      match Statement.readTensor p (w.drop pos) with
      | none => T.scalar (r 3)=0
      | some (tensor,tail) => T.scalar (r 3)=1 ∧
          IdentificationParsing.EncodesTensor p T.left tensor ∧
          w.drop (T.scalar (r 0))=tail := by
  obtain ⟨U,t,ht,run,hU,hpos,hlen,hvalid,hinput,spec⟩ := ValidatedTensorProgram.program_runs p S.left w pos M
    bounded.left room fieldRoom powerRoom position posBound length valid inputEq
  refine ⟨U.join S.right,t,ht,run.left_bounded bounded,hU.join bounded.right,hpos,hlen,hvalid,hinput,rfl,?_⟩
  cases hp : Statement.readTensor p (w.drop pos) with
  | none =>simpa only [hp] using spec
  | some v =>
    rcases v with ⟨tensor,tail⟩
    simp only [hp] at spec
    exact ⟨spec.1,⟨spec.2.1,spec.2.2.1,spec.2.2.2.1⟩,spec.2.2.2.2⟩

def parseCost (p N : ℕ) : ℕ := 2*ValidatedTensorProgram.scanCost p N+6*N+20

theorem program_runs (p : ℕ) [Fact p.Prime] (e : Statement.DimensionEncoding)
    (S : State) (w : List Bool) (M : ℕ) (bounded : S.Bounded M)
    (room : (w.length+1)^3≤M) (fieldRoom : p^3+p≤M)
    (powerRoom : p^w.length≤M) (binaryRoom : 2^(w.length+1)≤M)
    (inputEq : S.array input=w.map bitNat) :
    ∃T t,t≤parseCost p w.length ∧ Runs (storageBound Reg Arr M) (program p e) S t T ∧
      T.Bounded M ∧ T.scalar (r 3)≤1 ∧ T.array input=w.map bitNat ∧
      match Statement.readEquivalence p e w with
      | none => T.scalar (r 3)=0
      | some (left,right,k) => T.scalar (r 3)=1 ∧ T.scalar (r 2)=k ∧
          EncodesFirst p T left ∧ IdentificationParsing.EncodesTensor p T.left right := by
  have h2 : 2≤M := (pow_le_pow_right' (by decide : 1≤2) (by omega : 1≤w.length+1)).trans binaryRoom
  obtain ⟨initRun,hV⟩ := atoms_runs bounded initializeInput
    (by simp [initializeInput,ValidAtoms,Atom.Valid,Atom.SmallResult];omega)
  let V := applyAtoms initializeInput S
  have vpos : V.scalar (r 0)=0 := by simp [V,applyAtoms,initializeInput,Atom.apply,Store.setScalar,r,ValidatedTensorProgram.r]
  have vlen : V.scalar (r 1)=w.length := by simp [V,applyAtoms,initializeInput,Atom.apply,Store.setScalar,r,ValidatedTensorProgram.r,inputEq]
  have vvalid : V.scalar (r 3)=1 := by simp [V,applyAtoms,initializeInput,Atom.apply,Store.setScalar,r,ValidatedTensorProgram.r]
  obtain ⟨U,u,hu,first,hU,upos,ulen,uvalid,uinput,uright,spec⟩ := parseTensor_runs p V w 0 M hV room fieldRoom powerRoom
    vpos (by omega) vlen vvalid inputEq
  simp only [List.drop_zero] at spec
  cases parsed : Statement.readTensor p w with
  | none =>
    have uz : U.scalar (r 3)=0 := by simpa only [parsed] using spec
    refine ⟨U,3+(u+1),by unfold parseCost;omega,
      .seq initRun (.seq first (.branch_zero uz (.skip (Store.size_le_of_bounded hU)))),hU,uvalid,uinput,?_⟩
    simpa [Statement.readEquivalence,parsed] using uz
  | some val =>
    rcases val with ⟨left,tail⟩
    have hs : U.scalar (r 3)=1 ∧ IdentificationParsing.EncodesTensor p U.left left ∧
        w.drop (U.scalar (r 0))=tail := by simpa only [parsed] using spec
    obtain ⟨saveRun,hW⟩ := atoms_runs hU snapshot (by simp [snapshot,ValidAtoms,Atom.Valid,Atom.SmallResult])
    let W := applyAtoms snapshot U
    have wleft : W.left=U.left := by
      apply Store.ext <;> intro x <;>
        simp [W,applyAtoms,snapshot,Atom.apply,Store.setScalar,Store.setArray,Store.left,saved]
    have firstData : EncodesFirst p W left := by
      rcases hs.2.1 with ⟨hn,hm,hc⟩
      refine ⟨?_,?_,?_⟩
      · simpa [W,applyAtoms,snapshot,Atom.apply,Store.setScalar,Store.setArray,saved,r,output,Store.left] using hn
      · simpa [W,applyAtoms,snapshot,Atom.apply,Store.setScalar,Store.setArray,saved,r,output,Store.left] using hm
      · simpa [W,applyAtoms,snapshot,Atom.apply,Store.setScalar,Store.setArray,saved,r,output,Store.left] using hc
    obtain ⟨X,x,hx,second,hX,xpos,xlen,xvalid,xinput,xright,spec'⟩ := parseTensor_runs p W w (U.scalar (r 0)) M hW room fieldRoom powerRoom
      (by change W.left.scalar (ValidatedTensorProgram.r 0)=_;rw [wleft];rfl) upos
      (by change W.left.scalar (ValidatedTensorProgram.r 1)=_;rw [wleft];exact ulen)
      (by change W.left.scalar (ValidatedTensorProgram.r 3)=_;rw [wleft];exact hs.1)
      (by change W.left.array ValidatedTensorProgram.input=_;rw [wleft];exact uinput)
    rw [hs.2.2] at spec'
    have firstData' : EncodesFirst p X left := by
      have hn := congrArg (fun Z : Store (Fin 2) Unit=>Z.scalar 0) xright
      have hm := congrArg (fun Z : Store (Fin 2) Unit=>Z.scalar 1) xright
      have ha := congrArg (fun Z : Store (Fin 2) Unit=>Z.array ()) xright
      exact ⟨hn.trans firstData.1,hm.trans firstData.2.1,ha.trans firstData.2.2⟩
    cases parsed' : Statement.readTensor p tail with
    | none =>
      have xz : X.scalar (r 3)=0 := by simpa only [parsed'] using spec'
      refine ⟨X,3+(u+((3+(x+1))+1)),by unfold parseCost;omega,
        .seq initRun (.seq first (.branch_nonzero (by omega)
          (.seq saveRun (.seq second (.branch_zero xz (.skip (Store.size_le_of_bounded hX))))))),hX,xvalid,xinput,?_⟩
      simpa [Statement.readEquivalence,parsed,parsed'] using xz
    | some val' =>
      rcases val' with ⟨right,bits⟩
      have hs' : X.scalar (r 3)=1 ∧ IdentificationParsing.EncodesTensor p X.left right ∧
          w.drop (X.scalar (r 0))=bits := by simpa only [parsed'] using spec'
      obtain ⟨Y,t,ht,last,hY,ypos,ylen,yvalid,yinput,dims⟩ := DimensionParser.program_runs e IdentificationParsing.dimensionRegs
        ValidatedTensorProgram.input X.left w (X.scalar (r 0)) M hX.left h2 rfl xlen xinput xpos binaryRoom
      let T := Y.join X.right
      have hT : T.Bounded M := hY.join hX.right
      have last' : Runs (storageBound Reg Arr M) (dimension e) X t T := last.left_bounded hX
      have secondData : IdentificationParsing.EncodesTensor p T.left right :=
        IdentificationParsing.dimension_tensor_frame p last right hs'.2.1
      have firstData'' : EncodesFirst p T left := firstData'
      change Statement.readDimension e (w.drop (X.scalar (r 0)))=
        if T.scalar (r 3)=0 then none else some (T.scalar (r 2)) at dims
      change T.scalar (r 3)≤1 at yvalid
      rw [hs'.2.2] at dims
      refine ⟨T,3+(u+((3+(x+(t+1)))+1)),by unfold parseCost;omega,
        .seq initRun (.seq first (.branch_nonzero (by omega)
          (.seq saveRun (.seq second (.branch_nonzero (by omega) last'))))),hT,yvalid,yinput,?_⟩
      by_cases hz : T.scalar (r 3)=0
      · simp [Statement.readEquivalence,parsed,parsed',dims,hz]
      · have hone : T.scalar (r 3)=1 := by omega
        simpa [Statement.readEquivalence,parsed,parsed',dims,hz] using
          And.intro hone (And.intro firstData'' secondData)

end GroupWL.MachinePrograms.EquivalenceParsing
