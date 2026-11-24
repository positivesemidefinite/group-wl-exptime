import GroupWL.MachinePrograms.CandidateDecoderRuntime
import GroupWL.MachinePrograms.IsomorphismClientBounds
import GroupWL.NumericPGroupIdentification

/-! Decode one compact p-group candidate and perform the actual table-based
isomorphism test. The source table and its generating tuple are preserved. -/
namespace GroupWL.MachinePrograms.IdentificationCandidate
open NatArrayLanguage
set_option maxHeartbeats 2500000
set_option maxRecDepth 12000
set_option synthInstance.maxSize 4096
set_option linter.unusedSimpArgs false

inductive InputReg where
  | dimension | order | code | arity
  deriving DecidableEq,Fintype
inductive InputArr where
  | table | generators
  deriving DecidableEq,Fintype
abbrev Reg := (CandidateDecoder.Reg ⊕ IsomorphismClient.Reg) ⊕ InputReg
abbrev Arr := (CandidateDecoder.Arr ⊕ IsomorphismClient.Arr) ⊕ InputArr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def decReg (r : CandidateDecoder.Reg) : Reg := .inl (.inl r)
def decArr (a : CandidateDecoder.Arr) : Arr := .inl (.inl a)
def isoReg (r : IsomorphismClient.Reg) : Reg := .inl (.inr r)
def isoArr (a : IsomorphismClient.Arr) : Arr := .inl (.inr a)
def valid : Reg := decReg (.inr .valid)
def isomorphic : Reg := isoReg IsomorphismClient.resultReg

def prepareDecoder : List (Atom Reg Arr) := [
  .copy (decReg (.inr .dimension)) (.inr .dimension),
  .copy (decReg (.inr .code)) (.inr .code)]
def prepareIsomorphism : List (Atom Reg Arr) := [
  .copy (isoReg (.inl 0)) (.inr .order),
  .copy (isoReg (.inl 1)) (.inr .order),
  .copy (isoReg (IsomorphismClient.decoderReg .arity)) (.inr .dimension),
  .const (isoReg IsomorphismClient.identityReg) 0,
  .const (isoReg IsomorphismClient.identityReg') 0,
  .copyArray (isoArr (.inl 0)) (.inr .table),
  .copyArray (isoArr (.inl 1)) (decArr (.inr .table)),
  .copyArray (isoArr IsomorphismClient.sourceTuple) (.inr .generators)]
def compare : Code := .seq (atoms prepareIsomorphism)
  ((IsomorphismClient.compare.map Sum.inr Sum.inr).map Sum.inl Sum.inl)
def program (p : ℕ) : Code := .seq (atoms prepareDecoder)
  (.seq (((CandidateDecoder.decode p).map Sum.inl Sum.inl).map Sum.inl Sum.inl)
    (.branch valid compare .skip))

def isoCost (n D : ℕ) : ℕ :=
  n^D*(10*(n*n)^3+8*(n*n)+19*D+n*(9*n+13)+19*n*n+49)+15*((n*n)*(n*n))+3*D+34

def cost (p D : ℕ) : ℕ :=
  D*(CandidateExtend.budget p (p^D) D+3*D+20)+isoCost (p^D) D+20

variable {p D : ℕ} [Fact p.Prime]
variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

structure Input (e : G≃Fin (p^D)) (a : Fin D→Fin (p^D)) (S : State) : Prop where
  dimension : S.scalar (.inr .dimension)=D
  order : S.scalar (.inr .order)=p^D
  table : S.array (.inr .table)=GroupInitial.tableWord (fun x y=>e (e.symm x*e.symm y))
  generators : S.array (.inr .generators)=GroupInitial.tupleWord a

theorem compare_runs (e : G≃Fin (p^D)) (a : Fin D→Fin (p^D))
    (ha : Refinement.Generates (e.symm ∘ a)) (he : (e 1).val=0)
    (g : Group (Fin (p^D))) (hg : (NumericGroupGenerators.identity g).val=0)
    (S : State) (M : ℕ) (hb : S.Bounded M) (input : Input e a S)
    (table : S.array (decArr (.inr .table))=GroupInitial.tableWord (NumericGroupGenerators.operation g))
    (hroom : ((p^D)*(p^D))*((p^D)*(p^D))≤M) (hpow : (p^D)^D≤M) :
    ∃t ≤ isoCost (p^D) D+8,∃T,Runs (storageBound Reg Arr M) compare S t T ∧
      T.Bounded M ∧ T.right=S.right ∧ T.left.left=S.left.left ∧
      T.scalar isomorphic≤1 ∧
      (letI := g; letI : Mul (Fin (p^D)) := g.toMul
       T.scalar isomorphic=1 ↔ Nonempty (G≃*Fin (p^D))) := by
  letI := g
  letI : Mul (Fin (p^D)) := g.toMul
  obtain ⟨prep,hU⟩ := atoms_runs hb prepareIsomorphism
    (by simp [prepareIsomorphism,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let U := applyAtoms prepareIsomorphism S
  have hinput : U.left.right.scalar (.inl 0)=p^D ∧ U.left.right.scalar (.inl 1)=p^D ∧
      U.left.right.scalar (IsomorphismClient.decoderReg .arity)=D ∧
      U.left.right.scalar IsomorphismClient.identityReg=(e 1).val ∧
      U.left.right.scalar IsomorphismClient.identityReg'=(NumericGroupGenerators.identity g).val ∧
      U.left.right.array (.inl 0)=GroupInitial.tableWord (fun x y=>e (e.symm x*e.symm y)) ∧
      U.left.right.array (.inl 1)=GroupInitial.tableWord (NumericGroupGenerators.operation g) ∧
      U.left.right.array IsomorphismClient.sourceTuple=GroupInitial.tupleWord a := by
    simp [U,applyAtoms,prepareIsomorphism,Atom.apply,Store.left,Store.right,Store.setScalar,Store.setArray,
      isoReg,isoArr,decArr,IsomorphismClient.decoderReg,IsomorphismClient.innerReg,
      IsomorphismClient.identityReg,IsomorphismClient.identityReg',IsomorphismClient.expansionReg,
      IsomorphismClient.groupReg,PairedImageExpansion.seedReg,PairedImageExpansion.imageReg,
      IsomorphismClient.sourceTuple,IsomorphismClient.innerArr,IndexedImageTest.sourceTuple,
      input.order,input.dimension,input.table,input.generators,table,he,hg]
    exact table
  obtain ⟨t,ht,V,run,hV,bit,correct⟩ := IsomorphismClient.compare_correct e.symm (Equiv.refl _)
    (fun x y=>e (e.symm x*e.symm y)) (NumericGroupGenerators.operation g)
    (by intro x y; simp) (fun _ _=>rfl) (e 1) (NumericGroupGenerators.identity g)
    (by simp) rfl a ha rfl U.left.right M hU.left.right
    hinput.1 hinput.2.1 hinput.2.2.1 hinput.2.2.2.1 hinput.2.2.2.2.1
    hinput.2.2.2.2.2.1 hinput.2.2.2.2.2.2.1 hinput.2.2.2.2.2.2.2 hroom hpow
  let T := (U.left.left.join V).join U.right
  have run' := (run.right_bounded hU.left).left_bounded hU
  refine ⟨8+t,by unfold isoCost; omega,T,.seq prep run',
    (hU.left.left.join hV).join hU.right,?_,?_,bit,correct⟩
  · apply Store.ext <;> intro r <;>
      simp [T,U,applyAtoms,prepareIsomorphism,Atom.apply,Store.right,Store.setScalar,Store.setArray,isoReg,isoArr,decArr]
  · apply Store.ext <;> intro r <;>
      simp [T,U,applyAtoms,prepareIsomorphism,Atom.apply,Store.left,Store.setScalar,Store.setArray,isoReg,isoArr,decArr]

theorem program_runs (e : G≃Fin (p^D)) (a : Fin D→Fin (p^D))
    (ha : Refinement.Generates (e.symm ∘ a)) (he : (e 1).val=0)
    (S : State) (M q : ℕ) (hb : S.Bounded M) (input : Input e a S)
    (hq : S.scalar (.inr .code)=q)
    (hroom : ((p^D)*(p^D))*((p^D)*(p^D))≤M) (hpow : (p^D)^D≤M) (hexp : 2*p≤M) :
    ∃t≤cost p D,∃T,Runs (storageBound Reg Arr M) (program p) S t T ∧ T.Bounded M ∧
      T.right=S.right ∧ CandidateDecoder.Data p D q T.left.left ∧
      ∀g,NumericPGroupCandidates.decode (p:=p) D q=some g →
        letI := g; letI : Mul (Fin (p^D)) := g.toMul
        T.scalar isomorphic≤1 ∧ (T.scalar isomorphic=1 ↔ Nonempty (G≃*Fin (p^D))) := by
  obtain ⟨prep,hU⟩ := atoms_runs hb prepareDecoder
    (by simp [prepareDecoder,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let U := applyAtoms prepareDecoder S
  have hj : U.left.left.scalar (.inr .dimension)=D := by
    simpa [U,applyAtoms,prepareDecoder,Atom.apply,Store.left,Store.setScalar,decReg] using input.dimension
  have hqU : U.left.left.scalar (.inr .code)=q := by
    simpa [U,applyAtoms,prepareDecoder,Atom.apply,Store.left,Store.setScalar,decReg] using hq
  obtain ⟨t,ht,V,run,hV,data,order,code⟩ := CandidateDecoder.decode_runs U.left.left M D q hU.left.left hj hqU hroom hpow hexp
  let W := (V.join U.left.right).join U.right
  have run' := (run.left_bounded hU.left).left_bounded hU
  have hW : W.Bounded M := (hV.join hU.left.right).join hU.right
  have fixed : W.right=S.right := by
    apply Store.ext <;> intro r <;>
      simp [W,U,applyAtoms,prepareDecoder,Atom.apply,Store.right,Store.setScalar,decReg]
  cases h : NumericPGroupCandidates.decode (p:=p) D q with
  | none =>
    have zero : W.scalar valid=0 := by simpa [W,valid,decReg,h] using data.valid
    refine ⟨2+(t+1),by unfold cost;omega,W,.seq prep (.seq run' (.branch_zero zero (.skip run'.end_bound))),
      hW,fixed,data,?_⟩
    intro g hg; simp [h] at hg
  | some g =>
    have one : W.scalar valid≠0 := by
      have hv : W.scalar valid=1 := by simpa [W,valid,decReg,h] using data.valid
      omega
    have inp : Input e a W := by
      constructor
      · change W.right.scalar .dimension=D; rw [fixed]; exact input.dimension
      · change W.right.scalar .order=p^D; rw [fixed]; exact input.order
      · change W.right.array .table=_; rw [fixed]; exact input.table
      · change W.right.array .generators=_; rw [fixed]; exact input.generators
    obtain ⟨u,hu,T,comp,hT,fixT,decT,bit,correct⟩ := compare_runs e a ha he g
      (by simpa [NumericGroupGenerators.identity,NumericPGroupCandidates.identity,NumericPGroupCandidates.zero] using congrArg Fin.val (NumericPGroupCandidates.decode_identity D q g h)) W M hW inp (data.table g h) hroom hpow
    refine ⟨2+(t+(u+1)),by unfold cost;omega,T,.seq prep (.seq run' (.branch_nonzero one comp)),hT,
      fixT.trans fixed,?_,?_⟩
    · rw [decT]; exact data
    · intro g' hg'
      have eqg : g'=g := Option.some.inj hg'.symm
      subst g'
      exact ⟨bit,correct⟩

end GroupWL.MachinePrograms.IdentificationCandidate
