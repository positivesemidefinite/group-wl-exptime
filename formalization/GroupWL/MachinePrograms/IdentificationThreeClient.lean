import GroupWL.MachinePrograms.IdentificationThreeEnumeration
import GroupWL.MachinePrograms.IdentificationGenerators

/-! Full table-input Version III identification program. It computes its own source
generators and enumerates every compact candidate, with no algorithmic premise. -/
namespace GroupWL.MachinePrograms.IdentificationThreeClient
open NatArrayLanguage
set_option maxHeartbeats 2000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
abbrev Reg := GeneratorChoice.Reg ⊕ IdentificationThreeEnumeration.Reg
abbrev Arr := GeneratorChoice.Arr ⊕ IdentificationThreeEnumeration.Arr
abbrev State := Store Reg Arr
abbrev Code := NatArrayLanguage.Program Reg Arr
instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def source (r : IdentificationCandidate.InputReg) : Reg := .inr (.inl (.inl (.inr r)))
def sourceArray (a : IdentificationCandidate.InputArr) : Arr := .inr (.inl (.inl (.inr a)))
def result : Reg := .inr IdentificationThreeEnumeration.result

def prepare : List (Atom Reg Arr) := [
  .copy (.inl (GeneratorChoice.decoderReg .n)) (source .order),
  .copy (.inl (GeneratorChoice.decoderReg .arity)) (source .dimension),
  .const (.inl (GeneratorChoice.seedReg .identity)) 0,
  .copyArray (.inl (GeneratorChoice.closureArr .table)) (sourceArray .table)]
def copyGenerators : Atom Reg Arr :=
  .copyArray (sourceArray .generators) (.inl (GeneratorChoice.decoderArr .vector))
def identify (p : ℕ) : Code := .seq (atoms prepare)
  (.seq (GeneratorChoice.choose.map Sum.inl Sum.inl)
    (.seq (.atom copyGenerators) ((IdentificationThreeEnumeration.identify p).map Sum.inr Sum.inr)))

def cost (p D B : ℕ) : ℕ :=
  (p^D)^D*(10*(p^D)^3+13*(p^D)+11*D+35)+9*D+25+IdentificationThreeEnumeration.cost p D B

variable {p D k B : ℕ} [Fact p.Prime]
variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

theorem identify_runs (e : G≃Fin (p^D)) (he : (e 1).val=0) (hk : k≠0)
    (S : State) (hb : S.Bounded B)
    (hd : S.scalar (source .dimension)=D) (hn : S.scalar (source .order)=p^D)
    (hkS : S.scalar (source .arity)=k)
    (ht : S.array (sourceArray .table)=GroupInitial.tableWord (fun x y=>e (e.symm x*e.symm y)))
    (hroom : ((p^D)*(p^D))*((p^D)*(p^D))≤B) (hpow : (p^D)^D≤B) (hexp : 2*p≤B)
    (hcube : D^3≤B) (hcount : p^(D^3)≤B)
    (sq : (IndexedGadget.size (p^D))^2≤B)
    (matrix : GraphMatrixPrograms.Room (IndexedGadget.size (p^D)) (IndexedGadget.size (p^D)) k B)
    (room : IndexedWL.Room ((IndexedGadget.size (p^D))^k+(IndexedGadget.size (p^D))^k) k
      (IndexedGadget.size (p^D)) B) :
    ∃t≤cost p D B,∃T,Runs (storageBound Reg Arr B) (identify p) S t T ∧ T.Bounded B ∧
      T.scalar result≤1 ∧ (T.scalar result=1 ↔ Refinement.Identifies .three k G) := by
  obtain ⟨prep,hU⟩ := atoms_runs hb prepare
    (by simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult])
  let U := applyAtoms prepare S
  have inputs : U.left.scalar (GeneratorChoice.decoderReg .n)=p^D ∧
      U.left.scalar (GeneratorChoice.decoderReg .arity)=D ∧
      U.left.scalar (GeneratorChoice.seedReg .identity)=(e 1).val ∧
      U.left.array (GeneratorChoice.closureArr .table)=GroupInitial.tableWord (fun x y=>e (e.symm x*e.symm y)) := by
    simp [U,applyAtoms,prepare,Atom.apply,Store.left,Store.setScalar,Store.setArray,
      GeneratorChoice.decoderReg,GeneratorChoice.seedReg,IndexedGeneratorTest.sourceReg,he]
    exact ⟨hn,hd,ht⟩
  obtain ⟨t,htime,V,gen,hV,out⟩ := IdentificationGenerators.choose_runs e U.left B hU.left
    inputs.1 inputs.2.1 inputs.2.2.1 inputs.2.2.2 ((Nat.le_mul_self _).trans hroom) hpow
  let W := V.join U.right
  have hW : W.Bounded B := hV.join hU.right
  have copy := atom_runs hW copyGenerators True.intro True.intro
  have hX : (copyGenerators.apply W).Bounded B := Atom.apply_bounded hW copyGenerators True.intro
  let X := copyGenerators.apply W
  have sourceFrame : U.right=S.right := by
    apply Store.ext <;> intro r <;> simp [U,applyAtoms,prepare,Atom.apply,Store.right,Store.setScalar,Store.setArray]
  have good : IdentificationThreeEnumeration.Good e (IdentificationGenerators.generators e) k X.right.left := by
    refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
    · change X.scalar (source .dimension)=D
      simpa [X,copyGenerators,Atom.apply,W,source,sourceArray,Store.setArray,sourceFrame] using hd
    · change X.scalar (source .order)=p^D
      simpa [X,copyGenerators,Atom.apply,W,source,sourceArray,Store.setArray,sourceFrame] using hn
    · change X.array (sourceArray .table)=_
      simpa [X,copyGenerators,Atom.apply,W,sourceArray,Store.setArray,sourceFrame] using ht
    · change X.array (sourceArray .generators)=_
      simpa [X,copyGenerators,Atom.apply,W,sourceArray,Store.setArray] using out
    · change X.scalar (source .arity)=k
      simpa [X,copyGenerators,Atom.apply,W,source,sourceArray,Store.setArray,sourceFrame] using hkS
  have contract := IdentificationThreeTest.contract e (Nat.pos_of_ne_zero hk) sq matrix room
  obtain ⟨u,hu,Y,enumerate,hY,bit,correct⟩ := IdentificationThreeEnumeration.identify_runs
    .three k B e (IdentificationGenerators.generators e)
    (IdentificationGenerators.generates e) he hk contract X.right hX.right good hroom hpow hexp hcube hcount
  refine ⟨4+(t+(1+u)),by unfold cost;omega,X.left.join Y,
    .seq prep (.seq (gen.left_bounded hU) (.seq copy (enumerate.right_bounded hX))),hX.left.join hY,bit,correct⟩


theorem cost_le {p D B : ℕ} (hp : p ≤ B) (hD : D ≤ B) (hn : p^D ≤ B)
    (hpow : (p^D)^D ≤ B) (hcount : p^(D^3) ≤ B) (hcube : D^3 ≤ B) :
    cost p D B ≤ 5000*(B+1)^8 := by
  have hdec := CandidateExtend.decode_time_le hp hn hD hpow
  have hiso := IsomorphismClient.time_le hn hn hD hpow
  change IdentificationCandidate.isoCost (p^D) D ≤ 200*(B+1)^7 at hiso
  have hcand : IdentificationCandidate.cost p D ≤ 720*(B+1)^7 := by
    unfold IdentificationCandidate.cost
    have h1 : 1 ≤ (B+1)^7 := one_le_pow₀ (by omega)
    omega
  have htest : IdentificationThreeTest.testCost p D B+9 ≤ 2300*(B+1)^7 := by
    unfold IdentificationThreeTest.testCost IdentificationThreeTest.wlCost
    have h1 : 1 ≤ (B+1)^7 := one_le_pow₀ (by omega)
    omega
  have hgen : (p^D)^D*(10*(p^D)^3+13*(p^D)+11*D+35)+9*D+25 ≤ 103*(B+1)^4 := by
    have h1 : 1 ≤ B+1 := by omega
    have h0 : 1 ≤ (B+1)^4 := one_le_pow₀ h1
    have hB : B+1 ≤ (B+1)^4 := by simpa using Nat.pow_le_pow_right h1 (by decide : 1 ≤ 4)
    have hB2 : (B+1)^2 ≤ (B+1)^4 := Nat.pow_le_pow_right h1 (by decide)
    calc
      _ ≤ (B+1)*(10*(B+1)^3+13*(B+1)+11*(B+1)+35)+9*(B+1)+25 := by gcongr <;> omega
      _ = 10*(B+1)^4+24*(B+1)^2+44*(B+1)+25 := by ring
      _ ≤ 103*(B+1)^4 := by omega
  have henum : IdentificationThreeEnumeration.cost p D B ≤ 2320*(B+1)^8 := by
    have hm := Nat.mul_le_mul hcount htest
    have h1 : 1 ≤ B+1 := by omega
    have h0 : 1 ≤ (B+1)^8 := one_le_pow₀ h1
    have hB : B+1 ≤ (B+1)^8 := by simpa using Nat.pow_le_pow_right h1 (by decide : 1 ≤ 8)
    have heq : (B+1)*(2300*(B+1)^7)=2300*(B+1)^8 := by ring
    unfold IdentificationThreeEnumeration.cost
    nlinarith
  have h48 : (B+1)^4 ≤ (B+1)^8 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold cost
  omega
end GroupWL.MachinePrograms.IdentificationThreeClient
