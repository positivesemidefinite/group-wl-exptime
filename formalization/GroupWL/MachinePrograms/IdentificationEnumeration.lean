import GroupWL.MachinePrograms.IdentificationTest
import GroupWL.MachinePrograms.NatArrayPredicateLoop

/-! Actual bounded enumeration of all compact p-group candidates. The bound
p^(D^3) is itself computed by the program. -/
namespace GroupWL.MachinePrograms.IdentificationEnumeration
open NatArrayLanguage
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false

abbrev Reg := NatArrayPredicateSearch.Reg IdentificationTest.Reg
abbrev Arr := NatArrayPredicateSearch.Arr IdentificationTest.Arr
abbrev State := Store Reg Arr
abbrev Code := Program Reg Arr
instance : DecidableEq Reg := inferInstance
instance : DecidableEq Arr := inferInstance
instance : Fintype Reg := inferInstance
instance : Fintype Arr := inferInstance

def dimension : Reg := .inl (.inl (.inr .dimension))
def result : Reg := .inr .found

def powerRegs : Fin 5 ↪ Reg :=
  ⟨![.inr .flag,.inr .index,.inr .limit,.inr .todo,.inr .one],by decide⟩
def prepare (p : ℕ) : List (Atom Reg Arr) := [
  .const (.inr .flag) p,.copy (.inr .index) dimension,
  .binary .mul (.inr .index) (.inr .index) (.inr .index),
  .binary .mul (.inr .index) (.inr .index) dimension]
def search (p : ℕ) (word : Bool) : Code := NatArrayPredicateSearch.search
  (IdentificationTest.test p word) IdentificationTest.inputCode IdentificationTest.result
def normalize : List (Atom Reg Arr) := [
  .const (.inr .flag) 0,.binary .eq result result (.inr .flag)]
def identify (p : ℕ) (word : Bool) : Code := .seq (atoms (prepare p))
  (.seq (power powerRegs) (.seq (search p word) (atoms normalize)))

def cost (p D B : ℕ) : ℕ := p^(D^3)*(IdentificationTest.testCost p D B+9)+3*(D^3)+16

variable {p D : ℕ} [Fact p.Prime]
variable {G : Type} [Group G] [Fintype G] [DecidableEq G]

def Good (e : G≃Fin (p^D)) (a : Fin D→Fin (p^D)) (k : ℕ) (S : IdentificationTest.State) : Prop :=
  IdentificationCandidate.Input e a S.left ∧ S.scalar (.inl (.inr .arity))=k

theorem good_setCode (e : G≃Fin (p^D)) (a : Fin D→Fin (p^D)) (k : ℕ)
    (S : IdentificationTest.State) (q : ℕ) (h : Good e a k S) :
    Good e a k (S.setScalar IdentificationTest.inputCode q) := by
  rcases h with ⟨h,hk⟩
  refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
  all_goals simpa [IdentificationTest.inputCode,Store.left,Store.setScalar] using
    (by first | exact h.dimension | exact h.order | exact h.table | exact h.generators | exact hk)

theorem search_runs (version : Refinement.Version) (word : Bool) (k B : ℕ)
    (e : G≃Fin (p^D)) (a : Fin D→Fin (p^D))
    (ha : Refinement.Generates (e.symm ∘ a)) (he : (e 1).val=0)
    (contract : IdentificationTest.WLContract version word k B e)
    (S : State) (hb : S.Bounded B) (hg : Good e a k S.left)
    (hlimit : S.scalar (.inr .limit)=p^(D^3))
    (hroom : ((p^D)*(p^D))*((p^D)*(p^D))≤B) (hpow : (p^D)^D≤B) (hexp : 2*p≤B) :
    ∃t≤p^(D^3)*(IdentificationTest.testCost p D B+9)+6,∃T,
      Runs (storageBound Reg Arr B) (search p word) S t T ∧ T.Bounded B ∧ Good e a k T.left ∧
      T.scalar result≤1 ∧ (T.scalar result=0 ↔ NumericPGroupCandidates.IdentifiesCandidates (p:=p) version k D G) := by
  classical
  let P : ℕ→Prop := fun q=>¬NumericPGroupCandidates.CandidateGood (p:=p) version k D G q
  have hB : 1≤B := (one_le_pow₀ (pow_pos (Fact.out : p.Prime).pos D)).trans hpow
  have code : ∀U q,U.Bounded B → Good e a k U → U.scalar IdentificationTest.inputCode=q → q<p^(D^3) →
      ∃t≤IdentificationTest.testCost p D B,∃V,
        Runs (storageBound IdentificationTest.Reg IdentificationTest.Arr B) (IdentificationTest.test p word) U t V ∧
        V.Bounded B ∧ Good e a k V ∧ (V.scalar IdentificationTest.result=1 ↔ P q) := by
    intro U q hU good hq _
    obtain ⟨t,ht,V,run,hV,fixed,bit,out⟩ := IdentificationTest.test_runs version word k B e a ha he contract
      U q hU good.1 good.2 hq hroom hpow hexp
    refine ⟨t,ht,V,run,hV,?_,out⟩
    rcases good with ⟨good,hk⟩
    refine ⟨⟨?_,?_,?_,?_⟩,?_⟩
    · change V.left.right.scalar .dimension=D; rw [fixed]; exact good.dimension
    · change V.left.right.scalar .order=p^D; rw [fixed]; exact good.order
    · change V.left.right.array .table=_; rw [fixed]; exact good.table
    · change V.left.right.array .generators=_; rw [fixed]; exact good.generators
    · change V.left.right.scalar .arity=k; rw [fixed]; exact hk
  obtain ⟨t,ht,T,run,hT,good,out,index⟩ := NatArrayPredicateSearch.search_runs
    (IdentificationTest.test p word) IdentificationTest.inputCode IdentificationTest.result
    (Good e a k) P S B (p^(D^3)) (IdentificationTest.testCost p D B) hb hB hg
    (fun U q h=>good_setCode e a k U q h) code hlimit
  refine ⟨t,ht,T,run,hT,good,?_,?_⟩
  · change T.scalar (.inr .found)≤1; rw [out]; split_ifs <;> omega
  · change T.scalar (.inr .found)=0 ↔ _
    rw [out]
    have hh := NatArrayPredicateSearch.hit_isSome_iff P (p^(D^3))
    unfold NumericPGroupCandidates.IdentifiesCandidates
    cases hv : (NatArrayPredicateSearch.hit P (p^(D^3))).isSome <;>
      simp only [hv,Bool.false_eq_true,ite_false,ite_true] at hh ⊢
    · simp only [false_iff,not_exists,not_and,not_not,P] at hh
      exact ⟨fun _=>hh,fun _=>True.intro⟩
    · constructor
      · omega
      · intro all
        obtain ⟨q,hq,bad⟩ := hh.mp True.intro
        exact False.elim (bad (all q hq))

theorem identify_runs (version : Refinement.Version) (word : Bool) (k B : ℕ)
    (e : G≃Fin (p^D)) (a : Fin D→Fin (p^D))
    (ha : Refinement.Generates (e.symm ∘ a)) (he : (e 1).val=0) (hk : k≠0)
    (contract : IdentificationTest.WLContract version word k B e)
    (S : State) (hb : S.Bounded B) (hg : Good e a k S.left)
    (hroom : ((p^D)*(p^D))*((p^D)*(p^D))≤B) (hpow : (p^D)^D≤B) (hexp : 2*p≤B)
    (hcube : D^3≤B) (hcount : p^(D^3)≤B) :
    ∃t≤cost p D B,∃T,Runs (storageBound Reg Arr B) (identify p word) S t T ∧ T.Bounded B ∧
      T.scalar result≤1 ∧ (T.scalar result=1 ↔ Refinement.Identifies version k G) := by
  have hp : 0<p := (Fact.out : p.Prime).pos
  have hB : 1≤B := (one_le_pow₀ hp).trans hcount
  have hD : S.scalar dimension=D := hg.1.dimension
  have hsquare : D*D≤B := by
    by_cases hD0 : D=0
    · simp [hD0]
    · have hp : D^2≤D^3 := Nat.pow_le_pow_right (by omega) (by omega)
      simpa [pow_two] using hp.trans hcube
  have hDexplicit : S.scalar (.inl (.inl (.inr .dimension)))=D := hD
  have valid : ValidAtoms B (prepare p) S := by
    simp [prepare,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,BinaryOp.eval,Store.setScalar,
      dimension,hDexplicit,show p≤B by omega,hsquare,show D*D*D≤B by simpa [pow_succ,pow_two] using hcube]
  obtain ⟨pre,hU⟩ := atoms_runs hb (prepare p) valid
  let U := applyAtoms (prepare p) S
  have base : U.scalar (powerRegs 0)=p := by
    simp [U,applyAtoms,prepare,Atom.apply,BinaryOp.eval,Store.setScalar,powerRegs,dimension]
  have exponent : U.scalar (powerRegs 1)=D^3 := by
    simp [U,applyAtoms,prepare,Atom.apply,BinaryOp.eval,Store.setScalar,powerRegs,dimension] at hD ⊢
    rw [hD]; ring
  obtain ⟨V,powerRun,hV,limit⟩ := power_runs powerRegs U p (D^3) B hU hp base exponent hcount
  have leftU : U.left=S.left := by
    apply Store.ext <;> intro r <;> simp [U,applyAtoms,prepare,Atom.apply,Store.left,Store.setScalar]
  have leftV : V.left=U.left := by
    apply Store.ext
    · intro r
      exact powerRun.scalar_eq_of_not_mem (.inl r)
        (by simp [power,powerLoop,powerBody,powerRegs,atoms,NatArrayLanguage.sequence,Program.scalarWrites,Atom.scalarWrites])
    · intro a
      exact powerRun.array_eq_of_not_mem (.inl a)
        (by simp [power,powerLoop,powerBody,powerRegs,atoms,NatArrayLanguage.sequence,Program.arrayWrites,Atom.arrayWrites])
  obtain ⟨t,ht,W,run,hW,good,bit,out⟩ := search_runs version word k B e a ha he contract V hV
    (by rw [leftV,leftU]; exact hg) (by simpa [powerRegs] using limit) hroom hpow hexp
  obtain ⟨last,hT⟩ := atoms_runs hW normalize
    (by
      simp [normalize,ValidAtoms,Atom.Valid,Atom.SmallResult,Atom.apply,Store.setScalar,result,BinaryOp.eval]
      split_ifs <;> omega)
  let T := applyAtoms normalize W
  have value : T.scalar result=if W.scalar result=0 then 1 else 0 := by
    simp [T,normalize,applyAtoms,Atom.apply,BinaryOp.eval,Store.setScalar,result]
  refine ⟨4+((3*(D^3)+4)+(t+2)),by unfold cost;omega,T,
    .seq pre (.seq powerRun (.seq run last)),hT,?_,?_⟩
  · rw [value]; split_ifs <;> omega
  · rw [value]
    have hc : Nat.card G=p^D := by rw [Nat.card_congr e,Nat.card_fin]
    have semantic := NumericPGroupCandidates.identifies_iff_candidates (p:=p) version hk hc
    simpa using out.trans semantic.symm

end GroupWL.MachinePrograms.IdentificationEnumeration
