import GroupWL.MachinePrograms.CircuitMetadataExpressionSemantics

/-! Actual finite-register programs materializing each numeric metadata table. -/
namespace GroupWL.MachinePrograms.CircuitMetadataExpressions
open NatArrayLanguage NatArrayExpressions CircuitMetadataValues
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

def static (r : Reg) : Prop := r≠.length ∧ r≠.index ∧ r≠.todo ∧ r≠.one ∧ r≠.zero
instance (r : Reg) : Decidable (static r) := inferInstanceAs (Decidable (_∧_∧_∧_∧_))
def loopRegisters : Fin 5 ↪ Reg := ⟨![.length,.index,.todo,.one,.zero],by decide⟩
def expr (f : Field) : Expr Reg Arr := ((entry f).expression sizeRegister).map id Sum.inl
def program (f : Field) := tableProgram (expr f) loopRegisters (Sum.inr ())

def Frame (base : Store Reg Input) (S : Store Reg Arr) : Prop :=
  (∀r,static r→S.scalar r=base.scalar r) ∧ ∀a,S.array (.inl a)=base.array a

theorem entry_variables (f : Field) (r : Reg)
    (h : r∈((entry f).expression sizeRegister).variables) : r=.index ∨ static r := by
  cases f <;> cases r <;> first | decide +kernel | exact absurd h (by decide +kernel)

theorem entry_literals (f : Field) : (entry f).Literals 6 := by
  cases f <;> simp [entry,dimension,source,target,sourceForm,targetForm,domain,permutation,
    connectionSource,connectionTarget,connectionSourceForm,connectionTargetForm,
    connectionDomain,connectionPermutation,connectionCase,pairIf,sourceGate,gateOutput,
    schemaStride,requestStride,num,reg,rd,add,sub,mul,quo,rem,eq,lt,branch,Total.Literals]

theorem Total.literals_mono {R A : Type*} (e : Total R A) {a b : ℕ}
    (h : e.Literals a) (hab : a≤b) : e.Literals b := by
  induction e with
  | const n=>exact h.trans hab
  | scalar r=>trivial
  | read a i ih=>exact ih h
  | binary op a b ia ib=>exact ⟨ia h.1,ib h.2⟩
  | branch c a b ic ia ib=>exact ⟨ic h.1,ia h.2.1,ib h.2.2⟩

theorem Frame.scalar (base : Store Reg Input) (S : Store Reg Arr) (h : Frame base S)
    (i : Fin 4) (v : ℕ) : Frame base (S.setScalar (loopRegisters i.succ) v) := by
  refine ⟨?_,h.2⟩
  intro r hr
  have hs := h.1 r hr
  fin_cases i <;> cases r <;> simp_all [static,loopRegisters,Store.setScalar]

theorem Frame.array (base : Store Reg Input) (S : Store Reg Arr) (h : Frame base S)
    (xs : List ℕ) : Frame base (S.setArray (.inr ()) xs) := by
  refine ⟨h.1,?_⟩
  intro a
  simpa [Store.setArray] using h.2 a

theorem Frame.data {base : Store Reg Input} {S : Store Reg Arr} (h : Frame base S) :
    readData (project id Sum.inl S)=readData base := by
  have hs := h.1
  have ha := h.2
  unfold readData
  simp only [project,id_eq]
  rw [hs .types (by decide),hs .coordinates (by decide),hs .edges (by decide),hs .seeds (by decide),
    hs .tests (by decide),hs .ports (by decide),ha .kinds,ha .schemas,ha .seeds,ha .tests,ha .owners,ha .ports]

theorem program_runs (f : Field) (base : Store Reg Input) (B M n : ℕ)
    (room : 6≤B) (lengths : ∀a,base.scalar (sizeRegister a)=(base.array a).length)
    (scalars : ∀r,static r→base.scalar r≤B) (arrays : ∀a x,x∈base.array a→x≤B)
    (nBound : n≤B) (budget : (B+2)^(2*((entry f).expression sizeRegister).cost)≤M)
    (S : Store (Registers Reg (expr f).need) Arr) (bounded : S.Bounded M)
    (pre : Frame base (inputs S)) (count : S.scalar (.inl .length)=n) :
    ∃t≤n*((expr f).cost+4)+6,∃U,
      Runs (storageBound (Registers Reg (expr f).need) Arr M) (program f) S t U ∧ U.Bounded M ∧
      Frame base (inputs U) ∧ U.array (.inr ())=
        List.ofFn (fun i : Fin n=>value (readData base) f i.val) := by
  have hM : 1≤M := (Nat.one_le_pow _ _ (by omega)).trans budget
  have safe : ∀W,Frame base W→W.Bounded M→W.scalar (loopRegisters 1)<n→(expr f).Safe M W := by
    intro W hW hb hi
    rw [expr,Expr.map_safe]
    apply Total.expression_safe
    · intro a
      change W.scalar (sizeRegister a)=(W.array (.inl a)).length
      rw [hW.1 _ (by cases a <;> decide),hW.2]
      exact lengths a
    · exact (Total.literals_mono (entry f) (entry_literals f) room)
    · intro r hr
      rcases entry_variables f r hr with h | h
      · subst r; change W.scalar .index≤B; change W.scalar .index<n at hi; omega
      · change W.scalar r≤B; rw [hW.1 r h]; exact scalars r h
    · intro a x hx
      change x∈W.array (.inl a) at hx
      rw [hW.2] at hx
      exact arrays a x hx
    · exact budget
  have meaning : ∀W,Frame base W→W.scalar (loopRegisters 1)<n→
      (expr f).eval W=value (readData base) f (W.scalar (loopRegisters 1)) := by
    intro W hW hi
    rw [expr,Expr.map_eval,Total.expression_eval]
    · rw [entry_eval,hW.data]; rfl
    · intro a
      change W.scalar (sizeRegister a)=(W.array (.inl a)).length
      rw [hW.1 _ (by cases a <;> decide),hW.2]
      exact lengths a
  exact tableProgram_runs (expr f) loopRegisters (.inr ()) (Frame base)
    (value (readData base) f) M n hM (Frame.scalar base) (Frame.array base)
    safe meaning S bounded pre count

end GroupWL.MachinePrograms.CircuitMetadataExpressions
