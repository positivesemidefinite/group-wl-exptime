import GroupWL.MachinePrograms.NatArrayExpressionExecution
import GroupWL.MachinePrograms.ArrayMaterialization

/-! Finite scratch registers and a reusable table loop for compiled expressions. -/
namespace GroupWL.MachinePrograms.NatArrayExpressions
open NatArrayLanguage
set_option maxHeartbeats 4000000
variable {R A R' A' : Type*}

def Expr.map (f : R → R') (g : A → A') : Expr R A → Expr R' A'
  | .const n=>.const n
  | .scalar r=>.scalar (f r)
  | .read a i=>.read (g a) (i.map f g)
  | .binary op a b=>.binary op (a.map f g) (b.map f g)
  | .branch c a b=>.branch (c.map f g) (a.map f g) (b.map f g)

@[simp] theorem Expr.map_need (e : Expr R A) (f : R → R') (g : A → A') :
    (e.map f g).need=e.need := by induction e <;> simp_all [map,need]
@[simp] theorem Expr.map_cost (e : Expr R A) (f : R → R') (g : A → A') :
    (e.map f g).cost=e.cost := by induction e <;> simp_all [map,cost]

variable [DecidableEq R] [DecidableEq A]
abbrev Registers (R : Type*) (n : ℕ) := R ⊕ Fin (n+1)

def inputs {n : ℕ} (S : Store (Registers R n) A) : Store R A :=
  ⟨fun r=>S.scalar (.inl r),S.array⟩
def destination (n : ℕ) : Registers R n := .inr 0
def scratch (n : ℕ) : List (Registers R n) := List.ofFn (fun i : Fin n => Sum.inr i.succ)
def expressionProgram (e : Expr R A) : NatArrayLanguage.Program (Registers R e.need) A :=
  (e.map Sum.inl id).compile (destination _) (scratch _)

@[simp] theorem Expr.map_inputs_eval (e : Expr R A) {n : ℕ} (S : Store (Registers R n) A) :
    (e.map Sum.inl id).eval S=e.eval (inputs S) := by
  induction e <;> simp_all [Expr.map,Expr.eval,inputs]
@[simp] theorem Expr.map_inputs_safe (e : Expr R A) {n : ℕ} (S : Store (Registers R n) A) (M : ℕ) :
    (e.map Sum.inl id).Safe M S↔e.Safe M (inputs S) := by
  induction e <;> simp_all [Expr.map,Expr.Safe,inputs]

theorem map_variables (e : Expr R A) {n : ℕ} :
    (e.map (Sum.inl : R → Registers R n) id).variables=e.variables.image Sum.inl := by
  induction e <;> simp_all [Expr.map,Expr.variables,Finset.image_union]

theorem scratch_nodup (n : ℕ) : ((destination (R:=R) n)::scratch n).Nodup := by
  simp only [List.nodup_cons,destination,scratch,List.mem_ofFn,List.nodup_ofFn]
  constructor
  · rintro ⟨i,h⟩
    have he : (i.succ : Fin (n+1))=0 := Sum.inr.inj h
    have := congrArg Fin.val he
    simp at this
  · intro i j h
    exact Fin.succ_injective _ (Sum.inr.inj h)

theorem scratch_fresh (e : Expr R A) (n : ℕ) :
    Fresh (e.map (Sum.inl : R → Registers R n) id) (destination n) (scratch n) := by
  intro r hr
  rw [map_variables] at hr
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hr
  simp [destination,scratch]

variable [Fintype R] [Fintype A]

theorem expressionProgram_runs (e : Expr R A) (S : Store (Registers R e.need) A) (M : ℕ)
    (bounded : S.Bounded M) (safe : e.Safe M (inputs S)) :
    ∃t≤e.cost,∃U,Runs (storageBound (Registers R e.need) A M) (expressionProgram e) S t U ∧
      U.Bounded M ∧ U.scalar (destination e.need)=e.eval (inputs S) ∧ inputs U=inputs S := by
  obtain ⟨t,ht,U,run,hU,out⟩ := (e.map Sum.inl id).compile_runs (destination _) (scratch _) S M
    bounded ((e.map_inputs_safe S M).mpr safe) (by simp [scratch])
    (scratch_nodup _) (scratch_fresh e _)
  refine ⟨t,by simpa using ht,U,run,hU,by simpa using out,?_⟩
  apply Store.ext
  · intro r
    apply run.scalar_eq_of_not_mem (.inl r)
    intro h
    have hh := (e.map Sum.inl id).compile_writes (destination _) (scratch _) h
    simpa [destination,scratch] using hh
  · intro a
    exact run.array_eq_of_not_mem a (by simp [(e.map Sum.inl id).compile_arrays])

def tableProgram (e : Expr R A) (reg : Fin 5 ↪ R) (output : A) :
    NatArrayLanguage.Program (Registers R e.need) A :=
  materialize (reg.trans ⟨Sum.inl,Sum.inl_injective⟩) output (destination e.need) (expressionProgram e)

theorem inputs_setScalar {n : ℕ} (S : Store (Registers R n) A) (r : R) (v : ℕ) :
    inputs (S.setScalar (.inl r) v)=(inputs S).setScalar r v := by
  apply Store.ext
  · intro s; simp [inputs,Store.setScalar]; rfl
  · intro a; rfl

theorem tableProgram_runs (e : Expr R A) (reg : Fin 5 ↪ R) (output : A)
    (P : Store R A → Prop) (f : ℕ → ℕ) (M n : ℕ) (room : 1≤M)
    (scalarStable : ∀S,P S → ∀i : Fin 4,∀v,P (S.setScalar (reg i.succ) v))
    (outputStable : ∀S,P S → ∀xs,P (S.setArray output xs))
    (safe : ∀S,P S → S.Bounded M → S.scalar (reg 1)<n → e.Safe M S)
    (meaning : ∀S,P S → S.scalar (reg 1)<n → e.eval S=f (S.scalar (reg 1)))
    (S : Store (Registers R e.need) A) (bounded : S.Bounded M) (pre : P (inputs S))
    (length : S.scalar (.inl (reg 0))=n) :
    ∃t≤n*(e.cost+4)+6,∃U,Runs (storageBound (Registers R e.need) A M)
      (tableProgram e reg output) S t U ∧ U.Bounded M ∧ P (inputs U) ∧
      U.array output=List.ofFn (fun i : Fin n=>f i.val) := by
  let rr : Fin 5 ↪ Registers R e.need := reg.trans ⟨Sum.inl,Sum.inl_injective⟩
  have stable : ∀S,P (inputs S) → ∀i : Fin 4,∀v,P (inputs (S.setScalar (rr i.succ) v)) := by
    intro S hS i v
    change P (inputs (S.setScalar (.inl (reg i.succ)) v))
    rw [inputs_setScalar]
    exact scalarStable _ hS i v
  have arrays : ∀S : Store (Registers R e.need) A,P (inputs S) → ∀xs,P (inputs (S.setArray output xs)) := by
    intro S hS xs
    exact outputStable _ hS xs
  have body : ∀S,P (inputs S) → S.Bounded M → S.scalar (rr 1)<n →
      ∃t≤e.cost,∃U,Runs (storageBound (Registers R e.need) A M) (expressionProgram e) S t U ∧
        U.Bounded M ∧ P (inputs U) ∧ U.scalar (destination e.need)=f (S.scalar (rr 1)) ∧
        U.array output=S.array output ∧ ∀i : Fin 4,U.scalar (rr i.castSucc)=S.scalar (rr i.castSucc) := by
    intro S hS hB hi
    have hb : (inputs S).Bounded M := ⟨fun r=>hB.1 (.inl r),hB.2⟩
    obtain ⟨t,ht,U,run,hU,out,frame⟩ := expressionProgram_runs e S M hB (safe _ hS hb hi)
    refine ⟨t,ht,U,run,hU,frame ▸ hS,out.trans (meaning _ hS hi),?_,?_⟩
    · exact congrArg (fun W : Store R A=>W.array output) frame
    · intro i
      exact congrArg (fun W : Store R A=>W.scalar (reg i.castSucc)) frame
  exact materialize_runs rr output (destination _) (expressionProgram e) (fun S=>P (inputs S))
    f M n e.cost room stable arrays body S bounded pre length

end GroupWL.MachinePrograms.NatArrayExpressions
