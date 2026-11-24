import GroupWL.MachinePrograms.CompilerOutput

/-! Emit fixed per-bit words while preserving the runtime bit string. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

def mapWord (f : Bool → List Bool) (xs : List Bool) : List Bool := (xs.map f).flatten

@[simp] theorem mapWord_nil (f : Bool → List Bool) : mapWord f [] = [] := rfl
@[simp] theorem mapWord_cons (f : Bool → List Bool) (b : Bool) (xs : List Bool) :
    mapWord f (b::xs) = f b++mapWord f xs := rfl

def emitMapLoop (counter output : K) (f : Bool → List Bool) : Program K :=
  .while counter Option.isSome
    (.pop counter .skip (emitFixed output (f false)) (emitFixed output (f true)))

theorem emitMapLoop_runs (counter output : K) (hne : counter ≠ output)
    (f : Bool → List Bool) (xs : List Bool) :
    ∀ S : Store K, S counter = xs →
      Runs (emitMapLoop counter output f) S ((mapWord f xs).length+2*xs.length+1)
        (Function.update (Function.update S counter []) output
          ((mapWord f xs).reverse++S output)) := by
  induction xs with
  | nil =>
    intro S hs
    have hreset : Function.update S counter [] = S := by rw [← hs,Function.update_eq_self]
    have he : Function.update (Function.update S counter []) output
        ((mapWord f []).reverse++S output) = S := by simp [hreset]
    rw [he]
    exact Runs.while_false (by simp [hs])
  | cons b xs ih =>
    intro S hs
    let S₀ := Function.update S counter xs
    let S₁ := Function.update S₀ output ((f b).reverse++S output)
    have first : Runs (.pop counter .skip (emitFixed output (f false)) (emitFixed output (f true)))
        S ((f b).length+1) S₁ := by
      apply Runs.pop
      have hr := emitFixed_runs S₀ output (f b)
      cases b <;> simpa [select,hs,S₀,S₁,Ne.symm hne] using hr
    have rest := ih S₁ (by simp [S₁,S₀,hne])
    have hr := Runs.while_true (test := Option.isSome) (by simp [hs]) first rest
    have he : Function.update (Function.update S₁ counter []) output
        ((mapWord f xs).reverse++S₁ output) =
        Function.update (Function.update S counter []) output
          ((mapWord f (b::xs)).reverse++S output) := by
      funext k
      by_cases hk : k = output
      · subst k
        simp [S₁,mapWord_cons,List.reverse_append,List.append_assoc]
      · by_cases hk' : k = counter
        · subst k; simp [hne]
        · simp [S₁,S₀,Function.update_of_ne hk,Function.update_of_ne hk']
    rw [he] at hr
    convert hr using 1
    simp only [mapWord_cons,List.length_append,List.length_cons]
    omega

/-- Registers are the preserved bit string, reversed output, copied cursor,
and scratch. Each runtime symbol selects one of two fixed emitted words. -/
def emitMap (reg : Fin 4 ↪ K) (f : Bool → List Bool) : Program K :=
  .seq (copy (reg 0) (reg 2) (reg 3)) (emitMapLoop (reg 2) (reg 1) f)

theorem emitMap_runs (S : Store K) (reg : Fin 4 ↪ K) (f : Bool → List Bool)
    (hc : S (reg 2) = []) (ht : S (reg 3) = []) :
    Runs (emitMap reg f) S ((mapWord f (S (reg 0))).length+9*(S (reg 0)).length+3)
      (Function.update S (reg 1) ((mapWord f (S (reg 0))).reverse++S (reg 1))) := by
  have hne {i j : Fin 4} (h : i ≠ j) : reg i ≠ reg j := fun he => h (reg.injective he)
  have heq (i j : Fin 4) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let S' := Function.update S (reg 2) (S (reg 0))
  have first : Runs (copy (reg 0) (reg 2) (reg 3)) S (7*(S (reg 0)).length+2) S' := by
    simpa [S',hc] using copy_runs S (reg 0) (reg 2) (reg 3)
      (hne (by decide)) (hne (by decide)) (hne (by decide)) ht
  have rest := emitMapLoop_runs (reg 2) (reg 1) (hne (by decide)) f (S (reg 0)) S'
    (by simp [S'])
  have hreset : Function.update S' (reg 2) [] = S := by
    simp only [S',Function.update_idem]
    rw [← hc,Function.update_eq_self]
  rw [hreset] at rest
  have hout : S' (reg 1) = S (reg 1) := by simp [S',heq]
  rw [hout] at rest
  have hr := Runs.seq first rest
  convert hr using 1
  omega

open AddressedCircuit CircuitDescription

theorem domainWord_singleton {d : ℕ} (a : Address d) :
    domainWord (ProductDomain.singleton a) = mapWord (fun b => [!b,b]) (List.ofFn a) := by
  unfold domainWord mapWord
  rw [List.map_ofFn]
  congr 2
  funext i
  cases ha : a i <;> simp [ProductDomain.singleton,ha]

theorem singletonMask_length (xs : List Bool) :
    (mapWord (fun b => [!b,b]) xs).length = 2*xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [mapWord_cons,ih]; omega

def emitSingletonDomain (reg : Fin 4 ↪ K) : Program K := emitMap reg (fun b => [!b,b])

theorem emitSingletonDomain_runs (S : Store K) (reg : Fin 4 ↪ K) {d : ℕ} (a : Address d)
    (ha : S (reg 0) = List.ofFn a) (hc : S (reg 2) = []) (ht : S (reg 3) = []) :
    Runs (emitSingletonDomain reg) S (11*d+3)
      (Function.update S (reg 1) ((domainWord (ProductDomain.singleton a)).reverse++S (reg 1))) := by
  have hr := emitMap_runs S reg (fun b => [!b,b]) hc ht
  rw [singletonMask_length,ha,List.length_ofFn,← domainWord_singleton] at hr
  convert hr using 1
  omega

end GroupWL.MachinePrograms.Structured
