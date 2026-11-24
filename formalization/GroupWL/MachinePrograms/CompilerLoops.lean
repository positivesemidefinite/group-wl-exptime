import GroupWL.MachinePrograms.CountedLoops
import GroupWL.MachinePrograms.CompilerOutput

/-! Operational enumeration of address coordinates with unary index registers. -/
namespace GroupWL.MachinePrograms.Structured

variable {K : Type*} [DecidableEq K]

def prefixWord (word : ℕ → List Bool) (n : ℕ) : List Bool :=
  ((List.range n).map word).flatten

@[simp] theorem prefixWord_zero (word : ℕ → List Bool) : prefixWord word 0 = [] := rfl
@[simp] theorem prefixWord_succ (word : ℕ → List Bool) (n : ℕ) :
    prefixWord word (n+1) = prefixWord word n ++ word n := by
  simp [prefixWord,List.range_succ,List.flatten_append]

theorem prefixWord_ofFn (word : ℕ → List Bool) (n : ℕ) :
    prefixWord word n = (List.ofFn (fun i : Fin n => word i.val)).flatten := by
  have h := List.ofFn_getElem_eq_map (List.range n) word
  simpa only [List.length_range,List.getElem_range,prefixWord] using congrArg List.flatten h.symm

def coordinateLoop (index remaining : K) (body : Program K) : Program K :=
  .while remaining Option.isSome (.seq (discard remaining) (.seq body (.push index true)))

def coordinateState (S : Store K) (index remaining output : K) (d n : ℕ)
    (word : ℕ → List Bool) : Store K :=
  Function.update (Function.update (Function.update S index (List.replicate n true))
    remaining (List.replicate (d-n) true)) output ((prefixWord word n).reverse++S output)

def coordinateCut (S : Store K) (index remaining output : K) (d n : ℕ)
    (word : ℕ → List Bool) : Store K :=
  Function.update (coordinateState S index remaining output d n word) remaining
    (List.replicate (d-n-1) true)

/-- The loop body is fixed executable code. Its per-coordinate output lemma
is composed here with the actual counter updates and all guard costs. -/
theorem coordinateLoop_runs (S : Store K) (index remaining output : K)
    (hir : index ≠ remaining) (hio : index ≠ output) (hro : remaining ≠ output)
    (d B : ℕ) (word : ℕ → List Bool) (body : Program K)
    (hbody : ∀ i < d, ∃ time ≤ B,
      Runs body (coordinateCut S index remaining output d i word) time
        (Function.update (coordinateCut S index remaining output d i word) output
          ((word i).reverse++(coordinateState S index remaining output d i word) output))) :
    ∃ time ≤ d*(B+3)+1,
      Runs (coordinateLoop index remaining body)
        (coordinateState S index remaining output d 0 word) time
        (coordinateState S index remaining output d d word) := by
  classical
  have hex (i : Fin d) := hbody i.val i.isLt
  choose cost hcost hrun using hex
  let times (i : ℕ) := if hi : i < d then cost ⟨i,hi⟩+2 else 0
  have hrem (i : ℕ) : (coordinateState S index remaining output d i word) remaining =
      List.replicate (d-i) true := by simp [coordinateState,hro]
  have hidx (i : ℕ) : (coordinateCut S index remaining output d i word) index =
      List.replicate i true := by simp [coordinateCut,coordinateState,hir,hio]
  apply while_runs_bound remaining Option.isSome
    (.seq (discard remaining) (.seq body (.push index true))) d (B+2)
    (fun i => coordinateState S index remaining output d i word) times
  · intro i hi
    rw [hrem]
    have hd : d-i = (d-i-1)+1 := by omega
    rw [hd,List.replicate_succ]
    rfl
  · rw [hrem]
    simp
  · intro i hi
    let V := coordinateState S index remaining output d i word
    let W := coordinateCut S index remaining output d i word
    let U := Function.update W output ((word i).reverse++V output)
    have first : Runs (discard remaining) V 1 W := by
      have hd : d-i = (d-i-1)+1 := by omega
      have hr := discard_runs V remaining
      change Runs (discard remaining) V 1
        (Function.update V remaining ((coordinateState S index remaining output d i word) remaining).tail) at hr
      rw [hrem,hd,List.replicate_succ,List.tail_cons] at hr
      exact hr
    have second : Runs body W (cost ⟨i,hi⟩) U := hrun ⟨i,hi⟩
    have third : Runs (.push index true) U 1
        (coordinateState S index remaining output d (i+1) word) := by
      have hr := Runs.push U index true
      have he : Function.update U index (true::U index) =
          coordinateState S index remaining output d (i+1) word := by
        funext k
        by_cases hk : k = output
        · subst k
          simp [U,W,V,coordinateCut,coordinateState,Ne.symm hio,
            prefixWord_succ,List.reverse_append,List.append_assoc]
        · by_cases hk' : k = index
          · subst k
            simp [U,W,hidx,hir,hio,coordinateState,List.replicate_succ]
          · by_cases hk'' : k = remaining
            · subst k
              simp [U,W,coordinateCut,coordinateState,hro,Ne.symm hir,Nat.sub_sub]
            · simp [U,W,V,coordinateCut,coordinateState,
                Function.update_of_ne hk,Function.update_of_ne hk',Function.update_of_ne hk'']
      rw [he] at hr
      exact hr
    have hr := Runs.seq first (Runs.seq second third)
    simpa only [times,dif_pos hi,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hr
  · intro i hi
    simp only [times,dif_pos hi]
    exact Nat.add_le_add_right (hcost ⟨i,hi⟩) 2

/-- Registers: preserved dimension, current index, remaining coordinates,
reversed output, scratch. The body may use additional registers but its
specified effect is only on output. -/
def enumerateCoordinates (reg : Fin 5 ↪ K) (body : Program K) : Program K :=
  .seq (copy (reg 0) (reg 2) (reg 4))
    (.seq (coordinateLoop (reg 1) (reg 2) body) (clear (reg 1)))

theorem enumerateCoordinates_runs (S : Store K) (reg : Fin 5 ↪ K)
    (d B : ℕ) (word : ℕ → List Bool) (body : Program K)
    (hd : S (reg 0) = List.replicate d true)
    (hi : S (reg 1) = []) (hr : S (reg 2) = []) (ht : S (reg 4) = [])
    (hbody : ∀ i < d, ∃ time ≤ B,
      Runs body (coordinateCut S (reg 1) (reg 2) (reg 3) d i word) time
        (Function.update (coordinateCut S (reg 1) (reg 2) (reg 3) d i word) (reg 3)
          ((word i).reverse++(coordinateState S (reg 1) (reg 2) (reg 3) d i word) (reg 3)))) :
    ∃ time ≤ d*(B+12)+4,
      Runs (enumerateCoordinates reg body) S time
        (Function.update S (reg 3) ((prefixWord word d).reverse++S (reg 3))) := by
  have hne {i j : Fin 5} (h : i ≠ j) : reg i ≠ reg j := fun he => h (reg.injective he)
  have heq (i j : Fin 5) : reg i = reg j ↔ i = j := reg.injective.eq_iff
  let S₀ := coordinateState S (reg 1) (reg 2) (reg 3) d 0 word
  let S₁ := coordinateState S (reg 1) (reg 2) (reg 3) d d word
  have first : Runs (copy (reg 0) (reg 2) (reg 4)) S (7*d+2) S₀ := by
    have h := copy_runs S (reg 0) (reg 2) (reg 4)
      (hne (by decide)) (hne (by decide)) (hne (by decide)) ht
    have hstate : S₀ = Function.update S (reg 2) (List.replicate d true) := by
      dsimp [S₀,coordinateState]
      rw [← hi,Function.update_eq_self]
      apply Function.update_eq_self_iff.mpr
      simp [heq]
    rw [hstate]
    simpa [hd,hr] using h
  obtain ⟨time,htime,middle⟩ := coordinateLoop_runs S (reg 1) (reg 2) (reg 3)
    (hne (by decide)) (hne (by decide)) (hne (by decide)) d B word body hbody
  have last : Runs (clear (reg 1)) S₁ (2*d+1)
      (Function.update S (reg 3) ((prefixWord word d).reverse++S (reg 3))) := by
    have h := clear_runs S₁ (reg 1)
    have hs : S₁ (reg 1) = List.replicate d true := by simp [S₁,coordinateState,heq]
    have hstate : Function.update S₁ (reg 1) [] =
        Function.update S (reg 3) ((prefixWord word d).reverse++S (reg 3)) := by
      funext k
      by_cases hk : k = reg 1
      · subst k; simp [heq,hi]
      · by_cases hk' : k = reg 2
        · subst k; simp [S₁,coordinateState,heq,hr]
        · by_cases hk'' : k = reg 3
          · subst k; simp [S₁,coordinateState,heq]
          · simp [S₁,coordinateState,Function.update_of_ne hk,
              Function.update_of_ne hk',Function.update_of_ne hk'']
    rw [hstate,hs,List.length_replicate] at h
    exact h
  refine ⟨(7*d+2)+time+(2*d+1),?_,?_⟩
  · nlinarith
  · have h := Runs.seq first (Runs.seq middle last)
    convert h using 1
    omega

end GroupWL.MachinePrograms.Structured
