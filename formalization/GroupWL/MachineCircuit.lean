import GroupWL.TableauCircuit
import GroupWL.BinaryIntervals

/-! A compact addressed monotone circuit for an actual finite-time machine run. -/
namespace GroupWL.MachineCircuit

open Complexity MachineCellular AddressedCircuit BinaryAddress TableauCircuit

abbrev SeedIndex (w : BitString) (d : ℕ) := Fin (w.length+1) ⊕ Option (Fin d)

def blank (M : Machine) : Cell M := (.inl none,none)

def seedRequest (M : Machine) (w : BitString) (d : ℕ) :
    SeedIndex w d → ScalarRequest (Cell M) (d+d)
  | .inl i =>
    ⟨cyclicInitial M w (2^d) (i.val : ZMod (2^d)),
      ProductAddress.domain (ProductDomain.singleton (fun _ => false))
        (ProductDomain.singleton (ofNat d i.val))⟩
  | .inr h =>
    ⟨blank M, ProductAddress.domain (ProductDomain.singleton (fun _ => false))
      (BinaryIntervals.indexedDomain (ofNat d (w.length+1)) h)⟩

def seeds (M : Machine) (w : BitString) (d : ℕ) :
    Fin (FiniteCode.size (SeedIndex w d)) → ScalarRequest (Cell M) (d+d) :=
  fun i => seedRequest M w d ((FiniteCode.equiv (α := SeedIndex w d)).symm i)

def tests (M : Machine) (d : ℕ) :
    Fin (FiniteCode.size (Symbol M.workSymbols)) → ScalarRequest (Cell M) (d+d) :=
  fun i => ⟨((FiniteCode.equiv (α := Symbol M.workSymbols)).symm i,some (.inl true)),
    ProductAddress.domain (ProductDomain.singleton (fun _ => true)) (ProductDomain.full d)⟩

def compile (M : Machine) (w : BitString) (d : ℕ) :
    Circuit (CellularTableau.Gate (Cell M)) (d+d) :=
  circuit (rule M) (seeds M w d) (tests M d)

@[simp] theorem space_val {d : ℕ} (a : Address (d+d)) :
    (TableauWiring.space a).val = value (ProductAddress.right a) := by
  simp only [TableauWiring.space,ZMod.val_natCast,Nat.mod_eq_of_lt (value_lt _)]

theorem time_zero_iff {d : ℕ} (a : Address (d+d)) :
    (ProductDomain.singleton (fun _ : Fin d => false)).Contains (ProductAddress.left a) ↔
      TableauWiring.time a = 0 := by
  rw [ProductDomain.contains_singleton]
  constructor
  · intro h; simp [TableauWiring.time,h]
  · intro h
    apply value_injective d
    simpa only [value_all_false] using h

theorem time_last_iff {d : ℕ} (a : Address (d+d)) :
    (ProductDomain.singleton (fun _ : Fin d => true)).Contains (ProductAddress.left a) ↔
      TableauWiring.time a = 2^d-1 := by
  rw [ProductDomain.contains_singleton]
  constructor
  · intro h; simp [TableauWiring.time,h]
  · intro h
    apply value_injective d
    simpa only [value_all_true] using h

theorem cyclicInitial_blank (M : Machine) (w : BitString) (d : ℕ) (x : ZMod (2^d))
    (h : w.length+1 ≤ x.val) : cyclicInitial M w (2^d) x = blank M := by
  have hw : w.length ≤ x.val := by omega
  have hx : (x.val : ℤ) ≠ 0 := by omega
  dsimp only [cyclicInitial,encode,initial,blank]
  simp only [Int.natCast_nonneg,ite_true,Int.toNat_natCast,
    List.getElem?_eq_none hw,hx,ite_false]

theorem seedRequest_exact (M : Machine) (w : BitString) (d : ℕ)
    (hw : w.length+1 < 2^d) (letter : Cell M) (a : Address (d+d)) :
    (∃ i : SeedIndex w d, letter = (seedRequest M w d i).letter ∧
      (seedRequest M w d i).domain.Contains a) ↔
    TableauWiring.time a = 0 ∧ letter = cyclicInitial M w (2^d) (TableauWiring.space a) := by
  constructor
  · rintro ⟨i,hi,ha⟩
    cases i with
    | inl i =>
      obtain ⟨ht,hx⟩ := (ProductAddress.contains_domain _ _ a).mp ha
      have ht' := (time_zero_iff a).mp ht
      have hx' := (ProductDomain.contains_singleton _ _).mp hx
      have he : TableauWiring.space a = (i.val : ZMod (2^d)) := by
        simp only [TableauWiring.space,hx',value_ofNat d i.val (by omega)]
      exact ⟨ht',by simpa only [seedRequest,he] using hi⟩
    | inr i =>
      obtain ⟨ht,hx⟩ := (ProductAddress.contains_domain _ _ a).mp ha
      have ht' := (time_zero_iff a).mp ht
      have hbound := (BinaryIntervals.indexed_covered_iff (ofNat d (w.length+1))
        (ProductAddress.right a)).mp ⟨i,hx⟩
      rw [value_ofNat d _ hw,← space_val] at hbound
      exact ⟨ht',hi.trans (cyclicInitial_blank M w d _ hbound).symm⟩
  · rintro ⟨ht,hl⟩
    by_cases hx : (TableauWiring.space a).val < w.length+1
    · let i : Fin (w.length+1) := ⟨(TableauWiring.space a).val,hx⟩
      refine ⟨.inl i,?_,?_⟩
      · simpa only [seedRequest,i,ZMod.natCast_zmod_val] using hl
      · apply (ProductAddress.contains_domain _ _ a).mpr
        refine ⟨(time_zero_iff a).mpr ht,?_⟩
        rw [ProductDomain.contains_singleton]
        apply value_injective d
        rw [value_ofNat d i.val (by dsimp [i]; omega)]
        exact (space_val a).symm
    · have hle : w.length+1 ≤ (TableauWiring.space a).val := by omega
      have hbound : value (ofNat d (w.length+1)) ≤ value (ProductAddress.right a) := by
        simpa only [value_ofNat d _ hw,space_val] using hle
      obtain ⟨i,hi⟩ := (BinaryIntervals.indexed_covered_iff _ _).mpr hbound
      refine ⟨.inr i,hl.trans (cyclicInitial_blank M w d _ hle),?_⟩
      exact (ProductAddress.contains_domain _ _ a).mpr ⟨(time_zero_iff a).mpr ht,hi⟩

theorem seeds_exact (M : Machine) (w : BitString) (d : ℕ) (hw : w.length+1 < 2^d) :
    SeedsExact (seeds M w d) (cyclicInitial M w (2^d)) := by
  intro letter a
  rw [← seedRequest_exact M w d hw letter a]
  constructor
  · rintro ⟨i,hi,ha⟩
    exact ⟨(FiniteCode.equiv (α := SeedIndex w d)).symm i,hi,ha⟩
  · rintro ⟨i,hi,ha⟩
    refine ⟨FiniteCode.equiv (α := SeedIndex w d) i,?_,?_⟩
    · simpa only [seeds,Equiv.symm_apply_apply] using hi
    · simpa only [seeds,Equiv.symm_apply_apply] using ha

theorem test_iff (M : Machine) (w : BitString) (d : ℕ)
    (g : CellularTableau.Gate (Cell M)) (a : Address (d+d)) :
    (compile M w d).Test (g,a) ↔
      ∃ symbol : Symbol M.workSymbols,
        g = .scalar (symbol,some (.inl true)) ∧ TableauWiring.time a = 2^d-1 := by
  constructor
  · rintro ⟨i,hi,ha⟩
    exact ⟨(FiniteCode.equiv (α := Symbol M.workSymbols)).symm i,hi,
      (time_last_iff a).mp ((ProductAddress.contains_domain _ _ a).mp ha).1⟩
  · rintro ⟨symbol,hg,ht⟩
    refine ⟨FiniteCode.equiv (α := Symbol M.workSymbols) symbol,?_,?_⟩
    · simpa only [compile,circuit,tests,Equiv.symm_apply_apply] using hg
    · apply (ProductAddress.contains_domain _ _ a).mpr
      exact ⟨(time_last_iff a).mpr ht,ProductDomain.contains_full _⟩

theorem accepts_iff_cyclic (M : Machine) (w : BitString) (d : ℕ)
    (hw : w.length+1 < 2^d) :
    (compile M w d).Accepts ↔
      ∃ x : ZMod (2^d),
        (MachineCellular.cyclicRun M (2^d) (cyclicInitial M w (2^d)) (2^d-1) x).2 =
          some (.inl true) := by
  have hs := seeds_exact M w d hw
  have hn : 2^d-1 < 2^d := Nat.sub_lt (pow_pos (by omega) d) (by omega)
  constructor
  · rintro ⟨⟨g,a⟩,ht,htrue⟩
    obtain ⟨symbol,hg,ha⟩ := (test_iff M w d g a).mp ht
    subst g
    have hc := (TableauCircuit.scalar_iff (rule M) (seeds M w d) (tests M d)
      (cyclicInitial M w (2^d)) hs _ a).mp htrue
    rw [ha,CellularTableau.machine_run_eq] at hc
    exact ⟨TableauWiring.space a,congrArg Prod.snd hc.symm⟩
  · rintro ⟨x,hx⟩
    let c := MachineCellular.cyclicRun M (2^d) (cyclicInitial M w (2^d)) (2^d-1) x
    let a := address d (2^d-1) x
    refine ⟨(.scalar c,a),?_,?_⟩
    · apply (test_iff M w d _ _).mpr
      refine ⟨c.1,?_,time_address d _ x hn⟩
      exact congrArg CellularTableau.Gate.scalar (Prod.ext rfl hx)
    · apply (TableauCircuit.scalar_iff (rule M) (seeds M w d) (tests M d)
        (cyclicInitial M w (2^d)) hs _ a).mpr
      rw [time_address d _ x hn,space_address,CellularTableau.machine_run_eq]

/-- The compact circuit's acceptance is the actual machine's halting answer.
There is no assumed compiler correctness premise. -/
theorem accepts_iff_halt (M : Machine) (w : BitString) (d T time : ℕ)
    (hT : 0 < T) (hspace : 4*T ≤ 2^d) (hw : w.length ≤ T)
    (htime : time ≤ T) (b : Bool) (hb : (execute M w time).control = .inl b) :
    (compile M w d).Accepts ↔ b = true := by
  rw [accepts_iff_cyclic M w d (by omega)]
  exact cyclic_terminal_acceptance M w (2^d) T time (2^d-1) hT hspace hw
    htime (by omega) b hb

theorem acyclic (M : Machine) (w : BitString) (d : ℕ) : (compile M w d).Acyclic :=
  TableauCircuit.acyclic (rule M) (seeds M w d) (tests M d)

theorem seed_count (M : Machine) (w : BitString) (d : ℕ) :
    (compile M w d).seedCount = w.length+d+2 := by
  change (w.length+1)+(d+1) = _
  omega

theorem test_count (M : Machine) (w : BitString) (d : ℕ) :
    (compile M w d).testCount = 3+M.workSymbols := rfl

theorem edge_count (M : Machine) (w : BitString) (d : ℕ) :
    (compile M w d).edges = ((3+M.workSymbols)*(3+M.states))^3 * (2*d^2+3*d+2) := by
  rw [compile,TableauCircuit.edges_eq]
  congr 2
  change ((2+1)+M.workSymbols)*((2+M.states)+1) = _
  ring

/-- The exponent of the time bound is enlarged by the input length. Two
further bits give enough cyclic tape room for the proved light-cone bound. -/
def addressBits (c e n : ℕ) : ℕ := (c*(n+1)^e+(n+1))+2

theorem addressBits_pos (c e n : ℕ) : 0 < addressBits c e n := by
  simp only [addressBits]
  omega

theorem addressBits_polynomial (c e n : ℕ) :
    addressBits c e n ≤ (c+3)*(n+1)^(e+1) := by
  have hp : 1 ≤ (n+1)^e := Nat.succ_le_of_lt (pow_pos (Nat.succ_pos n) e)
  have hpow : (n+1)^e ≤ (n+1)^e*(n+1) := by nlinarith
  have hn : n+3 ≤ 3*((n+1)^e*(n+1)) := by nlinarith
  have hm := Nat.mul_le_mul_left c hpow
  simp only [addressBits,pow_succ]
  nlinarith

/-- For every actual exponentially bounded decider, this explicit compact
circuit accepts precisely its language. -/
theorem compile_decider (M : Machine) (L : Language) (c e : ℕ)
    (hM : DecidesBy M L (fun n => 2^(c*(n+1)^e))) (w : BitString) :
    (compile M w (addressBits c e w.length)).Accepts ↔ w ∈ L := by
  obtain ⟨time,htime,b,hb,hL⟩ := hM w
  let exponent := c*(w.length+1)^e+(w.length+1)
  let T := 2^exponent
  have hT : 0 < T := pow_pos (by omega) _
  have hspace : 4*T ≤ 2^(addressBits c e w.length) := by
    simp only [T,exponent,addressBits,pow_add]
    omega
  have hinput : w.length ≤ T := by
    exact (show w.length < 2^w.length from Nat.lt_two_pow_self).le.trans
      (Nat.pow_le_pow_right (by omega) (by dsimp [exponent]; omega))
  have hrun : time ≤ T := htime.trans
    (Nat.pow_le_pow_right (by omega) (by dsimp [exponent]; omega))
  exact (accepts_iff_halt M w _ T time hT hspace hinput hrun b hb).trans hL

end GroupWL.MachineCircuit
