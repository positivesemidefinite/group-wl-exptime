import GroupWL.MachinePrograms.TensorParsingBudgets
import GroupWL.MachinePrograms.EquivalenceParsing

/-! Uniform single-exponential bounds for cached WL tables and compact p-group candidates. -/
namespace GroupWL.MachinePrograms.WLExponentialBudgets

def coefficient (p : ℕ) : ℕ := (p+11)*11^4
def exponent (p N : ℕ) : ℕ := coefficient p*(N+1)^4
def budget (p N : ℕ) : ℕ := 2^(exponent p N)

theorem local_exponent_le (p N : ℕ) : (p+11)*(N+11)^4≤exponent p N := by
  have h : N+11≤11*(N+1) := by omega
  calc
    _ ≤ (p+11)*(11*(N+1))^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h _)
    _ = _ := by unfold exponent coefficient; ring

theorem basic_exponents (p N k : ℕ) (hk : k≤N+10) :
    let a := (p+11)*(N+11)
    4*a≤exponent p N ∧ 3*a≤exponent p N ∧ 2*(a*k+1)≤exponent p N ∧
    (a*k+1)+2*a≤exponent p N ∧ (a*k+1)*k≤exponent p N ∧ a≤exponent p N := by
  have h := local_exponent_le p N
  let x := N+11
  have hx : 11≤x := by dsimp [x]; omega
  have hk' : k≤x := by dsimp [x]; omega
  have hx2 : x≤x^2 := by nlinarith
  have hx3 : x^2≤x^3 := by nlinarith
  have hx4 : x^3≤x^4 := by nlinarith
  change (p+11)*x^4≤exponent p N at h
  have hak : ((p+11)*x)*k≤(p+11)*x^2 := by
    simpa only [pow_two,Nat.mul_assoc] using Nat.mul_le_mul_left ((p+11)*x) hk'
  have hakk : (((p+11)*x)*k+1)*k≤((p+11)*x^2+1)*x :=
    Nat.mul_le_mul (by omega) hk'
  dsimp only
  change 4*((p+11)*x)≤_ ∧ 3*((p+11)*x)≤_ ∧ 2*((p+11)*x*k+1)≤_ ∧
    ((p+11)*x*k+1)+2*((p+11)*x)≤_ ∧ ((p+11)*x*k+1)*k≤_ ∧ (p+11)*x≤_
  have gap : (p+11)*x^3+x≤(p+11)*x^4 := by nlinarith [sq_nonneg (x*x)]
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> nlinarith [sq_nonneg (x*x)]

theorem pow_bound {n e k : ℕ} (h : n≤2^e) : n^k≤2^(e*k) := by
  simpa only [pow_mul] using Nat.pow_le_pow_left h k

theorem leaves (p N n m k : ℕ) (hn : n≤p^N) (hm : m≤p^N) (hk : k≤N+10) :
    let a := (p+11)*(N+11)
    n≤2^a ∧ m≤2^a ∧ k≤2^a := by
  have hp : p^N≤2^((p+11)*(N+11)) :=
    (TensorParsingBudgets.field_power_le_base p N).trans
      (pow_le_pow_right' (by decide) (by nlinarith))
  refine ⟨hn.trans hp,hm.trans hp,?_⟩
  exact (show k≤(p+11)*(N+11) by nlinarith).trans (Nat.le_of_lt Nat.lt_two_pow_self)

theorem room (p N n m k : ℕ) (hn : n≤p^N) (hm : m≤p^N) (hk : k≤N+10) :
    n*n≤budget p N ∧ m*m≤budget p N ∧ k^3≤budget p N ∧ 1≤budget p N ∧
    (n^k+m^k)^2≤budget p N ∧ (max n m)^4≤budget p N ∧
    ((n^k+m^k)*max n m)*k≤budget p N ∧ (n^k+m^k)*max n m≤budget p N ∧
    k≤budget p N ∧ max n m≤budget p N ∧ (n^k+m^k)^k≤budget p N := by
  let a := (p+11)*(N+11)
  obtain ⟨hn',hm',hk'⟩ := leaves p N n m k hn hm hk
  change n≤2^a at hn'; change m≤2^a at hm'; change k≤2^a at hk'
  have hw : max n m≤2^a := max_le hn' hm'
  have ht : n^k+m^k≤2^(a*k+1) := by
    calc
      _ ≤ 2^(a*k)+2^(a*k) := Nat.add_le_add (pow_bound hn') (pow_bound hm')
      _ = _ := by rw [pow_succ]; omega
  obtain ⟨he4,he3,het,heprod,hepow,he1⟩ := basic_exponents p N k hk
  change 4*a≤exponent p N at he4
  change 3*a≤exponent p N at he3
  change 2*(a*k+1)≤exponent p N at het
  change (a*k+1)+2*a≤exponent p N at heprod
  change (a*k+1)*k≤exponent p N at hepow
  change a≤exponent p N at he1
  have mono {e : ℕ} (he : e≤exponent p N) : 2^e≤budget p N := pow_le_pow_right' (by decide) he
  have hn2 : n*n≤budget p N := by simpa [pow_two] using (pow_bound (k:=2) hn').trans (mono (by omega))
  have hm2 : m*m≤budget p N := by simpa [pow_two] using (pow_bound (k:=2) hm').trans (mono (by omega))
  have hk3 : k^3≤budget p N := (pow_bound hk').trans (mono (by omega))
  have ht2 : (n^k+m^k)^2≤budget p N := (pow_bound ht).trans (mono (by omega))
  have hw4 : (max n m)^4≤budget p N := (pow_bound hw).trans (mono (by omega))
  have hprod : ((n^k+m^k)*max n m)*k≤2^((a*k+1)+2*a) := by
    calc
      _ ≤ (2^(a*k+1)*2^a)*2^a := Nat.mul_le_mul (Nat.mul_le_mul ht hw) hk'
      _ = _ := by rw [←pow_add,←pow_add]; congr 1; omega
  have hprod' : (n^k+m^k)*max n m≤2^((a*k+1)+2*a) := by
    calc
      _ ≤ 2^(a*k+1)*2^a := Nat.mul_le_mul ht hw
      _ = 2^((a*k+1)+a) := (pow_add ..).symm
      _ ≤ _ := pow_le_pow_right' (by decide) (by omega)
  exact ⟨hn2,hm2,hk3,one_le_pow₀ (by decide),ht2,hw4,hprod.trans (mono heprod),
    hprod'.trans (mono heprod),hk'.trans (mono he1),hw.trans (mono he1),
    (pow_bound ht).trans (mono hepow)⟩

theorem parser_room (p N : ℕ) : TensorParsingBudgets.magnitude p N≤budget p N ∧ N+10≤budget p N := by
  have h := (basic_exponents p N 0 (by omega)).1
  constructor
  · unfold TensorParsingBudgets.magnitude TensorParsingBudgets.base budget
    rw [←pow_mul]
    exact pow_le_pow_right' (by decide) (by nlinarith)
  · have hl : N+10≤2^((p+11)*(N+11)) :=
      (show N+10≤(p+11)*(N+11) by nlinarith).trans (Nat.le_of_lt Nat.lt_two_pow_self)
    exact hl.trans (pow_le_pow_right' (by decide) (by nlinarith))

theorem polynomial_bound (p N K d : ℕ) :
    K*(budget p N+1)^d≤2^((K+d*(coefficient p+1))*(N+1)^4) := by
  have hB : 1≤budget p N := one_le_pow₀ (by decide)
  have hplus : budget p N+1≤2^(exponent p N+1) := by
    rw [pow_succ]
    change budget p N+1≤budget p N*2
    omega
  have hK : K≤2^K := Nat.le_of_lt Nat.lt_two_pow_self
  have hpow := pow_bound (k:=d) hplus
  calc
    _ ≤ 2^K*2^((exponent p N+1)*d) := Nat.mul_le_mul hK hpow
    _ = 2^(K+(exponent p N+1)*d) := (pow_add ..).symm
    _ ≤ _ := by
      apply pow_le_pow_right' (by decide)
      have hN : 1≤(N+1)^4 := one_le_pow₀ (by omega)
      unfold exponent
      nlinarith

theorem candidate_room (p N D k : ℕ) (hp : 1≤p) (hD : D≤N) (hk : k≤N+10) :
    p^(D^3)≤budget p N ∧ D^3≤budget p N ∧ (p^D)^D≤budget p N ∧
    (p^D)^4≤budget p N ∧ (2*(p^D)^k)^k≤budget p N := by
  have hn : p^D≤p^N := pow_le_pow_right' hp hD
  have hD' : D≤N+10 := by omega
  have hdroom := room p N (p^D) (p^D) D hn hn hD'
  have hkroom := room p N (p^D) (p^D) k hn hn hk
  have hcount : p^(D^3)≤budget p N := by
    have hd : D≤N+11 := by omega
    have hx : (N+11)^3≤(N+11)^4 := pow_le_pow_right' (by omega) (by decide)
    calc
      _ ≤ 2^(p*(D^3)) := pow_bound (Nat.le_of_lt Nat.lt_two_pow_self)
      _ ≤ 2^((p+11)*(N+11)^4) := pow_le_pow_right' (by decide)
        (Nat.mul_le_mul (by omega) ((Nat.pow_le_pow_left hd 3).trans hx))
      _ ≤ _ := pow_le_pow_right' (by decide) (local_exponent_le p N)
  have hpow : (p^D)^D≤budget p N := by
    have hb := (leaves p N (p^D) (p^D) D hn hn hD').1
    have he := (basic_exponents p N D hD').2.2.1
    exact (pow_bound hb).trans (pow_le_pow_right' (by decide) (by omega))
  refine ⟨hcount,hdroom.2.2.1,hpow,?_,?_⟩
  · simpa only [max_self] using hkroom.2.2.2.2.2.1
  · simpa only [two_mul] using hkroom.2.2.2.2.2.2.2.2.2.2

end GroupWL.MachinePrograms.WLExponentialBudgets
