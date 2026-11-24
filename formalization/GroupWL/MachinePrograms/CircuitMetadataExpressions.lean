import GroupWL.CircuitMetadataValues
import GroupWL.MachinePrograms.ExpressionMap

/-! Concrete bounded-read expressions for every comparison metadata field. -/
namespace GroupWL.MachinePrograms.CircuitMetadataExpressions
open NatArrayLanguage NatArrayExpressions CircuitMetadataValues
set_option maxHeartbeats 4000000
inductive Reg where
  | length | index | todo | one | zero
  | types | coordinates | edges | seeds | tests | ports
  | lKinds | lSchemas | lSeeds | lTests | lOwners | lPorts
  deriving DecidableEq,Fintype
inductive Input where | kinds | schemas | seeds | tests | owners | ports
  deriving DecidableEq,Fintype
inductive Field where | dimension | source | target | sourceForm | targetForm | domain | permutation
  deriving DecidableEq,Fintype
abbrev Arr := Input ⊕ Unit
abbrev Term := Total Reg Input

def sizeRegister : Input → Reg
  | .kinds=>.lKinds | .schemas=>.lSchemas | .seeds=>.lSeeds | .tests=>.lTests | .owners=>.lOwners | .ports=>.lPorts

def readData (S : Store Reg Input) : Data where
  types:=S.scalar .types
  coordinates:=S.scalar .coordinates
  edges:=S.scalar .edges
  seeds:=S.scalar .seeds
  tests:=S.scalar .tests
  ports:=S.scalar .ports
  kinds:=S.array .kinds
  schemas:=S.array .schemas
  seedRequests:=S.array .seeds
  testRequests:=S.array .tests
  owners:=S.array .owners
  portNumbers:=S.array .ports

def num (n : ℕ) : Term := .const n
def reg (r : Reg) : Term := .scalar r
def add (a b : Term) : Term := .binary (.binary .add) a b
def sub (a b : Term) : Term := .binary (.binary .sub) a b
def mul (a b : Term) : Term := .binary (.binary .mul) a b
def quo (a b : Term) : Term := .binary .quotient a b
def rem (a b : Term) : Term := .binary .remainder a b
def eq (a b : Term) : Term := .binary (.binary .eq) a b
def lt (a b : Term) : Term := .binary (.binary .lt) a b
def branch (c a b : Term) : Term := .branch c a b
def rd (a : Input) (i : Term) : Term := .read a i

def schemaStride : Term := add (num 3) (mul (num 3) (reg .coordinates))
def requestStride : Term := add (num 1) (mul (num 2) (reg .coordinates))
def pairIf (c : Term) (a b : Term×Term) : Term×Term := (branch c a.1 b.1,branch c a.2 b.2)
def connectionCase (i : Term) : Term×Term :=
  pairIf (lt i (reg .edges)) (num 0,i) <|
  let i:=sub i (reg .edges)
  pairIf (lt i (reg .tests)) (num 1,i) <|
  let i:=sub i (reg .tests)
  pairIf (lt i (reg .coordinates)) (num 2,i) <|
  let i:=sub i (reg .coordinates)
  pairIf (lt i (reg .ports)) (num 3,i) <|
  let i:=sub i (reg .ports)
  pairIf (lt i (reg .ports)) (num 4,i) (num 5,sub i (reg .ports))

def sourceGate (kind i : Term) : Term := branch (eq kind (num 0))
  (rd .schemas (mul i schemaStride)) (rd .tests (mul i requestStride))
def gateOutput (gate k : Term) : Term := branch (eq k (num 0)) (num 1) (rd .kinds gate)
def connectionSource (i : Term) : Term :=
  let (kind,j):=connectionCase i
  branch (lt kind (num 2)) (sourceGate kind j)
    (branch (eq kind (num 4)) (rd .owners j) (reg .types))
def connectionTarget (i : Term) : Term :=
  let (kind,j):=connectionCase i
  branch (eq kind (num 0)) (rd .schemas (add (mul j schemaStride) (num 1)))
    (branch (add (eq kind (num 3)) (eq kind (num 4))) (rd .owners j) (reg .types))
def connectionSourceForm (i k : Term) : Term :=
  let (kind,j):=connectionCase i
  branch (lt kind (num 2)) (gateOutput (sourceGate kind j) k)
    (branch (eq kind (num 4)) (eq k (rd .ports j)) (eq k (num 0)))
def connectionTargetForm (i k : Term) : Term :=
  let (kind,j):=connectionCase i
  branch (eq kind (num 0))
    (eq k (mul (rd .kinds (rd .schemas (add (mul j schemaStride) (num 1))))
      (rd .schemas (add (mul j schemaStride) (num 2)))))
    (branch (add (eq kind (num 3)) (eq kind (num 4))) (eq k (rd .ports j)) (eq k (num 0)))
def connectionDomain (i coordinate bit : Term) : Term :=
  let (kind,j):=connectionCase i
  branch (eq kind (num 0)) (rd .schemas (add (add (add (mul j schemaStride) (num 3)) (mul (num 2) coordinate)) bit))
    (branch (eq kind (num 1)) (rd .tests (add (add (add (mul j requestStride) (num 1)) (mul (num 2) coordinate)) bit)) (num 1))
def connectionPermutation (i coordinate : Term) : Term :=
  let (kind,j):=connectionCase i
  branch (eq kind (num 0)) (rd .schemas (add (add (add (mul j schemaStride) (num 3)) (mul (num 2) (reg .coordinates))) coordinate))
    (branch (eq kind (num 2)) (eq coordinate j) (num 0))

def dimension (i : Term) : Term := branch (lt i (reg .types)) (add (num 1) (rd .kinds i))
  (branch (lt i (add (reg .types) (num 2))) (num 1) (num 2))
def source (i : Term) : Term := branch (lt i (reg .seeds)) (rd .seeds (mul i requestStride))
  (branch (eq (rem (sub i (reg .seeds)) (num 3)) (num 0))
    (add (add (reg .types) (num 2)) (quo (sub i (reg .seeds)) (num 3)))
    (connectionSource (quo (sub i (reg .seeds)) (num 3))))
def target (i : Term) : Term := branch (lt i (reg .seeds)) (add (reg .types) (num 1))
  (branch (eq (rem (sub i (reg .seeds)) (num 3)) (num 0))
    (connectionTarget (quo (sub i (reg .seeds)) (num 3)))
    (add (add (reg .types) (num 2)) (quo (sub i (reg .seeds)) (num 3))))
def sourceForm (i k : Term) : Term := branch (lt i (reg .seeds))
  (gateOutput (rd .seeds (mul i requestStride)) k)
  (branch (eq (rem (sub i (reg .seeds)) (num 3)) (num 0)) (num 1)
    (connectionSourceForm (quo (sub i (reg .seeds)) (num 3)) k))
def targetForm (i k : Term) : Term := branch (lt i (reg .seeds)) (num 0)
  (branch (eq (rem (sub i (reg .seeds)) (num 3)) (num 0))
    (connectionTargetForm (quo (sub i (reg .seeds)) (num 3)) k)
    (eq k (sub (rem (sub i (reg .seeds)) (num 3)) (num 1))))
def domain (i coordinate bit : Term) : Term := branch (lt i (reg .seeds))
  (rd .seeds (add (add (add (mul i requestStride) (num 1)) (mul (num 2) coordinate)) bit))
  (connectionDomain (quo (sub i (reg .seeds)) (num 3)) coordinate bit)
def permutation (i coordinate : Term) : Term := branch (lt i (reg .seeds)) (num 0)
  (branch (eq (rem (sub i (reg .seeds)) (num 3)) (num 0))
    (connectionPermutation (quo (sub i (reg .seeds)) (num 3)) coordinate) (num 0))

def entry (f : Field) : Term :=
  let i:=reg .index
  match f with
  | .dimension=>dimension i | .source=>source i | .target=>target i
  | .sourceForm=>sourceForm (quo i (num 2)) (rem i (num 2))
  | .targetForm=>targetForm (quo i (num 2)) (rem i (num 2))
  | .domain=>domain (quo i (mul (reg .coordinates) (num 2)))
      (rem (quo i (num 2)) (reg .coordinates)) (rem i (num 2))
  | .permutation=>permutation (quo i (reg .coordinates)) (rem i (reg .coordinates))

def value (D : Data) (f : Field) (i : ℕ) : ℕ := match f with
  | .dimension=>D.dimension i | .source=>D.source i | .target=>D.target i
  | .sourceForm=>D.sourceForm (i/2) (i%2) | .targetForm=>D.targetForm (i/2) (i%2)
  | .domain=>D.domain (i/(D.coordinates*2)) ((i/2)%D.coordinates) (i%2)
  | .permutation=>D.permutation (i/D.coordinates) (i%D.coordinates)

end GroupWL.MachinePrograms.CircuitMetadataExpressions
