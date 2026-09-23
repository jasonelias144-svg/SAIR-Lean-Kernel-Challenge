import Spec
namespace MB
def forceN (x : Nat) (k : Nat → Nat) : Nat :=
  Nat.casesOn (motive := fun _ => Nat) x (k 0) (fun m => k (Nat.succ m))
def forceI (x : Nat) (k : Nat → Int) : Int :=
  Nat.casesOn (motive := fun _ => Int) x (k 0) (fun m => k (Nat.succ m))
/-- bits `s, 2s, 3s, …, K s` with `K = n / s + 1` (pattern `(2^{sK}-1)/(2^s-1) <<< s`) -/
def multsFrom1 (n s : Nat) : Nat :=
  Nat.shiftLeft (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul s (Nat.add (Nat.div n s) 1))) 1)
      (Nat.sub (Nat.shiftLeft 1 s) 1)) s
def mults2 (n d : Nat) : Nat := Nat.shiftLeft (Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul d (Nat.add (Nat.div n d) 1))) 1)
      (Nat.sub (Nat.shiftLeft 1 d) 1)) (Nat.mul 2 d)
def allOf (n : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 (Nat.add n 1)) 1
def bound (n : Nat) : Nat := Nat.shiftLeft 1 (Nat.add (Nat.div (Nat.log2 n) 2) 1)
/-- primes ≤ n -/
def sieve (n all D : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.land all (Nat.xor all 3))
    (fun j S => forceN S fun S => Nat.land S (Nat.xor all (Nat.land (mults2 n (Nat.add j 2)) all))) D
/-- squarefree numbers in 1..n -/
def sqfree (n all D : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (Nat.land all (Nat.xor all 1))
    (fun j Q => forceN Q fun Q => Nat.land Q (Nat.xor all (Nat.land (multsFrom1 n (Nat.mul (Nat.add j 2) (Nat.add j 2))) all))) D
/-- parity of number of prime factors: for each set bit `L = 2^p` of `S` (lowest first),
XOR in the multiples of `p`, `L * (L^(n+1) - 1) / (L - 1)` masked to `n` bits. -/
def parity (n all S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ P => P)
    (fun _ ih S P => cond (Nat.beq S 0) P
      (forceN (Nat.land S (Nat.sub S 1)) fun S' =>
        forceN (Nat.xor S S') fun L =>
        forceN (Nat.xor P (Nat.land (Nat.mul L (Nat.div (Nat.sub (Nat.pow L (Nat.add n 1)) 1)
          (Nat.sub L 1))) all)) fun P' => ih S' P'))
    (Nat.add n 1) S 0
def pop (fuel x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun _ ih x => cond (Nat.beq x 0) 0 (Nat.add (ih (Nat.land x (Nat.sub x 1))) 1)) fuel x
def impl (n : Nat) : Int :=
  forceI (allOf n) fun all =>
  forceI (sqfree n all (bound n)) fun Q =>
  forceI (sieve n all (bound n)) fun S =>
  forceI (parity n all S) fun P =>
  Int.sub (Int.ofNat (pop (Nat.add n 1) (Nat.land Q (Nat.xor all P)))) (Int.ofNat (pop (Nat.add n 1) (Nat.land Q P)))
end MB
