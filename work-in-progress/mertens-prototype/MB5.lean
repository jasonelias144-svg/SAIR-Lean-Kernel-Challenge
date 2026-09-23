import MB4
namespace MB5
open MB
/-- square `X` until it exceeds `all` (at most `fuel` times) -/
def sqUp (all : Nat) (fuel X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun X => X)
    (fun _ ih X => cond (Nat.ble X all) (ih (Nat.mul X X)) X) fuel X
def geo2 (n all S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ P => P)
    (fun _ ih S P => cond (Nat.beq S 0) P
      ((fun S' => (fun L => ih S' (Nat.xor P (Nat.land (Nat.mul L (Nat.div (Nat.sub (sqUp all 10 L) 1)
          (Nat.sub L 1))) all))) (Nat.xor S S')) (Nat.land S (Nat.sub S 1))))
    (Nat.add n 1) S 0
def tG2 (n : Nat) : Nat := forceN (allOf n) fun all => forceN (sieve n all (bound n)) fun S => geo2 n all S % 1000003
def implB (n : Nat) : Int :=
  forceI (allOf n) fun all =>
  forceI (sqfree n all (bound n)) fun Q =>
  forceI (sieve n all (bound n)) fun S =>
  forceI (geo2 n all S) fun P =>
  Int.sub (Int.ofNat (pop (Nat.add n 1) (Nat.land Q (Nat.xor all P)))) (Int.ofNat (pop (Nat.add n 1) (Nat.land Q P)))
end MB5
