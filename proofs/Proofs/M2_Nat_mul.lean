import Proofs.M1_Nat_plus
import Mathlib.Logic.Basic
open Nat
theorem distributive (butter kommy tig : Nat)
    :butter*(kommy+tig)=butter*kommy+butter*tig:=by
induction tig
case zero =>
  rw [Nat.add_zero]
  rw [Nat.mul_zero]
  rw [Nat.add_zero]
case succ c h=>
rw [← Nat.add_assoc]
repeat rw [Nat.mul_succ]
rw [← Nat.add_assoc]
rw [h]

theorem associative (butter kommy tig : Nat)
    :butter*kommy*tig=butter*(kommy*tig):=by
induction tig
case zero =>
  repeat rw [Nat.mul_zero]
case succ c h=>
  repeat rw [Nat.mul_succ]
  rw [distributive]
  rw [h]
theorem zero_mul_butter_eq_zero (butter : Nat)
    :0*butter=0:=by
induction butter
case zero =>
  rw [Nat.mul_zero]
case succ butter hypothesis =>
  rw [distributive]
  rw [Nat.mul_one]
  rw [hypothesis, Nat.add_zero]
theorem one_mul_butter_eq_butter (butter : Nat)
    :1*butter=butter:=by
induction butter
case zero =>
  rw [Nat.mul_zero]
case succ butter hypothesis =>
  rw [distributive]
  rw [Nat.mul_one]
  rw [hypothesis]
theorem right_distributive (butter kommy tig : Nat)
    :(butter+kommy)*tig=butter*tig+kommy*tig:=by
induction tig
case zero =>
  repeat rw [Nat.mul_zero]
case succ tig hypothesis =>
  repeat rw [Nat.mul_succ]
  repeat rw [← Nat.add_assoc]
  rw [hypothesis]
  rw [Nat.add_assoc (butter*tig) butter (kommy*tig)]
  rw [Nat.add_comm butter (kommy*tig)]
  rw [← Nat.add_assoc]
theorem commutative (butter kommy : Nat)
    :butter*kommy=kommy*butter:=by
induction kommy
case zero =>
  rw [Nat.mul_zero]
  rw [zero_mul_butter_eq_zero]
case succ kommy hypothesis =>
  rw [right_distributive]
  rw [mul_succ]
  rw [one_mul_butter_eq_butter]
  rw [hypothesis]
theorem cancellation (butter kommy tig : Nat)
    :(¬(tig=0)→((butter*tig=kommy*tig)→butter=kommy)):=by
induction tig
case zero =>
  have zero_is_zero:0=0 := rfl
  intro h
  apply absurd zero_is_zero h
case succ tig hypothesis =>
  rw [← Nat.succ_eq_add_one]
  rw [← Ne.eq_1]
  intro h
  rw [Nat.mul_succ]
  sorry -- 이거 대소 관계 들어가서 그 담에 해야할듯
