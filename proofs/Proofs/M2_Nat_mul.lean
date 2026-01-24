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
--                                                                                                 버터+코미=0이라면 버터=코미=0이다.
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
theorem butter_mul_kommy_eq_zero_imp_butter_or_kommy_eq_zero (butter kommy : Nat)
    :butter*kommy=0→(butter=0∨kommy=0):=by
intro h
induction butter
case zero=>
  apply Or.inl
  rfl
case succ butter hypothesis=>
  apply Or.inr
  rw [succ_mul] at h
  replace h2:=(Plus.butter_plus_kommy_eq_zero_imp_butter_eq_kommy_eq_zero (butter*kommy) kommy)
  replace h:kommy=0:=And.right (h2 h)
  exact h

theorem cancellation (butter kommy tig : Nat)
    :(¬(tig=0)→((butter*tig=kommy*tig)→butter=kommy)):=by
intro h h2
induction butter generalizing kommy
case zero=>
  rw [Nat.zero_mul] at h2
  rw [Eq.comm] at h2
  match (butter_mul_kommy_eq_zero_imp_butter_or_kommy_eq_zero kommy tig h2) with
  | Or.inl h3=>
   rw [Eq.comm]
   trivial
  | Or.inr _=>
   contradiction
case succ butter hypothesis=>
  rw [Nat.succ_mul] at h2
  induction kommy
  case zero=>
    rw [Nat.zero_mul] at h2
    have tig_eq_zero:tig=0:=And.right (
      (Plus.butter_plus_kommy_eq_zero_imp_butter_eq_kommy_eq_zero (butter*tig) tig) h2
      )
    contradiction
  case succ kommy hi=>
    rw [succ_mul] at h2
    rw [Plus.cancellation] at h2
    have butter_eq_kommy:butter=kommy:=((hypothesis kommy) h2)
    rw [Nat.succ_inj]
    exact butter_eq_kommy
