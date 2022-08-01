import Mathbin

import ZkSNARK.GeneralLemmas.MvDivisibility
import ZkSNARK.Groth16.Vars

noncomputable section

namespace Groth16
open Finset Polynomial

variable {F : Type u} [Field F]

/- n_stmt - the statement size, 
n_wit - the witness size -/ 
variable {n_stmt n_wit n_var : ℕ}

/- u_stmt and u_wit are fin-indexed collections of polynomials from the square span program -/
variable (u_stmt : Finₓ n_stmt → F[X] )
variable (u_wit : Finₓ n_wit → F[X] )
variable (v_stmt : Finₓ n_stmt → F[X] )
variable (v_wit : Finₓ n_wit → F[X] )
variable (w_stmt : Finₓ n_stmt → F[X] )
variable (w_wit : Finₓ n_wit → F[X] )

def l := n_stmt
def m := n_wit

/- The roots of the polynomial t -/
variable (r : Finₓ m → F)
/-- t is the polynomial divisibility by which is used to verify satisfaction of the SSP -/
def t : Polynomial F := 
  ∏ i in finRange m, (x : F[X]) - c (r i)

end Groth16