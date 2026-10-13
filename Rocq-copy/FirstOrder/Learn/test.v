
Definition add_one : nat -> nat. 
Proof.
    refine (fun n => _).
    exact (S (S n)).
Qed.

Print add_one.