(* Adapted from Barendregt: https://gist.github.com/palmskog/341da4e54ff7e805077b6e0b3af7d21d *)
Section Barendregt.

Variable P : Prop.

Fixpoint B (n : nat) := match n with | 1 => P | S n' => P <-> B n' | 0 => True end.

Lemma B2n: forall n, B (2 * n).
Proof.
refine (fix B2n n : B (2 * n) := match n with | 0 => I | S n' => _ end).
refine (let IH : B (2 * n') := B2n n' in _).
change (B (S (n' + S (n' + 0)))).
rewrite <- (plus_n_Sm n' (n' + 0)).
change (B (2 + (2 * n'))).
refine (match 2 * n' as nn return B nn -> B (2 + nn)
        with O => fun _ => iff_refl P | S n'' => _ end IH).
intro IH'.
change (P <-> (P <-> B (S n''))).
tauto.
Qed.

End Barendregt.

Lemma iffP : forall P : Prop, P <-> (P <-> (P <-> (P <-> (P <-> (P <-> (P <-> (P <-> (P <-> P)))))))).
Proof.
exact (fun P => B2n P 5).
Qed.
