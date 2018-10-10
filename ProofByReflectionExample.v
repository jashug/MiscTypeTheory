(* Adapted from Barendregt: https://gist.github.com/palmskog/341da4e54ff7e805077b6e0b3af7d21d *)
Section Barendregt.

Variable P : Prop.

Fixpoint B (n : nat) := match n with | O => P | S n' => P <-> B n' end.

Lemma B2n: forall n, B (1 + n * 2).
Proof.
exact (fix B2n n : B (1 + n * 2) :=
  match n with
  | O => iff_refl P
  | S n' => let IH : B (1 + n' * 2) := B2n n' in
            ltac:(tauto) : P <-> (P <-> B (1 + n' * 2))
  end).
Qed.

End Barendregt.

Lemma iffP : forall P : Prop, P <-> (P <-> (P <-> (P <-> (P <-> (P <-> (P <-> (P <-> (P <-> P)))))))).
Proof.
exact (fun P => B2n P 4).
Qed.
