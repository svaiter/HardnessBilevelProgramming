# Independent source synthesis

Reviewed only `packets/source.json`, before viewing any candidate claims. Its 281 spans mix the paper's statements and proofs with repository corrections, alternative constructions, and selected Lean declarations. Blueprint labels such as `[prove]` describe intended arguments; they do not by themselves certify a completed Lean proof.

The fixed lower feasible set is independent of the upper variable. The lower argmin is defined by universal comparison of Q over that set. Optimistic and pessimistic values are respectively the infimum and supremum of P over this argmin. Empty argmins give +∞ and −∞ respectively. Finite infima need not be attained.

The smooth representation theorem concerns proper lower semicontinuous functions valued in ℝ∪{+∞} with closed effective domain. It constructs smooth, not necessarily polynomial or analytic, P,Q with three unrestricted lower variables. Whitney zero sets encode the real epigraph and domain. On the finite domain, the lower zero set includes both the epigraph coordinate and the reciprocal constraint; outside it, the reciprocal gadget prevents attainment. The argmin of h² must not be replaced by the argmin of h.

Extended semialgebraicity comprises the finite graph and both infinite-value loci. Quantifier elimination gives semialgebraicity for any semialgebraic lower feasible set, without attainment. The finite graph needs a lower-bound condition plus approximation for every positive ε. Compactness with nonemptiness and continuous P,Q gives attained finite values, lower semicontinuity, and two-sided bounds on each compact upper-variable set; empty feasible sets retain semicontinuity but not finite-valuedness.

The corrected expressivity results are:

- Unbounded-box polynomial values equal all extended-real semialgebraic functions; unrestricted lower spaces suffice for representation.
- Nonempty bounded-box polynomial values equal SA∩LSC∩CB. CB is local boundedness on every compact, not a global bound, and excludes infinite values.
- Convex lower objectives over unbounded boxes represent every piecewise polynomial function; only inclusions PP⊆C_unbound⊆SA are asserted.
- Bounded convex-lower box values satisfy PP∩LSC⊆C_bounded⊆SA∩LSC∩CB; equality is not supplied.
- Nonempty compact convex semialgebraic lower sets restore equality C_cc=SA∩LSC∩CB. Moment lifting preserves values; coefficients depend polynomially on x. Only positive-weight components of an optimal convex combination must be optimal.

General semialgebraic growth as printed is false in dimension ≥2. Boundedness on bounded sets repairs the premise. The blueprint uses projection, closed-set finiteness, and corrected growth assumptions, while polynomial sign normalization needs no general growth theorem. Convex constructions have global convexity in lower variables. Their useful invariant is constancy of P on the argmin, not uniqueness of lower minimizers. General extended-real optimistic constructions cannot simply be reused pessimistically. Negation gives the representation counterparts, replacing LSC by USC.

The complexity reduction asks whether the global optimistic value is strictly below a threshold. SSI asks for an integer in [R,R+2^r−1] missed by every subset sum, with positive input integers and r≤k. It constructs integer polynomials of total degree at most five over [0,1]^(k+1), with scalar z. The value is 1 off binary upper inputs and −min H on binary inputs. Compactness turns an absent subset sum into a strictly negative value; NO instances have optimum exactly zero. Coefficient sizes are O(log M); polynomial input size uses r≤k. Degree exactly five requires nonzero corresponding dimensions. The packet separates proved reduction correctness and degree bounds from the unformalized polynomial-time/Σ₂ᵖ-hardness wrapper. It supplies neither Σ₂ᵖ membership for the target nor a pessimistic hardness theorem.
