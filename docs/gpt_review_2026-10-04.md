# GPT Review of the overnight Lean build (received 2026-10-04)

Verbatim record of the review message (from the pi session
transcript `01a104d1-84ab-75e8-9ce6-86eeb46b1e80`). Per-finding status
is tracked in `docs/autonomous_lean_build.md` §4a.

---

I have a GPT Review: The agent has made **substantial useful progress**, but I would interrupt it now before it builds more theory on top of two design/math mistakes.

Since the overnight handoff, it made about 18 commits and added roughly 2,500 lines. The progression is sensible: kernel algebra → matrix bridges → TV theory → perturbation → Dobrushin → reversible Markov theory → start of general Bernoulli–Laplace. The working tree is clean, there are no `sorry`/`admit`s, it did not introduce new `native_decide` brute force or disable heartbeats, and the Python regression suite is still **7/7 passing**. I cannot run `lake build` in this environment because `lake` is unavailable here, so the Lean verification is based on source review plus the agent's recorded green builds.

## Findings

1. **High: the Dobrushin theorem has an unnecessary factor of 2.** In `Dobrushin.lean`, it defines

   \[
   \delta(K)=\max_{x,x'} d_{\rm TV}(K_x,K_{x'})
   \]

   correctly, but then introduces

   \[
   \texttt{dobrushin2}(K)=2\delta(K)
   \]

   and proves

   \[
   d_{\rm TV}(\mu K,\nu K)
   \le 2\delta(K)d_{\rm TV}(\mu,\nu).
   \]

   The standard sharp theorem is

   \[
   \boxed{d_{\rm TV}(\mu K,\nu K)\le\delta(K)d_{\rm TV}(\mu,\nu)}.
   \]

   The current theorem is true but much too weak. It is not a harmless constant: for the identity kernel, \(\delta=1\), while its claimed “contraction constant” is 2. Iterating gives a useless \(2^n\) upper bound where the correct coefficient is \(1^n\). For a kernel with \(\delta=0.6\), the correct theorem contracts by \(0.6\), while its version expands the bound by \(1.2\).

   This infects `dobrushin2_submult`, `run_contraction`, and any future weighted perturbation theorem. I would mark Priority D **not complete** and fix it now.

   The proof lost the factor because it centers the row-set probability \(r_x\) at an arbitrary \(x_0\) and then pays

   \[
   \sum_x |\mu_x-\nu_x| = 2\,d_{\rm TV}(\mu,\nu).
   \]

   The sharp proof should exploit the positive/negative decomposition of \(\mu-\nu\), or equivalently the oscillation

   \[
   \max_x r_x-\min_x r_x\le\delta(K).
   \]

2. **High: `BLState N m k` has the wrong dependency.** In `BernoulliLaplaceGeneral.lean`:

   ```lean
   def BLState (N m _ : Nat) : Type := ...
   ```

   `k` is deliberately carried as a phantom parameter even though the state space does not depend on the exchange size. That is exactly the wrong abstraction for this project.

   We want to compare \(k=24,25,26\), optimize over \(k\), and compose different exchange kernels on the **same state space**. With `BLState N m k`, those become different Lean types.

   It should be approximately:

   ```lean
   BLState N m
   ```

   with

   ```lean
   exchangeKernel N m k : FiniteKernel (BLState N m) (BLState N m)
   ```

   If we later generalize the number of marked/red cards independently, then the state type might depend on `N m r`, but still **not** on `k`.

3. **High-ish architecture: the “general” BL module imports the Commander-specific module.** `BernoulliLaplaceGeneral.lean` currently imports:

   ```lean
   import Shufflemath.BernoulliLaplace
   ```

   even though its present 114 lines don't use anything from it.

   This puts the dependency arrow backwards. The generic symbolic theory should not drag in the fixed 99-card executable certificate. If we want a theorem equating the generic kernel with the Commander implementation, put that in a small bridge module importing both, e.g. conceptually:

   ```text
   BernoulliLaplaceGeneral
   BernoulliLaplace
   BernoulliLaplaceCommanderBridge
   ```

   That also avoids a future import cycle if we ever want the concrete implementation to reuse generic theory.

4. **Medium: the perturbation theorem is mathematically useful, but its API is stronger and clumsier than necessary.** `hybridTelescope` assumes a single uniform contraction constant `d` for **every kernel in both protocols**.

   In its actual hybrid proof, the discrepancy at a changed step is propagated through one common suffix. Only that suffix needs contraction bounds. `hdK` appears to be unnecessary baggage caused by the recursive theorem signature.

   I would separate the theory cleanly:

   - unconditional crude telescope, using ordinary TV contraction:
     \[
     TV(\mu K_1\cdots K_T,\mu L_1\cdots L_T)
     \le\sum_i\Delta(K_i,L_i);
     \]
   - sharp weighted theorem:
     \[
     \le
     \sum_i \Delta(K_i,L_i)
     \prod_{j>i}\delta(\text{chosen common suffix kernel}_j).
     \]

   The current uniform-\(d\) theorem can remain as a corollary if useful. I would not call Priority C/D finished until the natural API exists.

5. **Medium: `Dist.tv_eq_zero` has a false explanatory comment and stops one theorem short.** It says:

   > distinct `Dist` representations can share the same mass function

   That is not right for `StdSimplex`/`Finsupp`. Equal mass functions determine equal weights, and proof fields are proof-irrelevant. The same codebase already proves equality of `Dist`s elsewhere using `ext x`.

   We should have the actual metric separation theorem:

   \[
   \boxed{tv(p,q)=0\iff p=q}.
   \]

   The existing pointwise-mass form can remain as a helper.

6. **Medium-low: there is noticeable LLM duplication that should be cleaned before it spreads.** Examples:
   - `Perturbation.lean` contains its own private `double_sum_pullout` even though `Dist.double_sum_pullout` was made public specifically for reuse.
   - `Dobrushin.lean` reproves that `apply μ K` has nonnegative masses and sums to one. But `apply μ K` is already a `Dist`, so these are simply `Dist.mass_nonneg` and `Dist.sum_mass`.
   - There are matrix and kernel versions of row-TV/pair-distance/Dobrushin concepts. The semantic kernel version should become canonical and the matrix API should be clearly derived/compatibility-only.

   This isn't catastrophic, but it is exactly the kind of vibe-coded duplication we want to stop early.

7. **Medium-low: `Markov.lean` proves a useful self-adjointness identity, but its docstring overstates what follows.** The theorem

   \[
   \langle f,Kg\rangle_\mu=\langle g,Kf\rangle_\mu
   \]

   is good. But the comment says this gives an orthogonal eigenbasis. As written:
   - coefficients are over `Rat`;
   - the weighted form can be degenerate if \(\mu(x)=0\);
   - a rational self-adjoint matrix need not have all eigenvalues/eigenvectors over \(\mathbb Q\).

   Keep the algebraic self-adjointness theorem. Don't claim the full real spectral theorem until we explicitly move to \(\mathbb R\) and handle support/positivity.

8. **Process issue: the new BL module is not imported by `Shufflemath.lean`.** Nothing else imports it either. That means there is at least a real risk that the ordinary top-level build is not exercising this newest module. Before the agent continues F2, I would require either:
   ```bash
   lake env lean Shufflemath/BernoulliLaplaceGeneral.lean
   ```
   or wire it into the library import graph and run the full build.

9. **Minor documentation hallucination:** `Finite.lean` calls ordinary Markov-kernel pushforward a “Krein–von Neumann pushforward.” That terminology is unrelated here and should simply say kernel pushforward / mixture of rows.

10. **Workflow:** the agent did not follow your requested commit trailer. Most commits use:
    ```text
    Co-authored-by: Qwen3.8:27b <noreply@openai.com>
    ```
    and at least one commit appears to lack a trailer. I would not rewrite published history merely for that, but future commits should follow whatever attribution convention you want.

## What I think is genuinely good

The finite-kernel algebra is a strong foundation. `apply_comp`, associativity, identity laws, powers, and the matrix bridge are exactly the right things to formalize, and the implementation remains centered on `StdSimplex` rather than inventing another probability type.

The TV work is also good. The triangle inequality, positive-set construction, exact event-excess formula, general kernel contraction, and mass-level pushforward formula are all directly useful. The positive-set work in particular is the right groundwork for both Dobrushin and the eventual Bayer–Diaconis likelihood-ratio event.

The Markov layer is compact and conceptually clean: stationarity, detailed balance, detailed-balance-implies-stationarity, function action, and the weighted self-adjoint identity. That is exactly enough theory without trying to build an entire probability library.

The agent has also shown good discipline about small commits and avoiding `sorry`. So I would **correct it rather than replace it**.

### Recommendation

I would stop the current F work temporarily and give it this order:

**First fix Dobrushin sharply**, remove `dobrushin2`, and prove the real \(\delta(K)\) contraction/submultiplicativity/iteration theorem. Then simplify the perturbation API around that result. Then fix the BL state type so `k` is a kernel parameter rather than a state-space parameter, remove the generic→Commander import, explicitly compile the new module, and only then continue with row stochasticity/stationarity/detailed balance.

After those fixes, I think the overnight work is a **net positive and quite a large one**. Right now I would not merge further BL theory on top of the current D/BL abstractions.
