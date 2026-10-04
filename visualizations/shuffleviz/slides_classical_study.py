"""Definition reminders and study checkpoints interleaved with the classical riffle chapter."""
from __future__ import annotations

from manim import DOWN, LEFT, RIGHT, UP, FadeIn, LaggedStart, VGroup

from shuffleviz.style import ERROR, FG, LOCAL, MUTED, UNIFORM, DeckSlide, boxed, colored_math, math, para, tex
from shuffleviz.study import definition_box, derivation_steps, glossary_grid, remember_box, reminder_box


SOURCE_BD = "Bayer and Diaconis (1992), Trailing the Dovetail Shuffle to its Lair."


class CS00ClassicalNotation(DeckSlide):
    title = "Classical riffle notation — keep this dictionary nearby"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        grid = glossary_grid([
            (r"$n$", r"number of cards; the famous example has $n=52$"),
            (r"$k$", r"number of successive ideal riffle shuffles"),
            (r"$a=2^k$", r"number of equally likely inverse labels after $k$ riffles"),
            (r"$\pi\in S_n$", r"a particular permutation of the $n$ cards"),
            (r"$d(\pi)$", r"number of descents: adjacent positions where $\pi_i>\pi_{i+1}$"),
            (r"$r(\pi)=d(\pi)+1$", r"number of maximal increasing runs / rising sequences"),
            (r"$Q_a$", r"law of an $a$-shuffle; after $k$ riffles use $a=2^k$"),
            (r"$U$", r"uniform law: every permutation has probability $1/n!$"),
        ], body_size=18).shift(DOWN * 0.1)
        self.say("Part one is self-contained even if you skip the foundations chapter. These eight symbols carry almost the whole Bayer--Diaconis derivation. We will remind you of them when they reappear.")
        self.play(FadeIn(grid))


class CS01TVReminder(DeckSlide):
    title = "Reminder: what exactly are we measuring when we say 'mixed'?"
    kicker = r"$d_{TV}(Q,U)=\frac12\sum_{\pi\in S_n}|Q(\pi)-U(\pi)|$"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        rem = reminder_box(
            "total variation",
            r"The finite probability distance obtained by summing absolute mass discrepancies and dividing by two. Equivalently, it is the largest difference $|Q(A)-U(A)|$ over events $A$.",
            symbol=r"d_{TV}",
            color=ERROR,
        ).shift(UP * 0.8)
        rows = derivation_steps([
            ("Not a visual test", r"One messy-looking deck order is only one sample; it does not define a probability distance."),
            ("Not entropy alone", r"Having enough random bits is necessary, but it does not say how evenly those bits cover permutations."),
            ("Our target", r"Compute the exact law $Q$ induced by riffles, compare it with $U$, and exploit structure to avoid summing $n!$ unrelated terms."),
        ], width=10.5, body_size=22).shift(DOWN * 1.15)
        self.say("This reminder is important because the phrase seven shuffles often gets repeated without saying which metric or model produced it. Here the model is the ideal Gilbert--Shannon--Reeds (GSR) riffle and the distance is total variation.")
        self.play(FadeIn(rem), FadeIn(rows))


class CS05DescentDefinition(DeckSlide):
    title = "Definition: descents cut a permutation into rising sequences"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        row = math(r"1\quad 3\quad 6\quad 2\quad 4\quad 5\quad 7\quad 8", size=44).shift(UP * 0.8)
        relation = colored_math(
            (r"1<3<6", UNIFORM),
            (r"\;>\;", ERROR),
            (r"2<4<5<7<8", UNIFORM),
            size=35,
        ).shift(DOWN * 0.15)
        defs = VGroup(
            definition_box("Descent", r"An index $i$ with $\pi_i>\pi_{i+1}$.  Here there is one descent, at $6>2$.", symbol=r"d(\pi)", color=ERROR, width=5.3, body_size=21),
            definition_box("Rising sequence", r"A maximal consecutive increasing block.  One descent creates two rising sequences.", symbol=r"r(\pi)=d(\pi)+1", color=LOCAL, width=5.3, body_size=21),
        ).arrange(RIGHT, buff=0.4).shift(DOWN * 1.45)
        self.say("A rising sequence is not an arbitrary increasing subsequence. It is a maximal consecutive run in the one-line permutation. That word consecutive matters for every formula that follows.")
        self.play(FadeIn(row), FadeIn(relation), FadeIn(defs))


class CS09StarsAndBarsPrimer(DeckSlide):
    title = "Mini-lesson: why weakly increasing labels are counted by stars-and-bars"
    kicker = r"$0\le z_1\le\cdots\le z_n\le M$ is a multiset of size $n$ from $M+1$ values"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        example = math(r"0\le z_1\le z_2\le z_3\le 2", size=36, color=LOCAL).shift(UP * 1.2)
        seqs = tex(r"Examples: $(0,0,2),\ (0,1,1),\ (1,2,2)$", size=25, color=MUTED).shift(UP * 0.45)
        steps = derivation_steps([
            ("Forget order", r"Because the sequence is already sorted, it is determined by how many 0s, 1s, ..., $M$s it contains."),
            ("Counts", r"Choose nonnegative counts $c_0+\cdots+c_M=n$."),
            ("Stars-and-bars", r"The number of solutions is $\binom{n+M}{n}$."),
            ("Our use", r"After removing $r-1$ forced strict steps, $M=a-r$, so the count is $\binom{a+n-r}{n}$."),
        ], width=10.7, body_size=20).shift(DOWN * 1.25)
        self.say("We pause here because stars-and-bars is carrying real probability mass. The compatible inverse labels are not a metaphor: they are exactly these weakly increasing integer sequences.")
        self.play(FadeIn(example), FadeIn(seqs), FadeIn(steps))


class CS12EulerianDefinition(DeckSlide):
    title = "Definition: Eulerian numbers count permutations by descents"
    kicker = r"$A(n,d)=\#\{\pi\in S_n:d(\pi)=d\}$"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        box = definition_box(
            "Eulerian number",
            r"$A(n,d)$ counts permutations of $n$ objects having exactly $d$ descents, equivalently exactly $d+1$ rising sequences.  Do not confuse Eulerian numbers with Euler numbers or binomial coefficients.",
            symbol=r"A(n,d)",
            color=LOCAL,
        ).shift(UP * 0.7)
        row = math(r"A(4,0),A(4,1),A(4,2),A(4,3)=1,11,11,1", size=34, color=UNIFORM).shift(DOWN * 0.65)
        check = math(r"1+11+11+1=24=4!", size=31).shift(DOWN * 1.5)
        self.say("Eulerian numbers are the multiplicities we need when the per-permutation GSR probability depends only on the descent count. They tell us how many terms share the same likelihood.")
        self.play(FadeIn(box), FadeIn(row), FadeIn(check))


class CS13TVClassCollapsePrimer(DeckSlide):
    title = "Why a statistic can collapse the TV sum without losing anything"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        steps = derivation_steps([
            ("Partition", r"Group permutations by rising-sequence count $r$: $C_r=\{\pi:r(\pi)=r\}$."),
            ("Constant likelihood", r"Every $\pi\in C_r$ has the same $Q_a(\pi)$, while every permutation has the same uniform mass $1/n!$."),
            ("Multiply once", r"The contribution of the whole class is $|C_r|\,|Q_a(\pi_r)-1/n!|$."),
            ("Eulerian multiplicity", r"$|C_r|=A(n,r-1)$, leaving only $n$ class terms instead of $n!$ permutation terms."),
        ], body_size=21).shift(DOWN * 0.1)
        exact = math(r"d_{TV}(Q_a,U)=\frac12\sum_{r=1}^n A(n,r-1)\left|\frac{\binom{a+n-r}{n}}{a^n}-\frac1{n!}\right|", size=28, color=UNIFORM).shift(DOWN * 2.25)
        self.say("This is an exact aggregation, not an approximation. We are allowed to collapse because the sign and magnitude of the pointwise probability difference are constant inside each class.")
        self.play(FadeIn(steps), FadeIn(exact))


class CS18CutoffReminder(DeckSlide):
    title = r"Reminder: the $\tfrac32\log_2 n$ statement is a cutoff scale"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        rem = reminder_box(
            "cutoff",
            r"For a sequence of larger and larger chains, the distance to stationarity stays large until near a characteristic time and then falls through a much narrower transition window. It is an asymptotic shape statement, not an exact finite threshold.",
            color=ERROR,
        ).shift(UP * 0.65)
        scale = math(r"k\approx\frac32\log_2 n + c", size=44, color=UNIFORM).shift(DOWN * 0.65)
        note = remember_box(r"For $n=52$, seven lies inside the rapid transition region.  It does not mean the seventh riffle produces exact uniformity, nor that six is useless and seven is perfect.", width=10.6, size=23).shift(DOWN * 1.65)
        self.say(f"Keep the finite and asymptotic statements separate. The exact 52-card TV table is one finite calculation; the three-halves log-two n result explains why the transition lives on that scale as n grows.\n[Sources] {SOURCE_BD}")
        self.play(FadeIn(rem), FadeIn(scale), FadeIn(note))


class CS21ClassicalGlossary(DeckSlide):
    title = "Classical riffle glossary and checkpoint"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        grid = glossary_grid([
            ("Gilbert--Shannon--Reeds (GSR) riffle", r"binomial cut plus uniformly random order-preserving interleaving"),
            ("inverse riffle", r"independent card labels followed by a stable sort"),
            ("stable sort", r"sort by label while preserving old relative order among equal labels"),
            (r"$a$-shuffle", r"assign independent uniform labels in $\{0,\ldots,a-1\}$ and stable-sort"),
            ("descent", r"adjacent reversal $\pi_i>\pi_{i+1}$"),
            ("rising sequence", r"maximal consecutive increasing run; count is descents plus one"),
            (r"$A(n,d)$", r"Eulerian number: permutations of $n$ with exactly $d$ descents"),
            (r"$Q_a(\pi)$", r"$a$-shuffle probability $a^{-n}\binom{a+n-r(\pi)}{n}$"),
            ("likelihood ratio", r"$Q_a(\pi)/U(\pi)$; tells which orders are overrepresented"),
            ("seven riffles", r"for 52 ideal GSR riffles, the seventh-step TV is about $0.334$, not zero"),
        ], body_size=17).shift(DOWN * 0.15)
        self.say("If you can explain every entry on this slide without looking backward, you own the vocabulary needed to formalize the classical local-shuffle kernel.")
        self.play(FadeIn(grid))

class CS16LikelihoodRatioPrimer(DeckSlide):
    title = "Definition: the likelihood ratio says how over- or under-represented a state is"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        definition = definition_box(
            "Likelihood ratio",
            r"When the reference law $U$ assigns positive mass everywhere, define $L(\pi)=Q(\pi)/U(\pi)$.  $L>1$ means the shuffled law puts more mass on that permutation than uniform does; $L<1$ means less mass.",
            symbol=r"L(\pi)=\frac{Q(\pi)}{U(\pi)}",
            color=LOCAL,
        ).shift(UP * 0.65)
        grid = glossary_grid([
            (r"$L(\pi)=1$", r"the two laws assign exactly the same probability to $\pi$"),
            (r"$L(\pi)>1$", r"$\pi$ contributes positive excess mass $Q(\pi)-U(\pi)$"),
            (r"$L(\pi)<1$", r"$\pi$ contributes a probability deficit relative to uniform"),
            (r"$A_+=\{L\ge1\}$", r"the positive-excess region; for finite laws $Q(A_+)-U(A_+)=d_{TV}(Q,U)$"),
        ], body_size=18).shift(DOWN * 1.25)
        self.say("The likelihood ratio is the right object for locating the event that witnesses total variation. Once we show it is monotone in rising-sequence count, the n-factorial optimization over events collapses to one threshold.")
        self.play(FadeIn(definition), FadeIn(grid))
