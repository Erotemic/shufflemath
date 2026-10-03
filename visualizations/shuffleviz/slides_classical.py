"""Part 1: discover the Bayer--Diaconis seven-riffle result from first principles.

The pedagogical goal of this section is not to quote ``seven shuffles`` but to
make every ingredient feel inevitable:

1. specify the GSR physical model;
2. invert it into independent labels;
3. notice that rising sequences are the surviving statistic;
4. count compatible labels;
5. count permutations in each rising-sequence class;
6. collapse total variation from n! states to n terms;
7. read the 52-card answer and understand the 3/2 log_2(n) scale.
"""
from __future__ import annotations

from math import sqrt

from manim import (
    DOWN,
    LEFT,
    RIGHT,
    UP,
    ArcBetweenPoints,
    Arrow,
    Axes,
    Brace,
    Create,
    DashedLine,
    Dot,
    FadeIn,
    FadeOut,
    GrowArrow,
    Indicate,
    LaggedStart,
    Line,
    MoveAlongPath,
    Rectangle,
    ReplacementTransform,
    SurroundingRectangle,
    Transform,
    TransformFromCopy,
    VGroup,
    VMobject,
)

from shuffleviz import model
from shuffleviz.style import (
    ERROR,
    FAINT,
    FG,
    LOCAL,
    MUTED,
    PANEL,
    UNIFORM,
    DeckSlide,
    boxed,
    colored_math,
    math,
    mono,
    para,
    tex,
)
from shuffleviz.visual import card, deck_row


SOURCE_BD = "Bayer and Diaconis (1992), Trailing the Dovetail Shuffle to its Lair."
SOURCE_GSR = "Gilbert (1955); Shannon/Reeds formulation as summarized by Bayer and Diaconis (1992)."


def numbered_row(values, color=LOCAL, width=0.62, height=0.82, buff=0.08, size=24):
    """Small numbered cards for mechanics examples."""
    out = VGroup()
    for value in values:
        box = card(width, height, color=color, fill_opacity=0.08, stroke_width=1.8)
        label = tex(str(value), size=size, color=FG).move_to(box)
        out.add(VGroup(box, label))
    out.arrange(RIGHT, buff=buff)
    return out


def bit_row(bits, cards, color=LOCAL):
    return VGroup(*[tex(str(bit), size=22, color=color).next_to(c, UP, buff=0.08) for bit, c in zip(bits, cards)])


def rising_dividers(values, row, color=ERROR):
    """Vertical marks at descents in a one-line permutation."""
    marks = VGroup()
    for idx, (a, b) in enumerate(zip(values, values[1:])):
        if a > b:
            x = (row[idx].get_right()[0] + row[idx + 1].get_left()[0]) / 2
            marks.add(Line([x, row.get_bottom()[1] - 0.08, 0], [x, row.get_top()[1] + 0.08, 0], color=color, stroke_width=4))
    return marks


def polyline(axes, xs, ys, color, width=4, opacity=1.0):
    path = VMobject(stroke_color=color, stroke_width=width, stroke_opacity=opacity)
    path.set_points_as_corners([axes.c2p(x, y) for x, y in zip(xs, ys)])
    return path


def probability_bars(axes, xs, ys, color, opacity=0.75, width=0.16):
    bars = VGroup()
    zero = axes.c2p(0, 0)[1]
    for x, y in zip(xs, ys):
        top = axes.c2p(x, y)[1]
        h = max(0.001, top - zero)
        rect = Rectangle(width=width, height=h, stroke_width=0, fill_color=color, fill_opacity=opacity)
        rect.move_to([axes.c2p(x, 0)[0], zero + h / 2, 0])
        bars.add(rect)
    return bars


def move_item_to_card_center(item, card_mob, target_center):
    """Return an animation that moves a card-plus-annotation group by card center."""
    return item.animate.shift(target_center - card_mob.get_center())


def arc_move(mob, target_center, angle=0.42, run_time=0.34):
    """Move a card on a visible arc instead of teleporting between layouts."""
    path = ArcBetweenPoints(mob.get_center(), target_center, angle=angle)
    return MoveAlongPath(mob, path, run_time=run_time)


class C00SevenShuffles(DeckSlide):
    title = "Why seven riffle shuffles?"
    kicker = "Start with the famous 52-card result and derive it ourselves"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        deck = deck_row(26, LOCAL, width=8.9, height=0.74).shift(DOWN * 0.35)
        seven = tex(r"$7$", size=108, color=ERROR).shift(UP * 0.55)
        q = para(
            r"What model of a riffle makes this a theorem?  What feature of a permutation remembers the shuffle?  "
            r"And how can we possibly compute a distance on $52!$ deck orders?",
            10.7,
            29,
        ).shift(DOWN * 1.55)
        self.say(f"Open with the headline, but do not ask the audience to trust it. We are going to rebuild the argument from the physical shuffle.\n[Sources] {SOURCE_BD}")
        self.play(LaggedStart(*[FadeIn(c, shift=UP * 0.08) for c in deck], lag_ratio=0.02))
        self.play(FadeIn(seven), FadeIn(q))


class C01RandomIsADistribution(DeckSlide):
    title = "First trap: a deck does not become 'random-looking'"
    kicker = "The object that mixes is a probability distribution on all $52!$ orders"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        sample = numbered_row([7, 2, 8, 1, 5, 3, 6, 4], color=LOCAL).scale(0.9).shift(LEFT * 3.2 + UP * 0.5)
        sample_lab = tex("one observed order", size=24, color=MUTED).next_to(sample, DOWN, buff=0.2)
        cloud = VGroup(*[
            boxed(tex(s, size=19, color=MUTED), MUTED, 0.16)
            for s in ["1 2 3 ...", "1 2 4 ...", "1 3 2 ...", r"\vdots", "8 7 6 ..."]
        ]).arrange(DOWN, buff=0.12).shift(RIGHT * 3.15 + UP * 0.35)
        target = math(r"U(\pi)=\frac{1}{52!}", size=39, color=UNIFORM).shift(RIGHT * 3.15 + DOWN * 1.55)
        arrow = Arrow(sample.get_right(), cloud.get_left(), color=FAINT, buff=0.35)
        self.say("A single shuffled deck is just one sample. The theorem is about the law of that sample. Uniform means every permutation receives exactly the same probability.")
        self.play(FadeIn(sample), FadeIn(sample_lab), GrowArrow(arrow), FadeIn(cloud), FadeIn(target))
        self.say("This distinction matters later: visual disorder is not a distance to uniformity. We need the full law, or a statistic that captures the full likelihood ratio.")


class C01EntropyLowerBound(DeckSlide):
    title = "A first guess says at least five -- so where do seven come from?"
    kicker = "Entropy gives a necessary condition, but it throws away the geometry of the shuffle"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        uniform = math(r"\log_2(52!)\approx225.58\text{ bits}", size=39, color=UNIFORM).shift(UP * 1.15)
        source = math(r"\text{one inverse riffle uses }52\text{ independent fair bits}", size=34, color=LOCAL).shift(UP * 0.15)
        bound = colored_math(
            (r"52k\ge225.58", FG),
            (r"\quad\Longrightarrow\quad k\ge5", ERROR),
            size=38,
        ).shift(DOWN * 0.8)
        question = boxed(
            para(r"Five is only an information-theoretic floor.  To discover seven we must ask \emph{which} permutations receive too much probability, not merely how many random bits were used.", 10.3, 28),
            ERROR,
            0.28,
        ).shift(DOWN * 1.85)
        self.say("Before opening Bayer and Diaconis, try the obvious lower bound. A uniform 52-card order contains log2(52!) about 225.6 bits of uncertainty. One inverse riffle is driven by only 52 fair bits, so four riffles cannot possibly suffice.")
        self.play(FadeIn(uniform), FadeIn(source), FadeIn(bound))
        self.say("But entropy only gets us to five. It cannot explain the famous seven. That gap is the puzzle: the random bits enter the permutation in a highly structured way.")
        self.play(FadeIn(question))


class C02RiffleMechanicsLab(DeckSlide):
    title = "Watch one ideal riffle happen"
    kicker = "The randomness is in the cut and the left/right drop sequence"
    section = "Part 1 · discovering the classical riffle result"
    handout = False

    def body(self):
        values = list(range(1, 9))
        cut = 3
        source_word = list("LRLRRLRR")
        output_indices = [0, 3, 1, 4, 5, 2, 6, 7]

        cards = numbered_row(values).shift(UP * 1.45)
        cut_mark = Line(
            [cards[cut - 1].get_right()[0] + 0.06, cards.get_bottom()[1] - 0.12, 0],
            [cards[cut - 1].get_right()[0] + 0.06, cards.get_top()[1] + 0.12, 0],
            color=ERROR,
            stroke_width=4,
        )
        self.say("Start with eight ordered cards so every motion is traceable. The GSR cut chooses a packet size; this realization cuts after card 3.")
        self.play(FadeIn(cards), Create(cut_mark))

        left_target = numbered_row(values[:cut]).scale(0.82).move_to(LEFT * 2.65 + UP * 0.22)
        right_target = numbered_row(values[cut:]).scale(0.82).move_to(RIGHT * 2.35 + UP * 0.22)
        cut_anims = []
        for j in range(cut):
            cut_anims.append(cards[j].animate.scale(0.82).move_to(left_target[j].get_center()))
        for j in range(cut, len(values)):
            cut_anims.append(cards[j].animate.scale(0.82).move_to(right_target[j - cut].get_center()))
        self.play(FadeOut(cut_mark), *cut_anims, run_time=0.85)

        left_lab = tex("left packet", size=20, color=LOCAL).next_to(VGroup(*cards[:cut]), UP, buff=0.14)
        right_lab = tex("right packet", size=20, color=LOCAL).next_to(VGroup(*cards[cut:]), UP, buff=0.14)
        rule = math(
            r"\Pr(\text{next}=L)=\frac{\ell}{\ell+r},\qquad"
            r"\Pr(\text{next}=R)=\frac{r}{\ell+r}",
            size=28,
            color=LOCAL,
        ).shift(DOWN * 0.72)
        counter = mono("remaining: L=3  R=5", size=20, color=MUTED).next_to(rule, DOWN, buff=0.14)
        self.say("Interleaving is order-preserving. At each drop, choose a packet in proportion to how many cards remain in it. That sequential rule is equivalent to a uniformly chosen order-preserving interleaving conditional on the cut.")
        self.play(FadeIn(left_lab), FadeIn(right_lab), FadeIn(rule), FadeIn(counter))

        output_values = [values[i] for i in output_indices]
        output_target = numbered_row(output_values).scale(0.82).shift(DOWN * 1.85)
        source_markers = VGroup(*[
            mono(letter, size=18, color=LOCAL).next_to(output_target[j], UP, buff=0.09)
            for j, letter in enumerate(source_word)
        ])

        lrem, rrem = cut, len(values) - cut
        for j, (idx, letter) in enumerate(zip(output_indices, source_word)):
            if letter == "L":
                lrem -= 1
                angle = 0.48
            else:
                rrem -= 1
                angle = -0.48
            new_counter = mono(f"remaining: L={lrem}  R={rrem}", size=20, color=MUTED).move_to(counter)
            self.play(
                arc_move(cards[idx], output_target[j].get_center(), angle=angle, run_time=0.32),
                FadeIn(source_markers[j], shift=DOWN * 0.08),
                Transform(counter, new_counter),
            )

        word = VGroup(*source_markers)
        word_box = SurroundingRectangle(word, color=LOCAL, buff=0.08, stroke_width=2)
        caption = tex("the interleaving word", size=20, color=MUTED).next_to(word_box, DOWN, buff=0.11)
        self.say("The physical shuffle has become a binary word: L R L R R L R R. Once that word is fixed, the output order is forced. This is the object whose probability will cancel cleanly in the next scene.")
        self.play(Create(word_box), FadeIn(caption))


class C02GSRForwardMechanics(DeckSlide):
    title = "Model one ideal riffle: cut, then interleave without disturbing either packet"
    kicker = "The Gilbert--Shannon--Reeds model makes the physical move probabilistic"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        start = numbered_row(range(1, 9)).shift(UP * 1.55)
        left = numbered_row([1, 2, 3], color=LOCAL).scale(0.9).shift(LEFT * 2.2 + UP * 0.35)
        right = numbered_row([4, 5, 6, 7, 8], color=LOCAL).scale(0.9).shift(RIGHT * 2.0 + UP * 0.35)
        cut_arrow_l = Arrow(start.get_bottom(), left.get_top(), color=FAINT, buff=0.18)
        cut_arrow_r = Arrow(start.get_bottom(), right.get_top(), color=FAINT, buff=0.18)
        output = numbered_row([1, 4, 2, 5, 6, 3, 7, 8], color=LOCAL).shift(DOWN * 1.25)
        out_arrow = Arrow([0, -0.1, 0], output.get_top(), color=FAINT, buff=0.18)
        cutlaw = math(r"\Pr(C=c)=\binom{n}{c}2^{-n}", size=31).shift(LEFT * 3.55 + DOWN * 2.2)
        interleave = math(r"\Pr(w\mid C=c)=\binom{n}{c}^{-1}", size=31).shift(RIGHT * 0.3 + DOWN * 2.2)
        cancel = math(r"\Pr(w)=2^{-n}", size=35, color=UNIFORM).shift(RIGHT * 4.45 + DOWN * 2.2)
        self.say(f"GSR first chooses a binomial cut. Conditional on a cut of size c, every order-preserving interleaving is equally likely.\n[Sources] {SOURCE_GSR}")
        self.play(FadeIn(start), GrowArrow(cut_arrow_l), GrowArrow(cut_arrow_r), FadeIn(left), FadeIn(right))
        self.say("The internal order of each packet is sacred. Only the interleaving is random.")
        self.play(GrowArrow(out_arrow), FadeIn(output))
        self.say("Now the first useful cancellation: the binomial coefficient in the cut probability cancels the number of interleavings. Every binary source pattern w has probability exactly 2^{-n}.")
        self.play(FadeIn(cutlaw), FadeIn(interleave), FadeIn(cancel))


class C03WhyInvert(DeckSlide):
    title = "The forward riffle is awkward; invert the permutation"
    kicker = "Inversion preserves uniformity and total variation, but exposes the structure"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        physical_vals = [1, 4, 2, 5, 6, 3, 7, 8]
        inverse_vals = [1, 3, 6, 2, 4, 5, 7, 8]
        physical = numbered_row(physical_vals).shift(UP * 1.05)
        inverse = numbered_row(inverse_vals, color=UNIFORM).shift(DOWN * 0.75)
        lab1 = tex("visible order after the physical riffle", size=22, color=MUTED).next_to(physical, UP, buff=0.16)
        lab2 = tex(r"positions of original cards $1,2,\ldots,8$", size=22, color=MUTED).next_to(inverse, DOWN, buff=0.16)
        inv_arrow = Arrow(physical.get_bottom(), inverse.get_top(), color=FAINT, buff=0.2)
        eq = math(r"d_{TV}(Q,U)=d_{TV}(Q^{-1},U)", size=35, color=UNIFORM).shift(DOWN * 2.05)
        self.say("Here is a subtlety worth making explicit. The visible output can have many ordinary descents. The elegant statistic appears on the inverse permutation: where did original card i end up?")
        self.play(FadeIn(physical), FadeIn(lab1), GrowArrow(inv_arrow), FadeIn(inverse), FadeIn(lab2))
        self.say("Permutation inversion is a bijection, and uniform measure is invariant under it. So we lose nothing by analyzing the inverse shuffle instead.")
        self.play(FadeIn(eq))


class C04InverseRiffleLab(DeckSlide):
    title = "Run the riffle backward: independent bits become a stable sort"
    kicker = "The inverse model turns a coupled interleaving into independent card labels"
    section = "Part 1 · discovering the classical riffle result"
    handout = False

    def body(self):
        values = list(range(1, 9))
        bits = [0, 1, 0, 1, 1, 0, 1, 1]
        order = model.stable_sort_cards(values, bits)
        assert order == [1, 3, 6, 2, 4, 5, 7, 8]

        cards = numbered_row(values).shift(UP * 1.3)
        labels = VGroup(*[
            mono(str(bit), size=19, color=LOCAL).next_to(cards[i], UP, buff=0.08)
            for i, bit in enumerate(bits)
        ])
        items = [VGroup(cards[i], labels[i]) for i in range(len(values))]

        self.say("Instead of choosing a cut and then a coupled interleaving, attach one independent fair bit to every original card. The bits are the random source.")
        self.play(FadeIn(cards))
        self.play(LaggedStart(*[FadeIn(label, shift=DOWN * 0.18) for label in labels], lag_ratio=0.10))

        target = numbered_row(order, color=UNIFORM).scale(0.92).shift(DOWN * 0.85)
        target_centers = [target[j].get_center() for j in range(len(order))]
        position = {card_id: j for j, card_id in enumerate(order)}
        zeros = [card_id for card_id in values if bits[card_id - 1] == 0]
        ones = [card_id for card_id in values if bits[card_id - 1] == 1]

        zero_lab = tex("bit 0", size=20, color=LOCAL).move_to(LEFT * 3.4 + DOWN * 1.72)
        one_lab = tex("bit 1", size=20, color=LOCAL).move_to(RIGHT * 2.0 + DOWN * 1.72)
        self.say("Stable-sort by the bit. First the zero cards move left, but their relative order must remain 1, 3, 6.")
        self.play(
            LaggedStart(*[
                move_item_to_card_center(items[card_id - 1], cards[card_id - 1], target_centers[position[card_id]])
                for card_id in zeros
            ], lag_ratio=0.18),
            FadeIn(zero_lab),
            run_time=1.15,
        )

        self.say("Then the one cards fill the remaining positions, again preserving their old relative order: 2, 4, 5, 7, 8. Nothing inside either bit class is shuffled.")
        self.play(
            LaggedStart(*[
                move_item_to_card_center(items[card_id - 1], cards[card_id - 1], target_centers[position[card_id]])
                for card_id in ones
            ], lag_ratio=0.13),
            FadeIn(one_lab),
            run_time=1.25,
        )

        zero_group = VGroup(*[items[card_id - 1] for card_id in zeros])
        one_group = VGroup(*[items[card_id - 1] for card_id in ones])
        zero_box = SurroundingRectangle(zero_group, color=LOCAL, buff=0.10, stroke_width=2)
        one_box = SurroundingRectangle(one_group, color=LOCAL, buff=0.10, stroke_width=2)
        result = math(r"[1,3,6]\;|\;[2,4,5,7,8]", size=29, color=UNIFORM).shift(DOWN * 2.25)
        self.say("This is the inverse of the forward riffle we just watched. The complicated-looking interleaving has become independent bits plus a deterministic stable sort.")
        self.play(Create(zero_box), Create(one_box), FadeIn(result))


class C04InverseBinaryLabels(DeckSlide):
    title = "The inverse riffle is startlingly simple: give every card one fair bit"
    kicker = "Stable-sort by the bit; equal-bit cards keep their original order"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        values = list(range(1, 9))
        bits = [0, 1, 0, 1, 1, 0, 1, 1]
        before = numbered_row(values).shift(UP * 1.2)
        bit_labels = bit_row(bits, before)
        order = [i for i, b in enumerate(bits) if b == 0] + [i for i, b in enumerate(bits) if b == 1]
        after_vals = [values[i] for i in order]
        after = numbered_row(after_vals, color=UNIFORM).shift(DOWN * 0.75)
        arrow = Arrow([0, 0.45, 0], [0, -0.2, 0], color=LOCAL, stroke_width=4)
        caption = tex("stable sort by bit", size=24, color=LOCAL).shift(DOWN * 0.02)
        prob = math(r"2^n\text{ bit strings, each with probability }2^{-n}", size=31).shift(DOWN * 2.05)
        self.say("The cancellation on the previous slide suggests the inverse construction. Assign independent fair bits to cards and stable-sort. This produces exactly the inverse GSR law.")
        self.play(FadeIn(before), FadeIn(bit_labels))
        self.say("The zero cards remain in original order, then the one cards remain in original order. The result is the inverse permutation from the physical example.")
        self.play(GrowArrow(arrow), FadeIn(caption), FadeIn(after))
        self.play(FadeIn(prob))


class C05RisingSequenceLab(DeckSlide):
    title = "Scan the inverse output: where can a descent come from?"
    kicker = "Inside one label class the order can only rise"
    section = "Part 1 · discovering the classical riffle result"
    handout = False

    def body(self):
        values = [1, 3, 6, 2, 4, 5, 7, 8]
        bits = [0, 0, 0, 1, 1, 1, 1, 1]
        row = numbered_row(values, color=UNIFORM, width=0.70, height=0.90).shift(UP * 0.55)
        labels = VGroup(*[
            mono(str(bit), size=18, color=LOCAL).next_to(row[i], UP, buff=0.08)
            for i, bit in enumerate(bits)
        ])
        self.say("Keep the stable-sort output on screen and inspect adjacent cards. The bit labels remember which source packet each card belongs to.")
        self.play(FadeIn(row), FadeIn(labels))

        relation_marks = VGroup()
        divider = None
        for i, (a, b) in enumerate(zip(values, values[1:])):
            x = (row[i].get_right()[0] + row[i + 1].get_left()[0]) / 2
            symbol = "<" if a < b else ">"
            color = UNIFORM if a < b else ERROR
            mark = tex(symbol, size=24, color=color).move_to([x, row.get_bottom()[1] - 0.32, 0])
            relation_marks.add(mark)
            self.play(Indicate(row[i], color=color), Indicate(row[i + 1], color=color), FadeIn(mark), run_time=0.34)
            if a > b:
                divider = Line(
                    [x, row.get_bottom()[1] - 0.55, 0],
                    [x, row.get_top()[1] + 0.42, 0],
                    color=ERROR,
                    stroke_width=4,
                )
                self.say("Here is the only descent: 6 > 2. Notice that it occurs exactly when the label changes from 0 to 1. Equal labels could never reverse two original cards because the sort is stable.")
                self.play(Create(divider), Indicate(labels[i], color=ERROR), Indicate(labels[i + 1], color=ERROR))

        left_run = VGroup(*row[:3])
        right_run = VGroup(*row[3:])
        brace1 = Brace(left_run, DOWN, color=LOCAL).shift(DOWN * 0.42)
        brace2 = Brace(right_run, DOWN, color=LOCAL).shift(DOWN * 0.42)
        run1 = tex("increasing run 1", size=19, color=LOCAL).next_to(brace1, DOWN, buff=0.07)
        run2 = tex("increasing run 2", size=19, color=LOCAL).next_to(brace2, DOWN, buff=0.07)
        self.say("The output therefore decomposes into maximal increasing runs. This is not an arbitrary statistic we impose afterward; it is the visible footprint of the stable-sort mechanics.")
        self.play(FadeIn(brace1), FadeIn(brace2), FadeIn(run1), FadeIn(run2))


class C05RisingSequences(DeckSlide):
    title = "What survives one riffle? Increasing runs"
    kicker = "A descent is exactly where a stable-sort label was forced to increase"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        values = [1, 3, 6, 2, 4, 5, 7, 8]
        row = numbered_row(values, color=UNIFORM, width=0.66, height=0.88).shift(UP * 0.55)
        dividers = rising_dividers(values, row)
        brace1 = Brace(VGroup(*row[:3]), DOWN, color=LOCAL)
        brace2 = Brace(VGroup(*row[3:]), DOWN, color=LOCAL)
        r1 = tex("rising sequence 1", size=20, color=LOCAL).next_to(brace1, DOWN, buff=0.08)
        r2 = tex("rising sequence 2", size=20, color=LOCAL).next_to(brace2, DOWN, buff=0.08)
        formula = math(r"r(\pi)=1+\#\{i:\pi_i>\pi_{i+1}\}", size=36).shift(DOWN * 1.65)
        self.say("Read the inverse permutation left to right. It rises until 6 > 2, then rises again. That gives two maximal increasing runs.")
        self.play(FadeIn(row), Create(dividers), FadeIn(brace1), FadeIn(brace2), FadeIn(r1), FadeIn(r2))
        self.say("This is the statistic Bayer and Diaconis call the number of rising sequences. Equivalently it is one plus the number of descents.")
        self.play(FadeIn(formula))


class C06OneRiffleAlreadyPredictsTheFormula(DeckSlide):
    title = "Before doing any algebra, solve one riffle completely"
    kicker = "Binary labels can support one run, two runs, or nothing more"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        rows = VGroup(
            boxed(para(r"$r=1$: labels may switch from 0 to 1 at any of $n+1$ boundaries $\Rightarrow (n+1)/2^n$.", 10.5, 27), UNIFORM),
            boxed(para(r"$r=2$: the unique descent forces the unique switch $0\to1$ $\Rightarrow 1/2^n$ for each such permutation.", 10.5, 27), LOCAL),
            boxed(para(r"$r\ge3$: two or more forced increases need at least three labels $\Rightarrow$ impossible after one riffle.", 10.5, 27), ERROR),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.3).shift(DOWN * 0.3)
        self.say("At this point the one-riffle law is almost obvious. An increasing permutation permits any binary cut point. A two-run permutation forces exactly one cut point. Three runs cannot fit into two labels.")
        self.play(LaggedStart(*[FadeIn(r, shift=RIGHT * 0.16) for r in rows], lag_ratio=0.22))
        self.say("The general theorem should now look like a counting problem: replace two labels by a labels and count the weakly increasing label sequences with forced strict steps.")


class C07CompositionLab(DeckSlide):
    title = "Two inverse riffles become one sort by a two-bit address"
    kicker = "The second stable sort preserves the first sort inside each new bit class"
    section = "Part 1 · discovering the classical riffle result"
    handout = False

    def body(self):
        values = list(range(1, 9))
        first_bits = [1, 0, 1, 1, 0, 0, 1, 0]
        second_bits = [0, 1, 0, 1, 1, 0, 0, 1]
        first_order = model.stable_sort_cards(values, first_bits)
        second_order = model.stable_sort_cards(first_order, second_bits)
        addresses = [2 * second_bits[i] + first_bits[i] for i in range(len(values))]
        one_sort_order = model.stable_sort_cards(values, addresses)
        assert first_order == [2, 5, 6, 8, 1, 3, 4, 7]
        assert second_order == [6, 1, 3, 7, 2, 5, 8, 4]
        assert second_order == one_sort_order

        cards = numbered_row(values).shift(UP * 1.45)
        labels = VGroup(*[
            mono(str(first_bits[i]), size=18, color=LOCAL).next_to(cards[i], UP, buff=0.07)
            for i in range(len(values))
        ])
        items = [VGroup(cards[i], labels[i]) for i in range(len(values))]
        self.say("Give every card its first fresh bit. Stable-sort by that bit exactly as before.")
        self.play(FadeIn(cards), LaggedStart(*[FadeIn(label, shift=DOWN * 0.12) for label in labels], lag_ratio=0.08))

        first_target = numbered_row(first_order).scale(0.82).shift(UP * 0.15)
        first_centers = [first_target[j].get_center() for j in range(len(values))]
        first_pos = {card_id: j for j, card_id in enumerate(first_order)}
        self.play(
            LaggedStart(*[
                move_item_to_card_center(items[card_id - 1], cards[card_id - 1], first_centers[first_pos[card_id]])
                for card_id in first_order
            ], lag_ratio=0.08),
            run_time=1.25,
        )

        first_caption = tex("after bit 1: stable inside 0-block, then stable inside 1-block", size=20, color=MUTED).shift(DOWN * 0.72)
        self.play(FadeIn(first_caption))
        self.say("Now attach a second independent bit. It is more significant because the new stable sort moves whole old-order subsequences without disturbing their internal order.")

        new_labels = []
        for card_id in values:
            word = f"{second_bits[card_id - 1]}{first_bits[card_id - 1]}"
            new_labels.append(mono(word, size=17, color=LOCAL).move_to(labels[card_id - 1]))
        self.play(*[Transform(labels[i], new_labels[i]) for i in range(len(values))], FadeOut(first_caption), run_time=0.65)

        second_target = numbered_row(second_order, color=UNIFORM).scale(0.82).shift(DOWN * 1.55)
        second_centers = [second_target[j].get_center() for j in range(len(values))]
        second_pos = {card_id: j for j, card_id in enumerate(second_order)}
        self.play(
            LaggedStart(*[
                move_item_to_card_center(items[card_id - 1], cards[card_id - 1], second_centers[second_pos[card_id]])
                for card_id in second_order
            ], lag_ratio=0.08),
            run_time=1.35,
        )

        final_addresses = [f"{second_bits[card_id - 1]}{first_bits[card_id - 1]}" for card_id in second_order]
        dividers = VGroup()
        group_labels = VGroup()
        start = 0
        for j in range(1, len(second_order) + 1):
            boundary = j == len(second_order) or final_addresses[j] != final_addresses[j - 1]
            if not boundary:
                continue
            subgroup = VGroup(*[items[second_order[t] - 1] for t in range(start, j)])
            group_labels.add(mono(final_addresses[start], size=18, color=LOCAL).next_to(subgroup, DOWN, buff=0.12))
            if j < len(second_order):
                x = (cards[second_order[j - 1] - 1].get_right()[0] + cards[second_order[j] - 1].get_left()[0]) / 2
                dividers.add(Line([x, -2.18, 0], [x, -0.92, 0], color=FAINT, stroke_width=2))
            start = j

        equation = colored_math(
            (r"\text{stable sort by }b_1", LOCAL),
            (r"\;\text{ then by }b_2", LOCAL),
            (r"\;=\;\text{one stable sort by }(b_2b_1)", UNIFORM),
            size=27,
        ).shift(DOWN * 2.45)
        self.say("Read the final two-bit addresses: 00, then 01, then 10, then 11. Two inverse riffles are exactly one stable sort by a uniform four-valued address. This is the mechanism behind a = 2^k.")
        self.play(Create(dividers), FadeIn(group_labels), FadeIn(equation))


class C07RepeatedRifflesBecomeOneAShuffle(DeckSlide):
    title = "Now repeat the inverse shuffle: bits concatenate into addresses"
    kicker = r"$k$ riffles $\Longleftrightarrow$ one $a$-shuffle with $a=2^k$ labels"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        one = VGroup(*[tex(s, size=30, color=LOCAL) for s in ["0", "1"]]).arrange(RIGHT, buff=0.9).shift(UP * 1.25)
        two = VGroup(*[tex(s, size=28, color=LOCAL) for s in ["00", "01", "10", "11"]]).arrange(RIGHT, buff=0.65).shift(UP * 0.1)
        three = VGroup(*[tex(s, size=23, color=LOCAL) for s in ["000", "001", "010", "011", "100", "101", "110", "111"]]).arrange(RIGHT, buff=0.24).shift(DOWN * 1.0)
        formula = colored_math((r"k\text{ bits/card}", LOCAL), (r"\quad\Longrightarrow\quad a=2^k", UNIFORM), size=38).shift(DOWN * 2.0)
        self.say("Each inverse riffle adds one fresh independent bit per card. Successive stable sorts are equivalent to one stable sort by the resulting k-bit word, with later rounds as more significant bits. Because every k-bit word is uniform, this is exactly a uniform label in {0,...,2^k-1}.")
        self.play(FadeIn(one))
        self.play(TransformFromCopy(one, two), FadeIn(two))
        self.play(TransformFromCopy(two, three), FadeIn(three), FadeIn(formula))
        self.say("So after k riffles we only need to solve one problem: assign each card a uniform label in {0,...,a-1}, then stable-sort, where a=2^k.")


class C08TargetPermutationBecomesInequalities(DeckSlide):
    title = "Fix a target permutation. Which labelings produce it?"
    kicker = "Weak inequalities everywhere; strict inequalities exactly at descents"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        values = [1, 3, 5, 2, 4]
        row = numbered_row(values, color=UNIFORM, width=0.78, height=0.95).shift(UP * 1.1)
        marks = rising_dividers(values, row)
        ineq = math(r"x_1\le x_3\le x_5\; <\; x_2\le x_4", size=42).shift(DOWN * 0.35)
        why = para(
            r"If two adjacent output cards have the same label, stable sorting must leave them in original order. "
            r"Therefore a reversed adjacent pair can only occur when the label actually increases.",
            10.7,
            27,
        ).shift(DOWN * 1.65)
        self.say("Take a concrete two-run target. Along its output order, labels have to be nondecreasing. At the descent 5 > 2, equality is forbidden: stable sorting would put 2 before 5.")
        self.play(FadeIn(row), Create(marks), FadeIn(ineq))
        self.say("Nothing else about the permutation matters to the label count. Only the locations of the forced strict steps matter, and ultimately only how many there are.")
        self.play(FadeIn(why))


class C09CountCompatibleLabels(DeckSlide):
    title = "Remove the forced strict steps and the count becomes stars-and-bars"
    kicker = r"If $r$ is the number of rising sequences, there are $\binom{a+n-r}{n}$ compatible labelings"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        top = math(r"0\le y_1\le\cdots\le y_n\le a-1", size=34).shift(UP * 1.15)
        strict = tex(r"with $r-1$ prescribed strict steps", size=24, color=ERROR).next_to(top, DOWN, buff=0.18)
        arrow = Arrow([0, 0.35, 0], [0, -0.25, 0], color=FAINT, stroke_width=3)
        transform = math(r"z_j=y_j-\#\{\text{forced steps before }j\}", size=31, color=LOCAL).shift(DOWN * 0.05)
        bottom = math(r"0\le z_1\le\cdots\le z_n\le a-r", size=34).shift(DOWN * 0.85)
        count = math(r"\#\text{labelings}=\binom{(a-r+1)+n-1}{n}=\binom{a+n-r}{n}", size=35, color=UNIFORM).shift(DOWN * 1.85)
        self.say("Subtract one from every label after the first forced strict step, two after the second, and so on. The strict inequalities disappear.")
        self.play(FadeIn(top), FadeIn(strict), GrowArrow(arrow), FadeIn(transform), FadeIn(bottom))
        self.say("Now we are choosing a multiset of n labels from a-r+1 values. Stars-and-bars gives the binomial coefficient. This is the whole probability formula hiding inside the riffle.")
        self.play(FadeIn(count))


class C10BayerDiaconisProbabilityFormula(DeckSlide):
    title = "Divide by all $a^n$ equally likely labelings"
    kicker = "The probability of a permutation depends only on its rising-sequence count"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        formula = math(r"Q_a(\pi)=\frac{1}{a^n}\binom{a+n-r(\pi)}{n}", size=50, color=UNIFORM).shift(UP * 0.55)
        zero = math(r"r(\pi)>a\quad\Longrightarrow\quad Q_a(\pi)=0", size=33, color=ERROR).shift(DOWN * 0.55)
        punch = para(
            r"We have compressed an entire permutation to one integer $r$.  Two wildly different deck orders with the same number of rising sequences have exactly the same GSR probability.",
            10.5,
            29,
        ).shift(DOWN * 1.65)
        self.say(f"This is the central exact formula. We got it with independent labels, stable sorting, and one stars-and-bars count.\n[Sources] {SOURCE_BD}")
        self.play(FadeIn(formula), FadeIn(zero))
        self.say("Notice the hard support constraint: an a-shuffle cannot create more than a rising sequences in the inverse permutation.")
        self.play(FadeIn(punch))


class C11SanityCheckOnFiveCards(DeckSlide):
    title = "Sanity check: the general formula remembers our one-riffle reasoning"
    kicker = r"Set $n=5$, $a=2$"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        head = VGroup(tex("rising runs", size=23, color=MUTED), tex("compatible labels", size=23, color=MUTED), tex("probability / permutation", size=23, color=MUTED)).arrange(RIGHT, buff=1.0).shift(UP * 1.35)
        rows = VGroup()
        data = [(1, r"\binom{6}{5}=6", r"6/32"), (2, r"\binom{5}{5}=1", r"1/32"), (3, r"\binom{4}{5}=0", "0")]
        for r, count, prob in data:
            row = VGroup(tex(str(r), size=28, color=FG), math(count, size=29, color=LOCAL), math(prob, size=29, color=UNIFORM)).arrange(RIGHT, buff=1.5)
            rows.add(row)
        rows.arrange(DOWN, buff=0.38).shift(DOWN * 0.05)
        note = tex(r"Exactly what we predicted before deriving the formula.", size=25, color=MUTED).shift(DOWN * 1.8)
        self.say("Always test a formula against the case we already understand. The identity has six binary cut points, every two-run permutation has one compatible bit assignment, and three runs are impossible.")
        self.play(FadeIn(head), LaggedStart(*[FadeIn(r, shift=RIGHT * 0.15) for r in rows], lag_ratio=0.2), FadeIn(note))


class C12EulerianNumbers(DeckSlide):
    title = "One obstacle remains: how many permutations have each number of descents?"
    kicker = "Those class sizes are the Eulerian numbers"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        tri = VGroup(
            tex(r"$n=1:\quad 1$", size=26),
            tex(r"$n=2:\quad 1\quad1$", size=26),
            tex(r"$n=3:\quad 1\quad4\quad1$", size=26),
            tex(r"$n=4:\quad 1\quad11\quad11\quad1$", size=26),
            tex(r"$n=5:\quad 1\quad26\quad66\quad26\quad1$", size=26),
        ).arrange(DOWN, aligned_edge=LEFT, buff=0.18).shift(LEFT * 3.4 + DOWN * 0.15)
        rec = math(r"A(n,d)=(n-d)A(n-1,d-1)+(d+1)A(n-1,d)", size=32).shift(RIGHT * 2.1 + UP * 0.65)
        story = para(
            r"Insert the new largest card $n$ into a permutation of $n-1$.  Some insertion slots create a new descent; the others preserve the old count.  Counting those slots gives the recurrence.",
            5.5,
            25,
        ).shift(RIGHT * 2.5 + DOWN * 0.65)
        total = math(r"\sum_{d=0}^{n-1}A(n,d)=n!", size=31, color=UNIFORM).shift(RIGHT * 2.35 + DOWN * 2.0)
        self.say("We do not enumerate permutations. We count them by descent class. The Eulerian recurrence can itself be discovered by inserting the new largest element into all possible slots.")
        self.play(FadeIn(tri), FadeIn(rec), FadeIn(story), FadeIn(total))


class C12EulerianInsertionRecurrence(DeckSlide):
    title = "We can discover the Eulerian recurrence by inserting the new largest card"
    kicker = "The coefficients are just counts of insertion slots"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        base_vals = [3, 1, 4, 2]
        base = numbered_row(base_vals, color=LOCAL, width=0.75, height=0.9).shift(UP * 1.05 + LEFT * 2.85)
        marks = rising_dividers(base_vals, base)
        base_lab = tex(r"a permutation of $n-1$ with $d$ descents", size=23, color=MUTED).next_to(base, UP, buff=0.18)

        preserve = boxed(
            para(r"Insert $n$ after one of the $d$ existing descents, or at the end.  The old descent is replaced by $\cdots<n>\cdots$, so the total stays $d$.  Number of slots: $d+1$.", 5.15, 24),
            UNIFORM,
            0.25,
        ).shift(RIGHT * 3.25 + UP * 0.85)
        create = boxed(
            para(r"In every other slot, $n$ is followed by a smaller card and creates one new descent.  Starting from $d-1$ descents, the number of such slots is $n-d$.", 5.15, 24),
            ERROR,
            0.25,
        ).shift(RIGHT * 3.25 + DOWN * 0.8)
        recurrence = math(
            r"A(n,d)=(n-d)A(n-1,d-1)+(d+1)A(n-1,d)",
            size=33,
            color=FG,
        ).shift(DOWN * 2.15)
        self.say("The recurrence is not a mysterious identity. Take a permutation of n minus one and ask where the new largest element n can be inserted.")
        self.play(FadeIn(base), Create(marks), FadeIn(base_lab))
        self.say("If the old permutation already has d descents, inserting after a descent or at the end preserves the number. There are d plus one such slots. Every other slot creates a new descent; when we start from d minus one descents there are n minus d such slots.")
        self.play(FadeIn(preserve), FadeIn(create), FadeIn(recurrence))


class C13FiftyTwoFactorialCollapsesTo52Terms(DeckSlide):
    title = "$52!$ states collapse to 52 exact terms"
    kicker = "Because both GSR probability and the uniform probability are constant inside each rising-sequence class"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        huge = tex(r"$52!\approx 8.07\times10^{67}$ permutations", size=36, color=ERROR).shift(UP * 1.3)
        arrow = Arrow([0, 0.75, 0], [0, 0.1, 0], color=FAINT, stroke_width=4)
        bins = VGroup(*[Rectangle(width=0.13, height=0.55, stroke_color=LOCAL, stroke_width=1, fill_color=LOCAL, fill_opacity=0.25) for _ in range(52)]).arrange(RIGHT, buff=0.025).shift(DOWN * 0.25)
        label = tex("52 rising-sequence classes", size=26, color=LOCAL).next_to(bins, DOWN, buff=0.18)
        formula = math(
            r"d_{TV}(Q_a,U)=\frac12\sum_{r=1}^{n}A(n,r-1)\left|\frac{\binom{a+n-r}{n}}{a^n}-\frac1{n!}\right|",
            size=31,
            color=UNIFORM,
        ).shift(DOWN * 1.65)
        self.say("This is the computational miracle. Total variation nominally sums over every permutation, but the likelihood is constant on each descent class.")
        self.play(FadeIn(huge), GrowArrow(arrow), FadeIn(bins), FadeIn(label))
        self.say("Multiply the per-permutation discrepancy by the Eulerian class size. The exact distance is now a sum of only n terms. No Monte Carlo and certainly no enumeration of 52! orders.")
        self.play(FadeIn(formula))


class C14UniformMomentsFromIndicators(DeckSlide):
    title = "We can predict the center and width of the uniform curve without computing Eulerian numbers"
    kicker = "Descents are local indicator variables"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        definitions = math(
            r"D_i=\mathbf 1\{\pi_i>\pi_{i+1}\},\qquad R=1+\sum_{i=1}^{n-1}D_i",
            size=34,
        ).shift(UP * 1.35)
        mean = colored_math(
            (r"\Pr(D_i=1)=\tfrac12", LOCAL),
            (r"\quad\Longrightarrow\quad \mathbb E[R]=\frac{n+1}{2}", UNIFORM),
            size=32,
        ).shift(UP * 0.35)
        covariance = math(
            r"\Pr(D_i=D_{i+1}=1)=\frac16\quad\Longrightarrow\quad"
            r"\operatorname{Cov}(D_i,D_{i+1})=\frac16-\frac14=-\frac1{12}",
            size=29,
            color=LOCAL,
        ).shift(DOWN * 0.65)
        variance = colored_math(
            (r"\operatorname{Var}(R)=\frac{n-1}{4}+2(n-2)\!\left(-\frac1{12}\right)", FG),
            (r"=\frac{n+1}{12}", UNIFORM),
            size=31,
        ).shift(DOWN * 1.55)
        fiftytwo = math(r"n=52:\qquad \mathbb E[R]=26.5,\qquad \operatorname{sd}(R)=\sqrt{53/12}\approx2.10", size=29, color=UNIFORM).shift(DOWN * 2.25)
        self.say("Before plotting the uniform Eulerian distribution, derive its location. A descent at any fixed adjacent position has probability one half, so the mean run count is immediate.")
        self.play(FadeIn(definitions), FadeIn(mean))
        self.say("For the variance, nonadjacent descent indicators are independent. Adjacent descents both occur exactly when three neighboring values are in decreasing order, one of six relative orders. That gives covariance minus one twelfth.")
        self.play(FadeIn(covariance), FadeIn(variance), FadeIn(fiftytwo))


class C14WhatUniformLooksLikeInRisingSequences(DeckSlide):
    title = "What does a truly uniform 52-card permutation look like in this statistic?"
    kicker = "About 26.5 rising sequences, with fluctuations of only about 2.1"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        rs = list(range(1, 53))
        probs = [float(model.uniform_rising_mass(52, r)) for r in rs]
        axes = Axes(x_range=[14, 39, 4], y_range=[0, 0.21, 0.05], x_length=9.4, y_length=4.25, tips=False, axis_config={"color": MUTED}).shift(DOWN * 0.35)
        bars = probability_bars(axes, rs, probs, UNIFORM, opacity=0.75, width=0.14)
        center = DashedLine(axes.c2p(26.5, 0), axes.c2p(26.5, 0.205), color=UNIFORM, stroke_width=2)
        mean = math(r"\mathbb E[R]=\frac{n+1}{2}=26.5", size=27, color=UNIFORM).move_to([4.25, 1.8, 0])
        sd = math(r"\mathrm{sd}(R)=\sqrt{\frac{n+1}{12}}\approx2.10", size=27, color=UNIFORM).next_to(mean, DOWN, aligned_edge=LEFT, buff=0.18)
        xlab = tex("number of rising sequences $R$", size=21, color=MUTED).next_to(axes.x_axis, DOWN, buff=0.17)
        self.say("Under a uniform random permutation, descents are concentrated. The exact Eulerian distribution is centered at R=(n+1)/2. For 52 cards that is 26.5, with standard deviation about 2.1.")
        self.play(Create(axes), FadeIn(bars), Create(center), FadeIn(mean), FadeIn(sd), FadeIn(xlab))
        self.say("So an observer does not need to understand all 52! orders. If riffles systematically produce too few rising sequences, that signal will be easy to detect.")


class C15WatchTheRiffleDistributionApproachUniform(DeckSlide):
    title = "Watch the only relevant distribution move toward equilibrium"
    kicker = "Do not stack four curves; morph the exact law one riffle at a time"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        rs = list(range(14, 40))
        axes = Axes(
            x_range=[14, 39, 4],
            y_range=[0, 0.24, 0.05],
            x_length=9.4,
            y_length=4.25,
            tips=False,
            axis_config={"color": MUTED},
        ).shift(DOWN * 0.35)
        u = [float(model.uniform_rising_mass(52, r)) for r in rs]
        uniform = polyline(axes, rs, u, UNIFORM, width=4, opacity=0.75)
        xlab = tex("number of rising sequences $R$", size=20, color=MUTED).next_to(axes.x_axis, DOWN, buff=0.14)
        uniform_lab = tex("uniform target", size=20, color=UNIFORM).move_to([4.4, 1.85, 0])

        k = 5
        vals = [float(model.gsr_rising_mass(52, k, r)) for r in rs]
        current = polyline(axes, rs, vals, LOCAL, width=5)
        label = math(rf"k={k},\qquad d_{{TV}}={float(model.gsr_tv(52, k)):.3f}", size=28, color=LOCAL).move_to([-3.85, 1.85, 0])

        self.say("The relevant state is no longer a deck picture. It is the exact distribution of the sufficient statistic R. Start after five riffles: the law is strongly left-shifted relative to uniform.")
        self.play(Create(axes), FadeIn(xlab), Create(uniform), FadeIn(uniform_lab), Create(current), FadeIn(label))

        for k in (6, 7, 8):
            next_vals = [float(model.gsr_rising_mass(52, k, r)) for r in rs]
            next_curve = polyline(axes, rs, next_vals, LOCAL, width=5)
            next_label = math(rf"k={k},\qquad d_{{TV}}={float(model.gsr_tv(52, k)):.3f}", size=28, color=LOCAL).move_to(label)
            self.say(f"Apply one more ideal riffle. The exact run-count law morphs to k={k}; the total-variation distance is now {float(model.gsr_tv(52, k)):.3f}.")
            self.play(Transform(current, next_curve), Transform(label, next_label), run_time=1.1)
            if k == 7:
                threshold = 25
                marker = DashedLine(axes.c2p(threshold, 0), axes.c2p(threshold, 0.225), color=ERROR, stroke_width=2)
                marker_lab = tex(r"$R=25$", size=19, color=ERROR).next_to(marker, UP, buff=0.05)
                self.play(Create(marker), FadeIn(marker_lab))
                self.say("At seven riffles we are in the cutoff window, not at uniformity. The next scenes will explain why the discrepancy is concentrated on the low-R side of this threshold.")
                self.play(FadeOut(marker), FadeOut(marker_lab))


class C16LikelihoodRatioIsMonotone(DeckSlide):
    title = "Which deck orders are still overrepresented after seven riffles?"
    kicker = "The likelihood ratio falls monotonically with the number of rising sequences"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        lr = math(
            r"L_a(r)=\frac{Q_a(\pi)}{U(\pi)}=n!\,\frac{\binom{a+n-r}{n}}{a^n}",
            size=35,
        ).shift(UP * 1.25)
        ratio = colored_math(
            (r"\frac{L_a(r+1)}{L_a(r)}", FG),
            (r"=\frac{a-r}{a+n-r}", LOCAL),
            (r"<1", ERROR),
            size=39,
        ).shift(UP * 0.15)
        cross = VGroup(
            boxed(math(r"L_{128}(25)\approx1.287", size=28, color=LOCAL), LOCAL, 0.22),
            boxed(math(r"L_{128}(26)\approx0.855", size=28, color=UNIFORM), UNIFORM, 0.22),
        ).arrange(RIGHT, buff=0.55).shift(DOWN * 1.0)
        event = math(r"Q_a(\pi)\ge U(\pi)\quad\Longleftrightarrow\quad R(\pi)\le25\qquad(n=52,a=128)", size=31, color=ERROR).shift(DOWN * 2.05)
        self.say("Now ask where the shuffled law exceeds uniform. The exact probability formula gives a likelihood ratio depending only on r. Take the ratio of consecutive r values: almost everything cancels.")
        self.play(FadeIn(lr), FadeIn(ratio))
        self.say("The result is strictly less than one, so the likelihood ratio crosses one exactly once. For seven riffles on 52 cards it is above one at 25 runs and below one at 26. Therefore the whole positive discrepancy is the event R at most 25.")
        self.play(FadeIn(cross), FadeIn(event))


class C16TotalVariationBecomesAGuessingGame(DeckSlide):
    title = "Total variation asks for the best possible distinguishing event"
    kicker = "At seven riffles, the optimal test is essentially: 'are there at most 25 rising sequences?'"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        threshold, q, u, gap = model.gsr_optimal_rising_event(52, 7)
        definition = math(r"d_{TV}(Q,U)=\max_A |Q(A)-U(A)|", size=39).shift(UP * 1.25)
        event = boxed(math(rf"A=\{{R\le {threshold}\}}", size=37, color=ERROR), ERROR, 0.28).shift(LEFT * 3.5 + DOWN * 0.15)
        qbox = boxed(math(rf"Q_{{128}}(A)={float(q):.3f}", size=31, color=LOCAL), LOCAL, 0.24).shift(RIGHT * 1.0 + UP * 0.15)
        ubox = boxed(math(rf"U(A)={float(u):.3f}", size=31, color=UNIFORM), UNIFORM, 0.24).next_to(qbox, DOWN, aligned_edge=LEFT, buff=0.25)
        diff = math(rf"{float(q):.3f}-{float(u):.3f}={float(gap):.3f}", size=39, color=ERROR).shift(RIGHT * 2.85 + DOWN * 1.55)
        success = math(r"\Pr(\text{best classifier correct})=\frac{1+d_{TV}}2\approx0.667", size=29).shift(DOWN * 2.15)
        self.say("Total variation has an operational meaning: choose the event whose probability differs most between the shuffled and uniform laws. Because the GSR likelihood ratio decreases with R, the optimal event is a threshold in the rising-sequence count.")
        self.play(FadeIn(definition), FadeIn(event), FadeIn(qbox), FadeIn(ubox))
        self.say("After seven riffles, R<=25 happens about 65.0 percent of the time, versus 31.6 percent under uniform. Their difference is exactly the total variation distance, about 0.334.")
        self.play(FadeIn(diff), FadeIn(success))


class C17TheExact52CardTable(DeckSlide):
    title = "Now the famous table is no longer mysterious"
    kicker = "Each row is just the 52-term Eulerian sum with $a=2^k$"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        ks = list(range(4, 11))
        vals = [float(model.gsr_tv(52, k)) for k in ks]
        headers = VGroup(tex("riffles $k$", size=22, color=MUTED), tex("labels $a=2^k$", size=22, color=MUTED), tex(r"$d_{TV}$", size=22, color=MUTED)).arrange(RIGHT, buff=1.0).shift(UP * 1.7)
        rows = VGroup()
        for k, val in zip(ks, vals):
            color = ERROR if k == 7 else FG
            row = VGroup(tex(str(k), size=27, color=color), tex(str(2**k), size=27, color=color), tex(f"{val:.3f}", size=27, color=color)).arrange(RIGHT, buff=1.75)
            if k == 7:
                row.add(SurroundingRectangle(row, color=ERROR, buff=0.12, stroke_width=2))
            rows.add(row)
        rows.arrange(DOWN, buff=0.16).shift(DOWN * 0.15)
        note = tex(r"$5:\ .924\qquad6:\ .614\qquad\mathbf{7:\ .334}\qquad8:\ .167\qquad9:\ .085\qquad10:\ .043$", size=24, color=MUTED).shift(DOWN * 2.45)
        self.say(f"This is Table 1 in mathematical form. The distance is essentially one through four riffles, then drops abruptly: 0.924, 0.614, 0.334, 0.167, 0.085, 0.043.\n[Sources] {SOURCE_BD}")
        self.play(FadeIn(headers), LaggedStart(*[FadeIn(r) for r in rows], lag_ratio=0.08), FadeIn(note))


class C18DiscoverTheThreeHalvesScale(DeckSlide):
    title = r"We can even guess the $\tfrac32\log_2 n$ cutoff scale from the exact formula"
    kicker = "Ask when the likelihood ratio becomes nearly flat over a typical uniform fluctuation"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        lr = math(
            r"L_a(r)=\frac{Q_a(\pi)}{U(\pi)}=\frac{n!\binom{a+n-r}{n}}{a^n}"
            r"=\prod_{j=0}^{n-1}\left(1+\frac{n-r-j}{a}\right)",
            size=30,
        ).shift(UP * 1.45)
        expansion = math(
            r"\log L_a(r)\approx\frac{n\left(\frac{n+1}{2}-r\right)}{a}+O\!\left(\frac{n^3}{a^2}\right)",
            size=33,
            color=LOCAL,
        ).shift(UP * 0.25)
        typical = math(r"R=\frac{n+1}{2}+O(\sqrt n)\quad\text{under }U", size=33, color=UNIFORM).shift(DOWN * 0.75)
        scale = colored_math((r"\log L=O(n^{3/2}/a)", ERROR), (r"\quad\Rightarrow\quad a\asymp n^{3/2}", UNIFORM), (r"\quad\Rightarrow\quad k\asymp\frac32\log_2 n", LOCAL), size=34).shift(DOWN * 1.8)
        self.say("Here is the discovery heuristic for the asymptotic scale. Divide the exact GSR probability by 1/n! and expand the logarithm when a is large.")
        self.play(FadeIn(lr), FadeIn(expansion))
        self.say("A uniform permutation fluctuates in its rising-sequence count by order square-root n. Across that typical window the first-order log likelihood varies by order n^(3/2)/a; the quadratic remainder has the same transition scale.")
        self.play(FadeIn(typical), FadeIn(scale))
        self.say(f"Therefore a=2^k has to reach the n^(3/2) scale, giving k about (3/2) log_2 n. Bayer--Diaconis makes this heuristic sharp and proves the cutoff profile.\n[Sources] {SOURCE_BD}")


class C19WhatSevenActuallyMeans(DeckSlide):
    title = "So what does 'seven shuffles' actually mean?"
    kicker = "A landmark in a sharp transition, not an equality with uniform randomness"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        seven = boxed(para(r"After 7 ideal GSR riffles on 52 distinct cards: $d_{TV}\approx0.334$.", 5.5, 29), ERROR, 0.3).shift(LEFT * 3.1 + UP * 0.45)
        more = boxed(para(r"If your explicit target is $d_{TV}<0.1$, the same exact table says 9 riffles; for $<0.05$, it says 10.", 5.5, 27), UNIFORM, 0.3).shift(RIGHT * 3.1 + UP * 0.45)
        lesson = para(
            r"The enduring result is not the numeral 7.  It is the chain of ideas that turns a physical shuffle into an exact probability law, identifies a sufficient statistic, and computes a rigorous distance to uniformity.",
            10.8,
            30,
        ).shift(DOWN * 1.35)
        self.say("The popular slogan is useful, but it can obscure the theorem. Seven is inside the cutoff window and leaves substantial measurable nonuniformity. The right number depends on the distance metric and the error tolerance.")
        self.play(FadeIn(seven), FadeIn(more), FadeIn(lesson))
        self.say("This is exactly the perspective we need for shufflemath: preserve the derivation, then replace whole-deck ideal riffles by working-set operations and optimize against an explicit epsilon rather than inheriting a magic number.")


class C20ClassicalRoadmap(DeckSlide):
    title = "The classical theorem now gives us a concrete formalization ladder"
    kicker = "Each box has a mathematical purpose, not merely a file name"
    section = "Part 1 · discovering the classical riffle result"

    def body(self):
        labels = [
            ("physical GSR", "cut + interleave"),
            ("inverse law", "independent labels"),
            ("composition", r"$2^k$-shuffle"),
            ("likelihood", "rising sequences"),
            ("class sizes", "Eulerian numbers"),
            ("distance", "exact TV sum"),
            ("asymptotics", r"$\frac32\log_2 n$ cutoff"),
        ]
        boxes = VGroup()
        for top, bottom in labels:
            box = boxed(VGroup(tex(top, size=22, color=LOCAL), tex(bottom, size=18, color=MUTED)).arrange(DOWN, buff=0.08), LOCAL, 0.2)
            boxes.add(box)
        top_row = VGroup(*boxes[:4]).arrange(RIGHT, buff=0.28).shift(UP * 0.65)
        bottom_row = VGroup(*boxes[4:]).arrange(RIGHT, buff=0.48).shift(DOWN * 1.0)
        arrows = VGroup(
            *[Arrow(boxes[i].get_right(), boxes[i + 1].get_left(), color=FAINT, buff=0.08, stroke_width=2) for i in range(3)],
            *[Arrow(boxes[i].get_right(), boxes[i + 1].get_left(), color=FAINT, buff=0.08, stroke_width=2) for i in range(4, 6)],
        )
        bridge = Arrow(boxes[3].get_bottom(), boxes[4].get_top(), color=FAINT, buff=0.1, stroke_width=2)
        self.say("This is the roadmap I want the audience to carry forward. The result is a composition of reusable ideas: physical model, inverse representation, combinatorial statistic, exact finite count, distance, then asymptotics.")
        self.play(LaggedStart(*[FadeIn(b) for b in top_row], lag_ratio=0.12), FadeIn(arrows), GrowArrow(bridge), LaggedStart(*[FadeIn(b) for b in bottom_row], lag_ratio=0.12))
        self.say("Only after this foundation is genuinely understood should the talk move to large-deck working sets, Bernoulli--Laplace exchange, imperfect local shuffles, and cost-optimal protocols.")
