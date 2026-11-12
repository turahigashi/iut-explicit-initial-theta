/-
  ★★★★★★★★★★繋ぎ③ — 当方の §8-1「N1 は不要」判定は【誤り】だった
  ────────────────────────────────────────────────────────────────────────
  ★経緯：外部監査（2026-08-31）を受けて既存資産を棚卸ししたところ、
    ★★当方の判定に【反する定理が既にリポジトリにあった】ことが分かった。

  ── 当方が書いていたこと（`MISSING_LIST.md` 第2版 §1・論文 §8-1）──

    「争点は『$\Phi$ は充満か』＝『構成が $\alpha$ を担ぐか』に落ちていた。
      ★[IUTchI] 定義5.2 を実物で読むと、★★素帯の定義そのものが $\alpha$ を担ぐ。
      ⇒ ★★★Hodge 劇場を形式化しなくても、【定義の水準で決まっている】。
      ⇒ N1（Hodge 劇場・約340頁）は【不要】。」

  ── ★★★既存資産が示していたこと ──

    `M3/thetalink/FVdashPrimeStripSkeleton.lean` の
    ★`source_shape_and_squares_do_not_exclude_closed_unit`：

      ★★【退化した場合】（すべてが `ZMod 1` の閉じた単位）が
        ・`PrimeLabelSquare`（素点ラベルの可換性）を満たし
        ・`RhoNaturalitySquare`（$\rho$ の自然性）を満たし
        ・しかし `FVdashIsoNondegenerate` を【満たさない】

    ⇒ ★★★★【定義5.2 の形＋二つの可換正方形だけでは、自明な場合を排除できない】。

  ── ★★★★★したがって当方の判定は誤り ──

    ★「形が決まれば決着する」は成り立たない。
    ★★決着には【非退化性】が要り、それを供給するのは
      ★★★【実際の構成】＝[IUTchI] §4–§6（Hodge 劇場）である。
    ⇒ ★★★★N1 は「争点の型を書くのに」不要だっただけで、
      ★★★★★【対象の同定をするのに】は不要ではなかった。

  ── 本ファイルが記録すること ──

    ① ★形＋可換性は退化を排除しない（既存定理の再掲）
    ② ★★素点ラベルの可換性と $\rho$ の自然性は【互いに独立】（既存定理の再掲）
       ⇒ 二つ揃えても足りないことの補強
    ③ ★★★したがって非退化性は【追加の入力】であり、
       それは定義からは出ない

  検証: error 0 / sorryAx 0 / ★独自 axiom 0
-/
import M3.thetalink.FVdashPrimeStripSkeleton

namespace Grounding.Bridge.ShapeDoesNotDecide

open Grounding.ThetaLink

/-! ## 1. ★形＋可換性は退化を排除しない -/

/-- ★★★★★★★★① 既存定理の再掲。
    ★退化した場合が【形も可換性も満たす】が【非退化でない】。
    ⇒ ★★「定義5.2 の形で決まっている」は成り立たない。 -/
theorem shape_admits_degenerate :
    PrimeLabelSquare closedFVdashIso
    ∧ RhoNaturalitySquare closedFVdashIso
    ∧ ¬ FVdashIsoNondegenerate closedFVdashIso :=
  source_shape_and_squares_do_not_exclude_closed_unit

/-! ## 2. ★★二つの可換性は互いに独立 -/

/-- ★★★★★★② 既存定理の再掲。素点ラベルの可換性と $\rho$ の自然性は
    ★片方が成り立ってももう片方は落ちうる。
    ⇒ ★★二つ揃えることも「自動」ではない。 -/
theorem two_squares_are_independent :
    (RhoNaturalitySquare toyWrongPrimeFVdashIso
      ∧ FVdashIsoNondegenerate toyWrongPrimeFVdashIso
      ∧ ¬ PrimeLabelSquare toyWrongPrimeFVdashIso)
    ∧ (PrimeLabelSquare toyWrongRhoFVdashIso
      ∧ FVdashIsoNondegenerate toyWrongRhoFVdashIso
      ∧ ¬ RhoNaturalitySquare toyWrongRhoFVdashIso) :=
  prime_and_rho_compatibility_are_independent

/-! ## 3. ★★★非退化性は追加の入力である -/

/-- ★★★★★★★★★★③ 帰結。
    ★形と可換性を全部満たしても非退化とは限らない（`shape_admits_degenerate`）ので、
    ★★【非退化性は定義から出ない追加の入力】である。
    ⇒ ★★★それを供給するのが実際の構成＝Hodge 劇場（[IUTchI] §4–§6）であり、
      ★★★★当方の「N1 は不要」という判定は【誤りだった】。 -/
theorem nondegeneracy_is_an_extra_input :
    ∃ _ : Unit,
      (PrimeLabelSquare closedFVdashIso ∧ RhoNaturalitySquare closedFVdashIso)
      ∧ ¬ FVdashIsoNondegenerate closedFVdashIso :=
  ⟨(), ⟨shape_admits_degenerate.1, shape_admits_degenerate.2.1⟩,
   shape_admits_degenerate.2.2⟩

/-! ## 4. まとめ -/

/-- ★★★★★★★★★★★本ファイルの到達点。

    ★★★★★★当方の自己訂正である。

    ① ★`MISSING_LIST.md` 第2版と論文 §8-1 は
       「定義5.2 の形で決まっているので N1（Hodge 劇場）は不要」と判定した。
    ② ★★しかし既存資産 `FVdashPrimeStripSkeleton.lean` は、
       ★【形＋二つの可換正方形が退化した場合を排除しない】ことを
       既に証明していた（`source_shape_and_squares_do_not_exclude_closed_unit`）。
    ③ ★★★さらに二つの可換性は【互いに独立】であり、
       揃えることも自動ではない。
    ④ ★★★★したがって決着には【非退化性】という追加の入力が要り、
       それは定義からは出ない。

    ⇒ ★★★★★【「N1 は不要」は誤りだった】。
      ★正しくは「N1 は<u>争点の型を書くのに</u>不要だった」だけであり、
      ★★<u>対象の同定をするのに</u>は依然として必要である。

    ★★★★★★教訓：★【自分のリポジトリの中に反証が既にあった】。
      外部監査に指摘されるまで棚卸しをしていなかった。 -/
theorem summary :
    (PrimeLabelSquare closedFVdashIso
      ∧ RhoNaturalitySquare closedFVdashIso
      ∧ ¬ FVdashIsoNondegenerate closedFVdashIso)
    ∧ ((RhoNaturalitySquare toyWrongPrimeFVdashIso
          ∧ ¬ PrimeLabelSquare toyWrongPrimeFVdashIso)
        ∧ (PrimeLabelSquare toyWrongRhoFVdashIso
          ∧ ¬ RhoNaturalitySquare toyWrongRhoFVdashIso)) :=
  ⟨shape_admits_degenerate,
   ⟨⟨two_squares_are_independent.1.1, two_squares_are_independent.1.2.2⟩,
    ⟨two_squares_are_independent.2.1, two_squares_are_independent.2.2.2⟩⟩⟩

end Grounding.Bridge.ShapeDoesNotDecide
