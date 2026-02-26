/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
  -/

import Mathlib

-- BEGIN AUTO-IMPORTS (managed by orchestrator)
import Books.Analysis2_Tao_2022.Chapters.Chap04.section01
import Books.Analysis2_Tao_2022.Chapters.Chap04.section02
import Books.Analysis2_Tao_2022.Chapters.Chap04.section03
import Books.Analysis2_Tao_2022.Chapters.Chap04.section04
import Books.Analysis2_Tao_2022.Chapters.Chap04.section05
import Books.Analysis2_Tao_2022.Chapters.Chap04.section06
import Books.Analysis2_Tao_2022.Chapters.Chap04.section07
-- END AUTO-IMPORTS

/-!
Chapter 04

Title: Chapter 04 -- Power Series

Verso links:
- [Local Verso: Chapter overview](/ReasBook/books/analysis2_tao_2022/chapters/chap04/)
- [Local Verso: Book overview](/ReasBook/books/analysis2_tao_2022/book/)
- [Published Verso: Chapter overview](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap04/)
- [Published Verso: Book overview](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/book/)

Section overviews:

- [4.1 Formal Power Series file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap04/section01.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap04/section01/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap04/section01/))
- [4.2 Real Analytic Functions file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap04/section02.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap04/section02/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap04/section02/))
- [4.3 Abel's Theorem file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap04/section03.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap04/section03/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap04/section03/))
- [4.4 Multiplication of Power Series file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap04/section04.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap04/section04/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap04/section04/))
- [4.5 The Exponential and Logarithm Functions file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap04/section05.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap04/section05/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap04/section05/))
- [4.6 A Digression on Complex Numbers file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap04/section06.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap04/section06/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap04/section06/))
- [4.7 Trigonometric Functions file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap04/section07.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap04/section07/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap04/section07/))

-/

/-!
# Books.Analysis2_Tao_2022: Chap04

Auto-managed imports live below.
-/
