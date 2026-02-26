/-
  Copyright (c) 2026 Zichen Wang. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Zichen Wang, Wanli Ma, Zaiwen Wen
  -/

import Mathlib

-- BEGIN AUTO-IMPORTS (managed by orchestrator)
import Books.Analysis2_Tao_2022.Chapters.Chap03.section01
import Books.Analysis2_Tao_2022.Chapters.Chap03.section02
import Books.Analysis2_Tao_2022.Chapters.Chap03.section03
import Books.Analysis2_Tao_2022.Chapters.Chap03.section04
import Books.Analysis2_Tao_2022.Chapters.Chap03.section05
import Books.Analysis2_Tao_2022.Chapters.Chap03.section06
import Books.Analysis2_Tao_2022.Chapters.Chap03.section07
import Books.Analysis2_Tao_2022.Chapters.Chap03.section08
-- END AUTO-IMPORTS

/-!
Chapter 03

Title: Chapter 03 -- Uniform Convergence

Verso links:
- [Local Verso: Chapter overview](/ReasBook/books/analysis2_tao_2022/chapters/chap03/)
- [Local Verso: Book overview](/ReasBook/books/analysis2_tao_2022/book/)
- [Published Verso: Chapter overview](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap03/)
- [Published Verso: Book overview](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/book/)

Section overviews:

- [3.1 Limiting Values of Functions file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap03/section01.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap03/section01/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap03/section01/))
- [3.2 Pointwise and Uniform Convergence file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap03/section02.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap03/section02/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap03/section02/))
- [3.3 Uniform Convergence and Continuity file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap03/section03.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap03/section03/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap03/section03/))
- [3.4 The Metric of Uniform Convergence file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap03/section04.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap03/section04/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap03/section04/))
- [3.5 Series of Functions; the Weierstrass M-Test file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap03/section05.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap03/section05/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap03/section05/))
- [3.6 Uniform Convergence and Integration file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap03/section06.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap03/section06/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap03/section06/))
- [3.7 Uniform Convergence and Derivatives file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap03/section07.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap03/section07/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap03/section07/))
- [3.8 Uniform Approximation by Polynomials file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap03/section08.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap03/section08/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap03/section08/))

-/

/-!
# Books.Analysis2_Tao_2022: Chap03

Auto-managed imports live below.
-/
