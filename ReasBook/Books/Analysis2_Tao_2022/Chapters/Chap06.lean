import Mathlib

-- BEGIN AUTO-IMPORTS (managed by orchestrator)
import Books.Analysis2_Tao_2022.Chapters.Chap06.section01
import Books.Analysis2_Tao_2022.Chapters.Chap06.section02
import Books.Analysis2_Tao_2022.Chapters.Chap06.section03
import Books.Analysis2_Tao_2022.Chapters.Chap06.section04
import Books.Analysis2_Tao_2022.Chapters.Chap06.section05
import Books.Analysis2_Tao_2022.Chapters.Chap06.section06
import Books.Analysis2_Tao_2022.Chapters.Chap06.section07
import Books.Analysis2_Tao_2022.Chapters.Chap06.section08
-- END AUTO-IMPORTS

/-!
Chapter 06

Title: Chapter 06 -- Several Variable Differential Calculus

Verso links:
- [Local Verso: Chapter overview](/ReasBook/books/analysis2_tao_2022/chapters/chap06/)
- [Local Verso: Book overview](/ReasBook/books/analysis2_tao_2022/book/)
- [Published Verso: Chapter overview](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap06/)
- [Published Verso: Book overview](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/book/)

Section overviews:

- [6.1 Linear Transformations file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap06/section01.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap06/section01/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap06/section01/))
- [6.2 Derivatives in Several Variable Calculus file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap06/section02.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap06/section02/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap06/section02/))
- [6.3 Partial and Directional Derivatives file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap06/section03.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap06/section03/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap06/section03/))
- [6.4 The Several Variable Calculus Chain Rule file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap06/section04.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap06/section04/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap06/section04/))
- [6.5 Double Derivatives and Clairaut's Theorem file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap06/section05.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap06/section05/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap06/section05/))
- [6.6 The Contraction Mapping Theorem file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap06/section06.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap06/section06/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap06/section06/))
- [6.7 The Inverse Function Theorem in Several Variable Calculus file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap06/section07.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap06/section07/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap06/section07/))
- [6.8 The Implicit Function Theorem file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/Analysis2_Tao_2022/Chapters/Chap06/section08.lean) ([Local Verso](/ReasBook/books/analysis2_tao_2022/chapters/chap06/section08/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap06/section08/))

-/

/-!
# tao_analysis2_formal: Chap06

Auto-managed imports live below.
-/
