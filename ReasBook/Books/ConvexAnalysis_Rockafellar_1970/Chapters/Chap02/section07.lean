/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Wanli Ma, Xinyi Guo, Zaiwen Wen
-/

import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part1
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part2
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part6
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part7
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part8
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part9
import Books.ConvexAnalysis_Rockafellar_1970.Chapters.Chap02.section07_part10

/-!
Overview page for `2.7 Closures of Convex Functions`.

This aggregation module imports all currently available part files for this section.

Verso links:
- [Local Verso: Section overview](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07/)
- [Local Verso: Chapter overview](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/)
- [Local Verso: Book overview](/ReasBook/books/convexanalysis_rockafellar_1970/book/)
- [Published Verso: Section overview](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07/)
- [Published Verso: Chapter overview](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/)
- [Published Verso: Book overview](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/book/)

Directory:

- [Part 1 file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section07_part1.lean) ([Local Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part1/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part1/))
- [Part 2 file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section07_part2.lean) ([Local Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part2/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part2/))
- [Part 3 file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section07_part3.lean) ([Local Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part3/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part3/))
- [Part 4 file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section07_part4.lean) ([Local Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part4/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part4/))
- [Part 5 file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section07_part5.lean) ([Local Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part5/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part5/))
- [Part 6 file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section07_part6.lean) ([Local Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part6/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part6/))
- [Part 7 file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section07_part7.lean) ([Local Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part7/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part7/))
- [Part 8 file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section07_part8.lean) ([Local Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part8/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part8/))
- [Part 9 file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section07_part9.lean) ([Local Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part9/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part9/))
- [Part 10 file](https://github.com/optsuite/ReasBook/blob/main/ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap02/section07_part10.lean) ([Local Verso](/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part10/)) ([Published Verso](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap02/section07_part10/))

-/
