# ReasBook

**ReasBook** is a Lean 4 project for formalizing mathematics from textbooks and research papers.
The goal is to preserve the structure of original references while producing machine-checkable proofs.
We welcome collaboration from researchers, students, and practitioners.

## Current Coverage

### Books
- Terence Tao, *Analysis II*, 4th ed., Hindustan Book Agency / Springer, Singapore, 2022, ISBN 978-981-19-7284-3.
  - Contributors: (TBD)
  - Links: [Verso](https://optsuite.github.io/ReasBook/books/analysis2_tao_2022/chapters/chap01/section01/) | [Documentation](https://optsuite.github.io/ReasBook/docs/Books/Analysis2_Tao_2022/Chapters/Chap01/section01.html) | [Lean source](./ReasBook/Books/Analysis2_Tao_2022/Book.lean)
- R. Tyrrell Rockafellar, *Convex Analysis*, Princeton University Press, Princeton, 1970, ISBN 0-691-08069-0.
  - Contributors: (TBD)
  - Links: [Verso](https://optsuite.github.io/ReasBook/books/convexanalysis_rockafellar_1970/chapters/chap01/section01/) | [Documentation](https://optsuite.github.io/ReasBook/docs/Books/ConvexAnalysis_Rockafellar_1970/Chapters/Chap01/section01_part1.html) | [Lean source](./ReasBook/Books/ConvexAnalysis_Rockafellar_1970/Book.lean)
- Jiri Lebl, *Introduction to Real Analysis, Volume I*, version 6.2, May 23, 2025, (TBD: publisher/city), (TBD: ISBN).
  - Contributors: (TBD)
  - Links: [Verso](https://optsuite.github.io/ReasBook/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap01/section01/) | [Documentation](https://optsuite.github.io/ReasBook/docs/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Chapters/Chap01/section01.html) | [Lean source](./ReasBook/Books/IntroductiontoRealAnalysisVolumeI_JiriLebl_2025/Book.lean)
- Michele Conforti, Gerard Cornuejols, Giacomo Zambelli, *Integer Programming*, Graduate Texts in Mathematics 271, Springer, 2014, ISBN 978-3-319-11007-3.
  - Contributors: (TBD)
  - Links: Verso (TBD: landing page not yet generated) | [Documentation](https://optsuite.github.io/ReasBook/docs/) | [Source index](./ReasBook/Books/IntegerProgramming_Conforti_2014/README.md)

### Papers
- Yurii Nesterov, "Smooth minimization of non-smooth functions," *Mathematical Programming*, Ser. A 103, 127-152, 2005, DOI: 10.1007/s10107-004-0552-5.
  - Contributors: (TBD)
  - Links: [Verso](https://optsuite.github.io/ReasBook/papers/smoothminimization_nesterov_2004/paper/) | [Documentation](https://optsuite.github.io/ReasBook/docs/Papers/SmoothMinimization_Nesterov_2004/Sections/section01.html) | [Lean source](./ReasBook/Papers/SmoothMinimization_Nesterov_2004/Paper.lean)
- Mohamad Maassarani, "On Some Local Rings," arXiv:2512.19197v1 [math.AC], 2025.
  - Contributors: (TBD)
  - Links: [Verso](https://optsuite.github.io/ReasBook/papers/onsomelocalrings_maassaran_2025/paper/) | [Documentation](https://optsuite.github.io/ReasBook/docs/Papers/OnSomeLocalRings_Maassaran_2025/Sections/section01.html) | [Lean source](./ReasBook/Papers/OnSomeLocalRings_Maassaran_2025/Paper.lean)

## Repository Layout

The repository is organized into a Lean source tree and a web-documentation tree:

```text
ReasBook/
├── ReasBook/                         # Main Lean project (books + papers + doc-gen target)
│   ├── Books/
│   ├── Papers/
│   ├── ReasBook.lean
│   ├── LiterateExtract.lean
│   ├── lakefile.lean
│   ├── lake-manifest.json
│   └── lean-toolchain
├── ReasBookWeb/                      # Verso website project
│   ├── ReasBookSite/
│   ├── static_files/
│   ├── scripts/gen_sections.py
│   ├── ReasBookSite.lean
│   ├── lakefile.lean
│   ├── lake-manifest.json
│   └── lean-toolchain
├── .github/workflows/deploy_pages.yml
├── build.sh
├── build-web.sh
├── serve.py
└── scripts/cleanup-generated.sh
```

## Naming Convention

Top-level content directories use:

`<Title>_<AuthorLastName>_<Year>`

Examples:

- `ConvexAnalysis_Rockafellar_1970`
- `SmoothMinimization_Nesterov_2004`
- `OnSomeLocalRings_Maassaran_2025`

## Build

From the repository root:

```bash
./build.sh
```

Build the Verso site (including Documentation copied to `_site/docs`):

```bash
./build-web.sh
```

Serve the generated site locally:

```bash
python3 serve.py
```

If generated artifacts were previously committed, untrack them (without deleting local files):

```bash
./scripts/cleanup-generated.sh
```

## Sponsors

- Beijing International Center for Mathematical Research, Peking University
- Sino-Russian Mathematics Center
- Great Bay University
- National Natural Science Foundation of China

## Lean Projects

### Formalization Platform

- [ReasLab](https://prove.reaslab.io)
  - An online Lean formalization platform for collaborative theorem development and verification.

### Formalization Projects

- [Optlib](https://github.com/optsuite/optlib)
  - A Lean4 library for mathematical optimization, covering convex analysis, optimality conditions, and algorithm convergence.
- [ReasBook](https://github.com/optsuite/ReasBook)
  - A Lean4 project for textbook and paper formalization, including both theorem proving and computational problems.

### Benchmark

- [AMBER](https://github.com/optsuite/AMBER)
  - A Lean4 benchmark for applied mathematics formalization including proving and computational problems.

### Autoformalization and Theorem Proving Systems

- [M2F](https://github.com/optsuite/M2F)
  - A toolkit for converting natural-language mathematical textbooks into formalization-ready Lean projects.

- [SITA](https://github.com/chenyili0818/SITA)
  - A structure-to-instance autoformalization framework for generating Lean definitions/theorems with verification feedback.

## Publications

### Formalization of Optimization

- Chenyi Li, Ziyu Wang, Wanyi He, Yuxuan Wu, Shengyang Xu, Zaiwen Wen. *Formalization of Complexity Analysis of the First-order Optimization Algorithms*, Journal of Automated Reasoning. [(Paper)](https://arxiv.org/abs/2403.11437)
- Chenyi Li, Zichen Wang, Yifan Bai, Yunxi Duan, Yuqing Gao, Pengfei Hao, Zaiwen Wen. *Formalization of Algorithms for Optimization with Block Structures*, Science in China Series A: Mathematics. [(Paper)](http://arxiv.org/abs/2503.18806)
- Chenyi Li, Shengyang Xu, Chumin Sun, Li Zhou, Zaiwen Wen. *Formalization of Optimality Conditions for Smooth Constrained Optimization Problems*. [(Paper)](https://arxiv.org/abs/2503.18821)
- Chenyi Li, Zaiwen Wen. *An Introduction to Mathematics Formalization Based on Lean*. [(Paper)](http://faculty.bicmr.pku.edu.cn/~wenzw/paper/OptLean.pdf)

### Autoformalization and Automated Theorem Proving

- Ziyu Wang, Bowen Yang, Chenyi Li, Yuan Zhang, Shihao Zhou, Bin Dong, Zaiwen Wen. *Translating Informal Proofs into Formal Proofs Using a Chain of States*. [(Paper)](https://arxiv.org/abs/2512.10317)
- Chenyi Li, Wanli Ma, Zichen Wang, Zaiwen Wen. *SITA: A Framework for Structure-to-Instance Theorem Autoformalization*, AAAI 2026. [(Paper)](https://arxiv.org/abs/2511.10356)
- Chenyi Li, Yanchen Nie, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *OptProver: Bridging Olympiad and Optimization through Continual Training in Formal Theorem Proving*.
- Zichen Wang, Wanli Ma, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. *M2F: Automated Formalization of Mathematical Literature at Scale*.

### Premise Selection

- Zichen Wang, Anjie Dong, Zaiwen Wen. *Tree-Based Premise Selection for Lean4*, NeurIPS 2025. [(Paper)](https://neurips.cc/virtual/2025/loc/san-diego/poster/116011)
- Shu Miao, Zichen Wang, Anjie Dong, Yishan Wu, Weixi Zhang, Zaiwen Wen. *Directed Multi-Relational GCNs for Premise Selection*.

### Benchmark

- Bowen Yang, Yi Yuan, Chenyi Li, Ziyu Wang, Liangqi Li, Bo Zhang, Zhe Li, Zaiwen Wen. *Construction-Verification: A Benchmark for Formalizing Applied Mathematics in Lean 4*.

## Team

We are a group of scholars and students interested in mathematical formalization.

### Core Members

- Chenyi Li, School of Mathematical Sciences, Peking University, China (`lichenyi@stu.pku.edu.cn`)
- Wanli Ma, Beijing International Center for Mathematical Research, Peking University, China (`wlma@pku.edu.cn`)
- Zichen Wang, School of Mathematical Sciences, Peking University, China (`zichenwang25@stu.pku.edu.cn`)
- Ziyu Wang, School of Mathematical Sciences, Peking University, China (`wangziyu-edu@stu.pku.edu.cn`)
- Zaiwen Wen, Beijing International Center for Mathematical Research, Peking University, China (`wenzw@pku.edu.cn`)

### Contributors

- Yifan Bai, Anjie Dong, Yunxi Duan, Xinyi Guo, Pengfei Hao, Yuhao Jiang, Gongxun Li, Zebo Liu, Zhenxi Liu, Siyuan Ma, Guangxuan Pan, Siyuan Shao, Weiran Shi, Junren Si, Xuran Sun, Xuan Tang, Yijie Wang, Zhiyan Wang, Zixi Wang, Suwan Wu, Mingyue Xu, Yunfei Zhang, Changyun Zou

## License

Copyright (c) 2026 Chenyi Li, Wanli Ma, Zichen Wang, Ziyu Wang, Zaiwen Wen.

Released under the Apache 2.0 license. See `LICENSE` for details.
