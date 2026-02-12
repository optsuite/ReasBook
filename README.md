# ReasBook

**ReasBook** is a Lean 4 project for formalizing mathematics from textbooks and research papers.
The goal is to preserve the structure of original references while producing machine-checkable proofs.
We welcome collaboration from researchers, students, and practitioners.

## Current Coverage

### Books

- *Analysis II*, Terence Tao (2022)
  - Chapter 1 ([Verso page](https://optsuite.github.io/books/analysis2_tao_2022/chapters/chap01/section01/))
  - Chapter 2 ([Verso page](https://optsuite.github.io/books/analysis2_tao_2022/chapters/chap02/section01/))
  - Chapter 3 ([Verso page](https://optsuite.github.io/books/analysis2_tao_2022/chapters/chap03/section01/))
  - Chapter 4 ([Verso page](https://optsuite.github.io/books/analysis2_tao_2022/chapters/chap04/section01/))
  - Chapter 5 ([Verso page](https://optsuite.github.io/books/analysis2_tao_2022/chapters/chap05/section01/))
  - Chapter 6 ([Verso page](https://optsuite.github.io/books/analysis2_tao_2022/chapters/chap06/section01/))
- *Convex Analysis*, R. Tyrrell Rockafellar (1970)
  - Chapter 1 ([Verso page](https://optsuite.github.io/books/convexanalysis_rockafellar_1970/chapters/chap01/section01/))
  - Chapter 2 ([Verso page](https://optsuite.github.io/books/convexanalysis_rockafellar_1970/chapters/chap02/section05/))
  - Chapter 3 ([Verso page](https://optsuite.github.io/books/convexanalysis_rockafellar_1970/chapters/chap03/section11/))
  - Chapter 4 ([Verso page](https://optsuite.github.io/books/convexanalysis_rockafellar_1970/chapters/chap04/section17/))
- *Introduction to Real Analysis, Volume I*, Jiri Lebl (2025)
  - Chapter 0 ([Verso page](https://optsuite.github.io/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap00/section03/))
  - Chapter 1 ([Verso page](https://optsuite.github.io/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap01/section01/))
  - Chapter 2 ([Verso page](https://optsuite.github.io/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap02/section01/))
  - Chapter 3 ([Verso page](https://optsuite.github.io/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap03/section01/))
  - Chapter 4 ([Verso page](https://optsuite.github.io/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap04/section01/))
  - Chapter 5 ([Verso page](https://optsuite.github.io/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap05/section01/))
  - Chapter 6 ([Verso page](https://optsuite.github.io/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap06/section01/))
  - Chapter 7 ([Verso page](https://optsuite.github.io/books/introductiontorealanalysisvolumei_jirilebl_2025/chapters/chap07/section01/))
- *Integer Programming*, Michele Conforti et al. (2014) (not yet formalized)

### Papers

- *Smooth Minimization of Nonsmooth Functions*, Yurii Nesterov (2004)
  - Section 1 ([Verso page](https://optsuite.github.io/papers/smoothminimization_nesterov_2004/sections/section01/))
  - Section 2 ([Verso page](https://optsuite.github.io/papers/smoothminimization_nesterov_2004/sections/section02/))
  - Section 3 ([Verso page](https://optsuite.github.io/papers/smoothminimization_nesterov_2004/sections/section03/))
  - Section 4 ([Verso page](https://optsuite.github.io/papers/smoothminimization_nesterov_2004/sections/section04/))
  - Section 5 ([Verso page](https://optsuite.github.io/papers/smoothminimization_nesterov_2004/sections/section05/))
- *On Some Local Rings*, Mansour Maassaran (2025)
  - Section 1 ([Verso page](https://optsuite.github.io/papers/onsomelocalrings_maassaran_2025/sections/section01/))
  - Section 2 ([Verso page](https://optsuite.github.io/papers/onsomelocalrings_maassaran_2025/sections/section02/))

## Repository Layout

The repository is organized into a Lean source tree and a web-documentation tree:

```text
ReasBook/
├── ReasBook/                  # Lean project root
│   ├── Books/                 # Textbook formalizations
│   ├── Papers/                # Paper formalizations
│   ├── ReasBook.lean          # Top-level import module
│   ├── lakefile.toml
│   └── lean-toolchain
└── ReasBookWeb/               # Generated HTML documentation
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
cd ReasBook/ReasBook
lake update
lake build
```

## Documentation

We use **Verso** to generate interactive web documentation that combines Lean code and mathematical exposition.

## Sponsors

- Beijing International Center for Mathematical Research, Peking University
- Sino-Russian Mathematics Center
- Great Bay University
- National Natural Science Foundation of China

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
