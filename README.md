# ReasBook

**ReasBook** is a comprehensive repository dedicated to the systematic formalization of classical mathematical textbooks and research papers using **Lean 4**. By strictly following the structure of authoritative literature across diverse areas of mathematics, this project bridges human-written mathematical texts with machine-verifiable proofs. Our long-term goal is to build a high-quality, machine-readable corpus **covering the broader mathematics landscape** and to actively welcome participation from the global community of researchers, students, and practitioners.

## Books and Papers Already Formalized

### Real Analysis, Tao, 2006

- Book Information: *Real Analysis*, Terence Tao, 2006.
- Formalization Contributors: to be updated.

### Convex Analysis, R.T. Rockafellar, 1970

- Book Information: *Convex Analysis*, R. Tyrrell Rockafellar, 1970.
- Formalization Contributors: to be updated.


## Repository Organization

To keep the library scalable and navigable, we use a standardized naming convention for all top-level directories. This ensures the correspondence between formal code and the original source material is immediately apparent.

### Naming Scheme and Structure

We categorize resources into **Textbooks** and **Papers**. Both use the format:

`[Name]_[AuthorsLastName]_[PublicationTime]`

Example: *Convex Analysis* by R.T. Rockafellar (1970) is placed in `ConvexAnalysis_Rockafellar_1970`. Within each book directory, content is organized by chapter (e.g., `Chapter_01`).

We keep the Lean sources in `ReasBook/`, and keep the generated HTML output in a sibling folder `ReasBookWeb/`. The two are aligned by directory names to make cross-referencing straightforward.

```text
REASBOOK
  ReasBook/(lean仓库)
  ├── Books/
  │   ├── ConvexAnalysis_Rockafellar_1970/      -- [Convex Analysis, R.T. Rockafellar, 1970]
  │   │   ├── Chapter_01/
  │   │   ├── Chapter_02/
  │   ├── IntegerProgramming_Conforti_2014/     -- [Integer Programming, Conforti et al., 2014]
  │   │   ├── Chapter_01/
  │   │   └── ...
  ├── Papers/                                     -- Formalization of specific research papers
      ├── Paper1/
      └── Paper2/

  ReasBookWeb/(lean仓库) -- Generated HTML documentation output
  ├── Books/
  │   ├── ConvexAnalysis_Rockafellar_1970/      
  │   │   ├── Chapter_01/
  │   │   ├── Chapter_02/
  │   ├── IntegerProgramming_Conforti_2014/     
  │   │   ├── Chapter_01/
  │   │   └── ...
  ├── Papers/                                 
      ├── Paper1/
      └── Paper2/
```

## Documentation with Verso

We use **Verso** to generate interactive, web-based documentation. Unlike standard code comments, Verso lets us interweave formal Lean code with rich mathematical explanations, creating a literate programming experience that mirrors the flow of the original textbooks.

## Sponsor

- Beijing International Center for Mathematical Research, Peking University
- Sino-Russian Mathematics Center
- Great Bay University
- National Natural Science Foundation of China

## Publications

### Formalization of Optimization

- Chenyi Li, Ziyu Wang, Wanyi He, Yuxuan Wu, Shengyang Xu, Zaiwen Wen. Formalization of Complexity Analysis of the First-order Optimization Algorithms, Journal of Automated Reasoning. [(Paper)](https://arxiv.org/abs/2403.11437)
- Chenyi Li, Zichen Wang, Yifan Bai, Yunxi Duan, Yuqing Gao, Pengfei Hao, Zaiwen Wen. Formalization of Algorithms for Optimization with Block Structures, Science in China Series A: Mathematics. [(Paper)](http://arxiv.org/abs/2503.18806)
- Chenyi Li, Shengyang Xu, Chumin Sun, Li Zhou, Zaiwen Wen. Formalization of Optimality Conditions for Smooth Constrained Optimization Problems. [(Paper)](https://arxiv.org/abs/2503.18821)
- Chenyi Li, Zaiwen Wen. An Introduction to Mathematics Formalization Based on Lean (in Chinese). [(Paper)](http://faculty.bicmr.pku.edu.cn/~wenzw/paper/OptLean.pdf)

### Autoformalization and Automatic Theorem Proving

- Ziyu Wang, Bowen Yang, Chenyi Li, Yuan Zhang, Shihao Zhou, Bin Dong, Zaiwen Wen. Translating Informal Proofs into Formal Proofs Using a Chain of States. [(Paper)](https://arxiv.org/abs/2512.10317)
- Chenyi Li, Wanli Ma, Zichen Wang, Zaiwen Wen. SITA: A Framework for Structure-to-Instance Theorem Autoformalization, AAAI 2026. [(Paper)](https://arxiv.org/abs/2511.10356)
- Chenyi Li, Yanchen Nie, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. OptProver: Bridging Olympiad and Optimization through Continual Training in Formal Theorem Proving.
- Zichen Wang, Wanli Ma, Zhenyu Ming, Gong Zhang, Kun Yuan, Zaiwen Wen. M2F: Automated Formalization of Mathematical Literature at Scale.

### Premise Selection

- Zichen Wang, Anjie Dong, Zaiwen Wen. Tree-Based Premise Selection for Lean4, NeurIPS 2025. [(Paper)](https://neurips.cc/virtual/2025/loc/san-diego/poster/116011)
- Shu Miao, Zichen Wang, Anjie Dong, Yishan Wu, Weixi Zhang, Zaiwen Wen. Directed Multi-Relational GCNs for Premise Selection.

### Benchmark

- Bowen Yang, Yi Yuan, Chenyi Li, Ziyu Wang, Liangqi Li, Bo Zhang, Zhe Li, Zaiwen Wen. Construction–Verification: A Benchmark for Formalizing Applied Mathematics in Lean 4.


## The Team

We are a group of scholars and students with a keen interest in mathematical formalization.

### Core Members

- Chenyi Li, School of Mathematical Sciences, Peking University, CHINA (lichenyi@stu.pku.edu.cn)
- Wanli Ma, Beijing International Center for Mathematical Research, Peking University, CHINA (wlma@pku.edu.cn)
- Zichen Wang, School of Mathematics and Statistics, Xi’an Jiaotong University, CHINA (zichenwang25@stu.pku.edu.cn)
- Ziyu Wang, School of Mathematical Sciences, Peking University, CHINA (wangziyu-edu@stu.pku.edu.cn)
- Zaiwen Wen, Beijing International Center for Mathematical Research, Peking University, CHINA (wenzw@pku.edu.cn)

### Other Contributors

- Undergraduate students from Peking University:

  Hongjia Chen, Wanyi He, Yuxuan Wu, Shengyang Xu, Junda Ying, Penghao Yu, ...

- Undergraduate students from Summer Seminar on Mathematical Formalization and Theorem Proving, BICMR, Peking University, 2023:

  Zhipeng Cao, Yiyuan Chen, Heying Wang, Zuokai Wen, Mingquan Zhang, Ruichong Zhang, ...

- Undergraduate and graduate students from Summer Seminar on Mathematical Formalization and Theorem Proving, BICMR, Peking University, 2024:

  Yifan Bai, Yunxi Duan, Yuqing Gao, Pengfei Hao, Anqing Shen

- Other collaborators:

  Anjie Dong, Xinyi Guo, Yuhao Jiang, Gongxun Li, Zebo Liu, Zhenxi Liu, Siyuan Ma, Guangxuan Pan, Siyuan Shao, Weiran Shi, Junren Si, Xuran Sun, Xuan Tang, Yijie Wang, Zhiyan Wang, Zixi Wang, Suwan Wu, Mingyue Xu, Yunfei Zhang, Changyun Zou

## Copyright

Copyright (c) 2026 Chenyi Li, Wanli Ma, Zichen Wang, Ziyu Wang, Zaiwen Wen. All rights reserved.

Released under Apache 2.0 license as described in the file LICENSE.
