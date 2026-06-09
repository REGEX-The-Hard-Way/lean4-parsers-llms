# 📄 `parseltongue`

> *LLM-generated parsers, verified in Lean4*

A collection of parsers for programming languages, document formats, and complex markup — written primarily by LLMS, type-checked and verified in the Lean4 theorem prover.

---

## 🎯 Goal

Generate correct-by-construction parsers for:

| Category | Examples |
|----------|----------|
| **Programming languages** | Python subset, JSON, Lua, MiniML |
| **Document formats** | CSV, XML, HTML, Markdown |
| **Binary / data formats** | PDF (structure), TOML, YAML |
| **Complex document languages** | LaTeX, reStructuredText, Org-mode |
| **Domain-specific languages** | SQL, Regex, GraphQL |

Parsers are:
- ✅ Written **with heavy LLMS assistance** (Claude, DeepSeek4, Gemini)
- ✅ Verified in **Lean4** for correctness and totality
- ✅ Designed to be **provably non-crashing** and unambiguous where possible

---

## 🧠 Philosophy

> *"Trust, but verify — especially when the code was hallucinated at 3 AM."*

LLMS can generate parser stubs quickly. Lean4 ensures they:
- Terminate
- Don't index out of bounds
- Handle all cases (no hidden `sorry` or `panic`)
- Respect grammar constraints via dependent types

This repo explores the **LLMS + formal verification** workflow for real-world parsing tasks.

---

## 📁 Repository Structure

```
parseltongue/
├── Lean4/
│   ├── CSV/           # CSV parser with proofs
│   ├── JSON/          # Validating JSON parser
│   ├── LaTeX/         # LaTeX grammar subset
│   ├── XML/           # Well-formedness + parsing
│   └── PDF/           # PDF object structure parser
├── generated/         # Raw LLMS-generated stubs before porting
├── proofs/            # Lean4 termination & correctness proofs
├── tests/             # Property-based testing + examples
└── docs/              # Parser design and verification notes
```

---

## 🔧 How It Works

1. **LLMS generation** – Prompt LLM to write a parser in Lean4 (or a stub + spec)
2. **Manual refinement** – Add type signatures, preconditions, termination proofs
3. **Verification** – Lean4 checks all definitions and theorems
4. **Extraction** – Optionally extract to efficient C/JavaScript via Lean4 backend

---

## 🚀 Getting Started

### Prerequisites
- Lean 4 (latest stable)
- `lake` build tool

### Build
```bash
lake build
```

### Run tests
```bash
lake test
```


## 🛠 Future Work

- [ ] Full LaTeX grammar parsing with error recovery
- [ ] PDF text extraction + structure validation
- [ ] Generate parser from BNF spec using LLM + Lean4 tactic automation
- [ ] Benchmark against traditional parser generators (ANTLR, happy)

---

## 📝 License

MIT — parsers are free to use; verification proofs are open for learning.

---

## 🙃 Acknowledgments

- Lean4 theorem prover
- The LLMSs who wrote most of this code (and apologized when they failed to terminate)
- Parser combinators, the unsung heroes of PL

---

*Found a bug? The LLMS probably wrote it. Open an issue or prove us wrong with a counterexample.* 🐛
