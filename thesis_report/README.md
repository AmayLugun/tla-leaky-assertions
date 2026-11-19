# BIT Mesra Thesis LaTeX Report

This directory contains the single unified LaTeX document (`main.tex`) for the **Birla Institute of Technology (BIT), Mesra** thesis report, using the exact font style (`lmodern`, Latin Modern serif) of `documents/report.tex`.

---

## File Structure

- **`main.tex`**: Primary LaTeX document currently containing **Page 1 (Title Page)** formatted to match the BIT Mesra template with [`Birla_Institute_of_Technology_Mesra.png`](Birla_Institute_of_Technology_Mesra.png). Additional pages can be added below `\end{titlepage}` page by page.
- **`main.pdf`**: Compiled 1-page PDF document.
- **`Birla_Institute_of_Technology_Mesra.png`**: Official BIT Mesra emblem.

---

## Compilation

```bash
cd thesis_report
pdflatex main.tex
```
