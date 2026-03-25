import Std.Data.HashMap
import VersoManual
import SutherlandNumberTheory

open Verso.Genre Manual

def customCss : String := "
/* === Number Theory I: Custom Theme === */
/* Green and orange accents over the default Verso theme */

:root {
  /* Headings */
  --verso-structure-color: #2d6a4f;

  /* TOC sidebar */
  --verso-toc-background-color: #f0f7f2;

  /* Selection highlight */
  --verso-selected-color: #fde8d0;

  /* Code syntax highlighting */
  --verso-code-keyword-color: #2d6a4f;
  --verso-code-const-color: #5a4a3a;
}

/* Header bar */
header {
  background: linear-gradient(135deg, #2d6a4f 0%, #3a7d5c 100%) !important;
  box-shadow: 0 2px 8px rgba(45, 106, 79, 0.3) !important;
}
.header-title, .header-title h1 {
  color: white !important;
}

/* Section headings */
h1, h2, h3 {
  color: #2d6a4f;
}

/* Links */
a {
  color: #40916c;
}
a:hover {
  color: #e76f51;
}

/* TOC sidebar styling */
#toc .split-toc .title a {
  color: #2d6a4f;
}
#toc .split-toc .title .current a {
  color: #e76f51;
  font-weight: bold;
}

/* Prev/next navigation */
.prev-next-buttons a {
  color: #e76f51 !important;
  font-weight: 600;
}
.prev-next-buttons a:hover {
  color: #d45a3a !important;
}
.prev-next-buttons .arrow {
  color: #e76f51;
}

/* Lean code blocks */
code.hl.lean.block {
  background: #fef8f0 !important;
  border-left: 3px solid #40916c;
  padding: 0.75rem 1rem !important;
  border-radius: 4px;
  display: block;
}

/* Doc comments in code blocks */
.doc-comment.token {
  color: #40916c !important;
}

/* Inline code */
code.math.inline, code.math.display {
  color: #3a3a3a;
}

/* Permalink widget */
.permalink-widget a {
  color: #b7d4c0 !important;
}
.permalink-widget a:hover {
  color: #e76f51 !important;
}

/* Search box */
input[type='search'] {
  border-color: #b7d4c0 !important;
}
input[type='search']:focus {
  border-color: #40916c !important;
  outline-color: #40916c;
}
"

def config : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  htmlDepth := 2
  extraCss := [customCss]

def main := manualMain (%doc SutherlandNumberTheory) (config := config)
