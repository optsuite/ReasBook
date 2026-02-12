import VersoBlog
import ReasBookSite.Home
import ReasBookSite.LiterateModule
import ReasBookSite.Sections
import ReasBookSite.RouteTable
import Book

open Verso Genre Blog Site Syntax
open ReasBookSite.RouteTable
open scoped ReasBookSite.RouteTable

open Output Html Template Theme

def siteRoot : String := "/"
def siteRootScript : String := s!"window.__versoSiteRoot=\"{siteRoot}\""
def normalizeLinksScript : String :=
  "document.addEventListener(\"DOMContentLoaded\", function () {" ++
  "for (const a of document.querySelectorAll(\"a[href]\")) {" ++
  "const href = a.getAttribute(\"href\");" ++
  "if (!href) continue;" ++
  "if (href.startsWith(\"/\") || href.startsWith(\"#\") || href.startsWith(\"mailto:\") || href.startsWith(\"tel:\") || href.startsWith(\"http://\") || href.startsWith(\"https://\")) continue;" ++
  "let normalized = href;" ++
  "while (normalized.startsWith(\"/\")) normalized = normalized.slice(1);" ++
  "a.setAttribute(\"href\", \"/\" + normalized);" ++
  "}" ++
  "});"

def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html>
        <head>
          <meta charset="UTF-8"/>
          <title>{{ (← param (α := String) "title") }} " -- ReasBook "</title>
          <link rel="stylesheet" href="/static/style.css"/>
          <script>{{ siteRootScript }}</script>
          <script>{{ normalizeLinksScript }}</script>
          {{← builtinHeader }}
        </head>
        <body>
          <header>
            <div class="inner-wrap">
              <nav class="top" role="navigation">
                <ol>
                  <li><a href="/">"Home"</a></li>
                  {{ ← dirLinks (← read).site }}
                </ol>
              </nav>
            </div>
          </header>
          <div class="main" role="main">
            <div class="wrap">
              {{ (← param "content") }}
            </div>
          </div>
        </body>
      </html>
    }}
}
|>.override #[] ⟨do return {{<div class="frontpage"><h1>{{← param "title"}}</h1> {{← param "content"}}</div>}}, id⟩

/-- Generated section routes are injected by `reasbook_site_dir` from `ReasBookSite.RouteTable`. -/
def demoSite : Site := reasbook_site

def main := blogMain theme demoSite
