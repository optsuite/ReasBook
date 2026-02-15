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

def siteRoot : String := "/ReasBook/"
def siteRootScript : String := s!"window.__versoSiteRoot=\"{siteRoot}\""
def sidebarDataScript : String := s!"window.__reasbookSidebarData={ReasBookSite.Sections.sidebarDataJson};"
def docsRoot : String := s!"{siteRoot}docs/"
def staticRoot : String := s!"{siteRoot}static/style.css"
def navLinkRewriteScript : String := r##"
(function () {
  const siteRoot = "/ReasBook/";
  const siteRootNoSlash = "/ReasBook";
  const specials = ["#", "mailto:", "tel:"];

  function isSpecial(href) {
    return specials.some((p) => href.startsWith(p));
  }

  function trimToLastSegment(rel, key) {
    const i = rel.lastIndexOf(key);
    if (i > 0) return rel.slice(i);
    return rel;
  }

  function canonicalRelPath(rel) {
    rel = rel.replace(/^\/+/, "");
    rel = trimToLastSegment(rel, "books/");
    rel = trimToLastSegment(rel, "papers/");
    rel = trimToLastSegment(rel, "docs/");
    return rel;
  }

  function normalizeInternalHref(href) {
    if (!href) return href;
    href = href.trim();
    if (!href || isSpecial(href)) return href;

    let u;
    try {
      u = new URL(href, window.location.origin);
    } catch (_) {
      return href;
    }

    if (u.origin !== window.location.origin) return href;

    // Preserve query/hash while normalizing the path component.
    const qh = u.search + u.hash;
    let p = u.pathname;

    if (p === "/" || p === "/index.html") return siteRoot + qh;
    if (p === "/docs" || p === "/docs/") return siteRoot + "docs/" + qh;

    let rel;
    if (p.startsWith(siteRoot)) rel = p.slice(siteRoot.length);
    else if (p.startsWith(siteRootNoSlash + "/")) rel = p.slice(siteRootNoSlash.length + 1);
    else if (p.startsWith("/")) rel = p.slice(1);
    else rel = p;

    rel = canonicalRelPath(rel);
    return siteRoot + rel + qh;
  }

  function rewriteAllAnchors() {
    for (const a of document.querySelectorAll("a[href]")) {
      const oldHref = (a.getAttribute("href") || "").trim();
      const newHref = normalizeInternalHref(oldHref);
      if (newHref && newHref !== oldHref) a.setAttribute("href", newHref);
    }
  }

  function onClick(ev) {
    if (ev.defaultPrevented || ev.button !== 0 || ev.metaKey || ev.ctrlKey || ev.shiftKey || ev.altKey) return;
    const a = ev.target && ev.target.closest ? ev.target.closest("a[href]") : null;
    if (!a) return;
    if ((a.getAttribute("target") || "").toLowerCase() === "_blank") return;

    const oldHref = (a.getAttribute("href") || "").trim();
    const newHref = normalizeInternalHref(oldHref);
    if (!newHref || newHref === oldHref) return;

    a.setAttribute("href", newHref);
    ev.preventDefault();
    window.location.assign(newHref);
  }

  function boot() {
    const navData = window.__reasbookSidebarData || { books: [], papers: [] };
    const navRoot = document.getElementById("sidebar-nav-root");

    function trimSlashes(s) {
      return (s || "").replace(/^\/+|\/+$/g, "");
    }

    function mkItem(href, label) {
      const li = document.createElement("li");
      const a = document.createElement("a");
      a.href = href;
      a.textContent = label;
      li.appendChild(a);
      return li;
    }

    function mkSectionGroup(title, works) {
      const li = document.createElement("li");
      const details = document.createElement("details");
      details.open = true;
      const summary = document.createElement("summary");
      summary.textContent = title;
      details.appendChild(summary);

      const workList = document.createElement("ul");
      for (const w of works || []) {
        const workLi = document.createElement("li");
        const workDetails = document.createElement("details");
        const workSummary = document.createElement("summary");
        workSummary.textContent = w.title;
        workDetails.appendChild(workSummary);

        const sectionList = document.createElement("ul");
        for (const s of (w.sections || [])) {
          sectionList.appendChild(mkItem(siteRoot + trimSlashes(s.route) + "/", s.title));
        }
        workDetails.appendChild(sectionList);
        workLi.appendChild(workDetails);
        workList.appendChild(workLi);
      }

      details.appendChild(workList);
      li.appendChild(details);
      return li;
    }

    function renderGroupedNav(list) {
      list.appendChild(mkItem(siteRoot, "Home"));
      list.appendChild(mkItem(siteRoot + "docs/", "Documentation"));
      list.appendChild(mkSectionGroup("Books", navData.books || []));
      list.appendChild(mkSectionGroup("Papers", navData.papers || []));
    }

    function renderSidebarNav() {
      if (!navRoot) return;
      navRoot.innerHTML = "";
      const list = document.createElement("ol");
      renderGroupedNav(list);
      navRoot.appendChild(list);
    }

    renderSidebarNav();
    rewriteAllAnchors();
    document.addEventListener("click", onClick, true);
  }

  if (document.readyState === "loading") document.addEventListener("DOMContentLoaded", boot);
  else boot();
})();
"##

def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html>
        <head>
          <meta charset="UTF-8"/>
          <base href="/ReasBook/"/>
          <title>{{ (← param (α := String) "title") }} " -- ReasBook "</title>
          <link rel="stylesheet" href="/ReasBook/static/style.css"/>
          <script>{{ siteRootScript }}</script>
          <script>{{ sidebarDataScript }}</script>
          <script>{{ navLinkRewriteScript }}</script>
          {{← builtinHeader }}
        </head>
        <body>
          <header>
            <div class="inner-wrap">
              <nav class="top" role="navigation" id="sidebar-nav-root"></nav>
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

def baseUrl := "https://optsuite.github.io/ReasBook/docs/"

def linkTargets : Code.LinkTargets α where
  const name _ := #[mkLink s!"{baseUrl}find?pattern={name}#doc"]
  definition name _ := #[mkLink s!"{baseUrl}find?pattern={name}#doc"]
where
  mkLink href := { shortDescription := "doc", description := "API documentation", href }

def main := blogMain theme demoSite (linkTargets := linkTargets)
