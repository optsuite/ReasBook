import VersoBlog
import ReasBookSite.Home
import ReasBookSite.LiterateModule
import ReasBookSite.NavData
import ReasBookSite.Sections
import ReasBookSite.RouteTable
import Book

open Verso Genre Blog Site Syntax
open ReasBookSite.RouteTable
open scoped ReasBookSite.RouteTable

open Output Html Template Theme

def siteRoot : String := "/ReasBook/"
def siteRootScript : String := s!"window.__versoSiteRoot=\"{siteRoot}\""
def navDataScript : String := s!"window.__reasbookNavData={ReasBookSite.NavData.navDataJson};"
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
    const navData = window.__reasbookNavData || { books: [], papers: [] };
    const navRoot = document.getElementById("sidebar-nav-root");

    function trimSlashes(s) {
      return (s || "").replace(/^\/+|\/+$/g, "");
    }

    function currentRelPath() {
      let p = window.location.pathname || "/";
      if (p.startsWith(siteRoot)) p = p.slice(siteRoot.length);
      else p = p.replace(/^\/+/, "");
      return trimSlashes(p);
    }

    function mkItem(href, label) {
      const li = document.createElement("li");
      const a = document.createElement("a");
      a.href = href;
      a.textContent = label;
      li.appendChild(a);
      return li;
    }

    function renderDefaultNav(list) {
      list.appendChild(mkItem(siteRoot, "Home"));
      list.appendChild(mkItem(siteRoot + "docs/", "Documentation"));
      for (const w of [...(navData.books || []), ...(navData.papers || [])]) {
        list.appendChild(mkItem(siteRoot + trimSlashes(w.homeRoute) + "/", w.title));
      }
    }

    function renderWorkNav(list, work) {
      list.appendChild(mkItem(siteRoot, "Home"));
      list.appendChild(mkItem(siteRoot + "docs/", "Documentation"));
      list.appendChild(mkItem(siteRoot + trimSlashes(work.homeRoute) + "/", work.title + " Home"));
      for (const s of work.sections || []) {
        list.appendChild(mkItem(siteRoot + trimSlashes(s.route) + "/", s.title));
      }
    }

    function renderSidebarNav() {
      if (!navRoot) return;
      navRoot.innerHTML = "";
      const list = document.createElement("ol");

      const rel = currentRelPath();
      const parts = rel.split("/").filter(Boolean);
      if (parts.length >= 2 && (parts[0] === "books" || parts[0] === "papers")) {
        const slug = parts[1];
        const works = parts[0] === "books" ? (navData.books || []) : (navData.papers || []);
        const work = works.find((w) => w.slug === slug);
        if (work) {
          renderWorkNav(list, work);
        } else {
          renderDefaultNav(list);
        }
      } else {
        renderDefaultNav(list);
      }

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
          <script>{{ navDataScript }}</script>
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
