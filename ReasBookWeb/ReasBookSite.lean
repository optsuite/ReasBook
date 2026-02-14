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
def docsRoot : String := s!"{siteRoot}docs/"
def staticRoot : String := s!"{siteRoot}static/style.css"
def navLinkRewriteScript : String :=
  "(function(){" ++
  "const siteRoot='/ReasBook/';" ++
  "const isExternal=(h)=>/^(?:[a-z]+:)?\\/\\//i.test(h);" ++
  "const isSpecial=(h)=>h.startsWith('#')||h.startsWith('mailto:')||h.startsWith('tel:');" ++
  "const normalize=(href)=>{" ++
  "if(!href)return href;" ++
  "if(isSpecial(href))return href;" ++
  "if(isExternal(href))return href;" ++
  "if(href==='/'||href==='/index.html')return siteRoot;" ++
  "if(href==='/docs'||href==='/docs/')return siteRoot+'docs/';" ++
  "if(href.startsWith(siteRoot))return href;" ++
  "if(href.startsWith('/'))return siteRoot+href.slice(1);" ++
  "return siteRoot+href.replace(/^\\.?\\//,'');" ++
  "};" ++
  "const rewriteAll=()=>{" ++
  "for(const a of document.querySelectorAll('a[href]')){" ++
  "const oldHref=(a.getAttribute('href')||'').trim();" ++
  "const newHref=normalize(oldHref);" ++
  "if(newHref&&newHref!==oldHref)a.setAttribute('href',newHref);" ++
  "}" ++
  "};" ++
  "const onClick=(ev)=>{" ++
  "if(ev.defaultPrevented||ev.button!==0||ev.metaKey||ev.ctrlKey||ev.shiftKey||ev.altKey)return;" ++
  "const a=ev.target&&ev.target.closest?ev.target.closest('a[href]'):null;" ++
  "if(!a)return;" ++
  "if((a.getAttribute('target')||'').toLowerCase()==='_blank')return;" ++
  "const oldHref=(a.getAttribute('href')||'').trim();" ++
  "if(!oldHref||isExternal(oldHref)||isSpecial(oldHref))return;" ++
  "const newHref=normalize(oldHref);" ++
  "if(!newHref)return;" ++
  "if(newHref!==oldHref)a.setAttribute('href',newHref);" ++
  "ev.preventDefault();" ++
  "window.location.assign(newHref);" ++
  "};" ++
  "const boot=()=>{" ++
  "rewriteAll();" ++
  "document.addEventListener('click',onClick,true);" ++
  "const mo=new MutationObserver(()=>rewriteAll());" ++
  "mo.observe(document.documentElement,{subtree:true,childList:true});" ++
  "};" ++
  "if(document.readyState==='loading')document.addEventListener('DOMContentLoaded',boot);else boot();" ++
  "})();"

def theme : Theme := { Theme.default with
  primaryTemplate := do
    return {{
      <html>
        <head>
          <meta charset="UTF-8"/>
          <title>{{ (← param (α := String) "title") }} " -- ReasBook "</title>
          <link rel="stylesheet" href="/ReasBook/static/style.css"/>
          <script>{{ siteRootScript }}</script>
          <script>{{ navLinkRewriteScript }}</script>
          {{← builtinHeader }}
        </head>
        <body>
          <header>
            <div class="inner-wrap">
              <nav class="top" role="navigation">
                <ol>
                  <li><a href="/ReasBook/">"Home"</a></li>
                  <li><a href="/ReasBook/docs/">"Documentation"</a></li>
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

def baseUrl := "https://optsuite.github.io/ReasBook/docs/"

def linkTargets : Code.LinkTargets α where
  const name _ := #[mkLink s!"{baseUrl}find?pattern={name}#doc"]
  definition name _ := #[mkLink s!"{baseUrl}find?pattern={name}#doc"]
where
  mkLink href := { shortDescription := "doc", description := "API documentation", href }

def main := blogMain theme demoSite (linkTargets := linkTargets)
