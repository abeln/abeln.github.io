#lang scribble/html
@(require racket/match)
@(require racket/list)
@(require (only-in (rename-in racket/base (map list-map)) list-map))
@(require scribble/html/extra)

@(define (emph-name names name)
   (list-map (lambda (n) (if (equal? n name) @em{@n} n)) names))

@(define (elem-join lst sep)
   (match lst
     ['() '()]
     [(cons e lst)
      (cond
        [(empty? lst) (cons e lst)]
        [else (cons e (cons sep (elem-join lst sep)))])]))

@(define (show-urls urls)
   (cond
     [(empty? urls) @span{}]
     [else @span{|@elem-join[@(list-map (lambda (p) (@a[style: "color:blue" href: (first p)]{@(second p)})) urls) ", "]}]))

@(define (pub title authors venue urls)
  @li{
    @b{@title} @(show-urls urls)
    @br
    @elem-join[(emph-name authors "Abel Nieto") ", "]
    @br
    @small[@span[style: "color:gray"]{@venue}]
  }
)

@(define (tr title authors year urls)
  @li{
    @b{@title} @(show-urls urls)
    @br
    @elem-join[(emph-name authors "Abel Nieto") ", "]
    @br
    @small[@span[style: "color:gray"]{@year}]
  }
)

@(define (thesis title kind urls)
  @li{
    @b{@title} @(show-urls urls)
    @br
    @small[@span[style: "color:gray"]{@kind}]
  }
)

@(define (scribble title file date)
   @li{
       @a[href: @(string-append "scribbles/" @file ".html")]{@title} @small[@span[style: "color:gray"]{(@date)}]
   }
 )

@doctype{html}

@html[lang: "en"]{
 @head{
  @link[rel: "stylesheet" href: "tufte.css"]
  @script[src: "https://polyfill.io/v3/polyfill.min.js?features=es6"]
  @script[id: "MathJax-script" async:"" src:"https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"]
 }
 @body{
  @article{
    @h1{Abel Nieto}
    @; Intro section 
    @section{
      @p{
         Hello! My name is Abel, and I’m a PhD student at Aarhus University, where
         I'm a member of the @a[href: "https://cs.au.dk/research/logic-and-semantics/"]{Logic and Semantics} group,
         as well as the @a[href: "https://cs.au.dk/research/centers/cpv/"]{Center for Basic Research in Program Verification}.
         My advisor is @a[href: "https://cs.au.dk/~birke/"]{Lars Birkedal}.
       }
       @p{
         I work on @a[href: "https://iris-project.org/"]{formal verification} of distributed systems. I'm also interested in programming language design, type theory,
         program analysis, and compilers.
       }
    }
    @; Publications
    @section{
      @h2{Publications}
      @h3{peer-reviewed}
      @ol{
        @(pub "Blame for Null"
              '("Abel Nieto" "Marianna Rapoport" "Gregor Richards" "Ondřej Lhoták")
              "To appear in ECOOP 2020"
              '(("https://github.com/abeln/null-calculus" "code")))
        @(pub "Scala with Explicit Nulls"
              '("Abel Nieto" "Yaoyu Zhao" "Ondřej Lhoták" "Angela Chang" "Justin Pu")
              "To appear in ECOOP 2020"
              '(("https://github.com/abeln/dotty/tree/dotty-explicit-nulls-evaluation" "code")))
        @(pub "Towards Algorithmic Typing for DOT (Short Paper)"
              '("Abel Nieto")
              "Scala Symposium 2017"
              '(("https://cs.uwaterloo.ca/~anietoro/algo-dot.pdf" ".pdf")
                ("https://www.youtube.com/watch?v=uokvc1Do_nM" "talk")))
        }
      @h3{technical reports}
      @ol{
        @(tr "Tamarin: Concolic Disequivalence for MIPS"
             '("Abel Nieto")
             2018
             '(("https://arxiv.org/pdf/1801.02571.pdf" ".pdf")))
        @(tr "Towards Algorithmic Typing for DOT"
             '("Abel Nieto")
             2017
             '(("https://arxiv.org/abs/1708.05437" ".pdf")))
      }
      @h3{thesis}
      @ol{
        @(thesis "Scala with Explicit Nulls"
                  "master thesis, University of Waterloo, 2019"
                 '(("https://uwspace.uwaterloo.ca/handle/10012/15364" ".pdf")))
      }
    }
    @; Scribbles
    @section{
      @h2{Scribbles}
      @ul{
        @(scribble "a free theorem" "free-theorem" "08/25/20")
      }
    }
  }
 }
}