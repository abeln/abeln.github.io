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
     [else @span{@elem-join[@(list-map (lambda (p) (@a[href: (first p)]{@(second p)})) urls) ", "]}]))

@; Find a better way to add space betweeen rows
@(define (pad-below row)
  @span{
    @row
    @tr{@td{@br{}} @td{@br{}}}
  })
 
@(define (pub title authors venue urls)
  @(pad-below
    @tr{
      @td{
        @small[@span[style: "color:gray"]{@venue}]
     }
     @td{
       @b{@title}
       @br
       @elem-join[(emph-name authors "Abel Nieto") ", "]
       @br
       @(show-urls urls)
     }
    }
  ))

@(define (trep title authors year urls)
  @(pad-below
   @tr{
    @td{
      @small[@span[style: "color:gray"]{@year}]
    }
    @td{
      @b{@title}
      @br
      @elem-join[(emph-name authors "Abel Nieto") ", "]
      @br
      @(show-urls urls)
    }
  })
)

@(define (thesis title year kind urls)
   @(pad-below
   @tr{
    @td{
      @small[@span[style: "color:gray"]{@year}]
    }
    @td{
      @b{@title} 
      @br
      @small[@span[style: "color:gray"]{@kind}]
      @br
      @(show-urls urls)
    }
 })
)

@(define (memo title file date)
     @tr{
         @td{@small[@span[style: "color:gray"]{@date}]}
         @td{@a[href: @(string-append "scribbles/" @file ".html")]{@title} }
     }
   )

@doctype{html}

@html[lang: "en"]{
 @head{
  @meta[charset: "utf-8"]
  @link[rel: "stylesheet" href: "tufte.css"]
  @script[src: "https://polyfill.io/v3/polyfill.min.js?features=es6"]
  @script[id: "MathJax-script" async:"" src:"https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"]
 }
 @body{
  @article{
    @h1{Abel Nieto}
    @span[style: "color:gray"]{[@(show-urls '(("papers/cv.pdf" "cv") ("mailto:abeln@cs.au.dk" "email") ("https://github.com/abeln" "github") ("https://www.linkedin.com/in/abel-nieto-056768242/" "linkedin")))]}
    @; Intro section 
    @section{
      @p{
         Hello! My name is Abel, and I’m a PhD student at Aarhus University, where
         I'm a member of the @a[href: "https://cs.au.dk/research/logic-and-semantics/"]{Logic and Semantics} group.
         My advisor is @a[href: "https://cs.au.dk/~birke/"]{Lars Birkedal}.
       }
       @p{
         I work on @a[href: "https://iris-project.org/"]{formal verification} of distributed systems. I'm also interested in programming language design, type theory,
         program analysis, and compilers.
       }
       @p[style:"color:red"]{
          I expect to complete my PhD by July 2023. I am interested in an applied scientist or formal methods engineer position in industry, in the fields of formal verification, programming language design, compilers, type systems, and static analysis.
          I am affiliated with Aarhus University, but live in Waterloo, Canada. Do get in touch if you know of any opportunities in these areas!
      }
    }
    @; Publications
    @section{
      @h3{Publications}
      @span[style: "color:gray"]{[@(show-urls '(("https://scholar.google.ca/citations?hl=en&user=Z9nsk2AAAAAJ" "google scholar") ("https://dblp.org/pid/205/2896.html" "dblp")))]}
      @h4{peer-reviewed}
      @table{
        @colgroup{
          @col[span: "1" style: "width: 15%;"]
          @col[span: "1" style: "width: 85%;"]
        }
        @(pub "Distributed Causal Memory: Modular Specification and Verification in Higher-Order Distributed Separation Logic"
              '("Léon Gondelman" "Simon Oddershede Gregersen" "Abel Nieto" "Amin Timany" "Lars Birkedal")
              "POPL '21"
              '(("papers/ccdb-final.pdf" "pdf")))
        @(pub "Blame for Null"
              '("Abel Nieto" "Marianna Rapoport" "Gregor Richards" "Ondřej Lhoták")
              "ECOOP '20"
              '(("papers/blame-final.pdf" "pdf")
                ("https://github.com/abeln/null-calculus" "code")))
        @(pub "Scala with Explicit Nulls"
              '("Abel Nieto" "Yaoyu Zhao" "Ondřej Lhoták" "Angela Chang" "Justin Pu")
              "ECOOP '20"
              '(("papers/explicit-nulls-final.pdf" "pdf")
                ("https://github.com/abeln/dotty/tree/dotty-explicit-nulls-evaluation" "code")))
        @(pub "Towards Algorithmic Typing for DOT (Short Paper)"
              '("Abel Nieto")
              "SCALA '17"
              '(("papers/algo-dot.pdf" "pdf")
                ("https://www.youtube.com/watch?v=uokvc1Do_nM" "talk")))
        }
      @h4{technical reports}
      @table{
        @colgroup{
          @col[span: "1" style: "width: 15%;"]
          @col[span: "1" style: "width: 85%;"]
        }
        @(trep "Trillium: Unifying Refinement and Higher-Order Distributed Separation Logic"
               '("Amin Timany" "Simon Oddershede Gregersen" "Léo Stefanesco" "Léon Gondelman" "Abel Nieto" "Lars Birkedal")
               2021
               '(("https://arxiv.org/abs/2109.07863" "pdf")))
        @(trep "Tamarin: Concolic Disequivalence for MIPS"
             '("Abel Nieto")
             2018
             '(("https://arxiv.org/pdf/1801.02571.pdf" "pdf")))
        @(trep "Towards Algorithmic Typing for DOT"
             '("Abel Nieto")
             2017
             '(("https://arxiv.org/abs/1708.05437" "pdf")))
      }
      @h4{theses}
      @table{
        @colgroup{
          @col[span: "1" style: "width: 15%;"]
          @col[span: "1" style: "width: 85%;"]
        }
        @(thesis "Scala with Explicit Nulls"
                  "2019"
                  "Master thesis, University of Waterloo"
                 '(("https://uwspace.uwaterloo.ca/handle/10012/15364" "pdf")))
      }
      @h4{memos}
      @table{
        @colgroup{
          @col[span: "1" style: "width: 15%;"]
          @col[span: "1" style: "width: 85%;"]
        }
        @(memo "Why Least Fixpoints" "least-fp" "04/21")
        @(memo "Simulations and Commuting Quantifiers" "quantifiers" "03/21")
        @(memo "A Free Theorem" "free-theorem" "08/20")
      }
    }
  }
 }
}