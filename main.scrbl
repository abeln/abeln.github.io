#lang scribble/html
@(require racket/match)
@(require racket/list)
@(require (only-in (rename-in racket/base (map list-map)) list-map))
@(require scribble/html/extra)

@; TODO: replace with standard map
@(define (emph-name names name)
   (list-map (lambda (n) (if (equal? n name) @em{@n} n)) names))

@(define (elem-join lst sep)
   (match lst
     ['() '()]
     [(cons e lst)
      (cond
        [(empty? lst) (cons e lst)]
        [else (cons e (cons sep (elem-join lst sep)))])]))

@(define (pub title authors venue)
  @li{
    @b{@title}
    @br
    @elem-join[(emph-name authors "Abel Nieto") ", "]
    @br
    @small[@span[style: "color:gray"]{@venue}]
  }
)

@(define (tr title authors urls)
  @li{
    @b{@title}
    @br
    @elem-join[(emph-name authors "Abel Nieto") ", "]
  }
)   

@doctype{html}

@html[lang: "en"]{
 @head{
  @link[rel: "stylesheet" href: "tufte.css"]
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
              "To appear in ECOOP 2020")
        @(pub "Scala with Explicit Nulls"
              '("Abel Nieto" "Yaoyu Zhao" "Ondřej Lhoták" "Angela Chang" "Justin Pu")
              "To appear in ECOOP 2020")
        @(pub "Towards Algorithmic Typing for DOT (Short Paper)"
              '("Abel Nieto")
              "Scala Symposium 2017")
        }
      }
      @h3{technical reports}
      @ol{
        @(tr "Tamarin: Concolic Disequivalence for MIPS"
             '("Abel Nieto")
             '(("https://arxiv.org/pdf/1801.02571.pdf" ".pdf")))
      }
      @h3{thesis}
    }
  }
 }