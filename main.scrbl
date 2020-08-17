#lang scribble/html
@(require scribble/html/extra)

@(define (pub title authors venue)
  @li{
    @b{@title}
    @br
    @authors
    @br
    @small[@span[style: "color:gray"]{@venue}]
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
              "Abel Nieto, Marianna Rapoport, Gregor Richards, Ondřej Lhoták"
              "To appear at ECOOP 2020")
        @(pub "Scala with Explicit Nulls"
              "Abel Nieto, Yaoyu Zhao, Ondřej Lhoták, Angela Chang, Justin Pu"
              "To appear at ECOOP 2020")
        @(pub "Towards Algorithmic Typing for DOT (Short Paper)"
              "Abel Nieto"
              "Scala Symposium 2017")
        }
      }
    }
  }
 }