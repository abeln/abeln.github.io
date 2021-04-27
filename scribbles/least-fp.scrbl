#lang scribble/html
@(require racket/match)
@(require racket/list)
@(require (only-in (rename-in racket/base (map list-map)) list-map))
@(require scribble/html/extra)

@(define math-ctr 1)

@(define (get-math-ctr-and-incr)
   (define c math-ctr)
   (set! math-ctr (+ 1 math-ctr))
   c)

@(define (mathdef s)
   @u[@b[(format "~a ~a." s (get-math-ctr-and-incr))]])

@(define (theorem)
   (mathdef "Theorem"))

@(define (lemma)
   (mathdef "Lemma"))

@(define (fact)
   (mathdef "Fact"))

@(define (corollary)
   (mathdef "Corollary"))

@(define (definition)
   (mathdef "Definition"))

   
@html[lang: "en"]{
 @head{
  @link[rel: "stylesheet" href: "../tufte.css"]
  @script[src: "https://polyfill.io/v3/polyfill.min.js?features=es6"]
  @script[id: "MathJax-script" async:"" src:"https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"]
  @link[rel:"stylesheet" href:"../highlight/styles/a11y-light.css"]
  @script[src: "../highlight/highlight.pack.js"]
  @script{hljs.highlightAll();}
 }
 @body{
  @article{
   @h1{Why Least Fixpoints}
   @h3{April, 2021}
   @section{
    @p{
     @span[class: "newthought"]{Why does denotational semantics} care about @i{least} fixpoints, as opposed to say greatest or some other fixpoints.
     Answer: because it's least fixpoints that capture our operational intuitions of code. Read on for an example.
    }
   }
   @section{
    @p{
      @span[class: "newthought"]{In denotational semantics} we're interested in a @i{denotation} function that maps program terms to mathematical functions.
      For example, we might say that the denotation of the statement @code[class: "C"]{A := A + 1} is the function on stores that maps location @code[class: "C"]{A}
      to its successor
      @label[for: "store-upd" class:"margin-toggle sidenote-number"]
      @input[type:"checkbox" id:"store-upd" class: "margin-toggle"]
      @span[class: "sidenote"]{ I use the following notation for store updates: \( s' = s[A \rightarrow v] \) is the store such that \( s'(A) = v \) and \( s'(l) = s(l) \) for
      \( l \neq A \). }
      :
      $$ [[ A := A + 1 ]] = \lambda s. s[A \rightarrow s(A) + 1] $$
      To represent nontermination we use a bottom element \( \bot \), so denotations are functions \( Store_{\bot} \rightarrow Store_{\bot} \), where \( Store = Id \rightarrow Nat \)
      @label[for: "pointed-cpo" class:"margin-toggle sidenote-number"]
      @input[type:"checkbox" id:"pointed-cpo" class: "margin-toggle"]
      @span[class: "sidenote"]{ \( Store_{\bot} \) then contains all the functions in \( Store \), plus \( \bot \). }.
      This way, an infinite loop is denoted by the function that sends @i{any} store to \( \bot \):
      $$ [[ while\ (true)\ do\ skip ]] = \lambda s. \bot $$
    }
    @p{
       Fixpoints arise naturally when looking at denotations of loops. Our operational intuition of loops motivates the desideratum
       $$ [[ while \ (B)\  do \ S ]] = [[ if\ (B)\ then\ (S;\ while\ (B)\ do\ S)\  else\ skip ]] $$
       Now let \( L = while \ (B)\  do \ S \), getting
       $$ [[ L ]] = [[ if\ (B)\ then (S; L) else \ skip ]] $$
       Computing the denotations (which I haven't explained how to do) we get
       $$ [[ L ]] = \lambda s. if\ ([[ B ]] s)\ then\ [[ L ]] ([[ S ]] s)\ else\  s $$
       The important part is that \( [[L]] \) appears in both sides of the equation.
       Here we do the usual trick where instead of the equation above we write the corresponding @i{functional}
       $$ F = \lambda f. \lambda s. if\ ([[ B ]] s)\ then\ f([[ S ]] s)\ else\  s $$
       Notice the denotation \( [[ L ]] \) we're looking for is such that
       $$ [[ L ]] = F([[ L ]]) $$
       a fixpoint!
    }
   }
   @section{
    @p{
     @span[class: "newthought"]{Ok so now we know} that fixpoints are useful for modelling loops, but why do we care specifically about @i{least} fixpoints?
     The reason is that there's a @a[href: "https://en.wikipedia.org/wiki/Kleene_fixed-point_theorem"]{theorem} that tells us that least fixpoints can be computed in
     a way that's compatible with the operational semantics of loops. But it's also interesting to examine what goes @i{wrong} if we were to use e.g. @i{greatest} fixpoints.
    }
    @p{
     Consider the loop @code{while (A = 0) do skip } (call it \( L \)). Operationally, we would say that the loop terminates iff the initial value of \( A \) is non-zero.
     Denotationally, we'd like to say that \( [[ L ]] \) is the function that sends every store where \( A \) is zero to \( \bot \), and leaves all other stores unchanged:
     $$ [[ L ]] = \lambda s.\ if\ ([[ A = 0 ]] s)\ then\ \bot\ else\ s $$
     Indeed, this is a fixpoint, because
     $$ \begin{align*}
     F([[ L ]]) &= \lambda s.\ if ([[ A = 0 ]] s)\ then\ [[ L ]] ([[ skip ]] s)\ else\ s \\
     &= \lambda s.\ if ([[ A = 0 ]] s )\ then\ [[ L ]](s)\ else\ s \\
     &= \lambda s.\ if ([[ A = 0 ]] s )\ then\ (if ([[ A = 0 ]]\ then\  \bot \ else \ s)\ else\ s \\
     &= \lambda s.\ if ([[ A = 0 ]] s )\ then\ \bot\ else\ s \\
     &= [[ L ]]
     \end{align*}
     $$
    }
    @p{
       But the above is not the @i{only} fixpoint. Consider a denotation that makes \( L \) the identity:
       $$ [[ L ]]' = \lambda s. s $$
       This is also a fixpoint, because
       $$ \begin{align*}
       F([[ L ]]') &= \lambda s.\ if ([[ A = 0 ]] s)\ then\ [[ L ]]' ([[ skip ]] s)\ else\ s \\
       &= \lambda s.\ if ([[ A = 0 ]] s )\ then\ [[ L ]]'(s)\ else\ s \\
       &= \lambda s.\ if ([[ A = 0 ]] s )\ then\ s\ else\ s \\
       &= \lambda s. s \\
       &= [[ L ]]'
       \end{align*}
       $$
       Additionally, we have \( [[ L ]] < [[ L' ]] \) (although I haven't defined what @i{less than} means in this context) because the former sends stores
       with \( A = 0 \) to \( \bot \), whereas the latter leaves them unchanged. But this second interpretation of the loop as the identity is clearly wrong!
       Moral of the story: we really do want least fixpoints, and not just any old fixpoint.
    }
   }
   @section{
    @h2{References}
    @ul{
     @li{Schmidt, David A. Denotational semantics: a methodology for language development. William C. Brown Publishers, 1986.}
     @li{Winskel, Glynn. The formal semantics of programming languages: an introduction. MIT press, 1993.}
    }
   }
  }
 }
}