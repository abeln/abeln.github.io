#lang scribble/html
@(require racket/match)
@(require racket/list)
@(require (only-in (rename-in racket/base (map list-map)) list-map))
@(require scribble/html/extra)
   
@html[lang: "en"]{
 @head{
  @link[rel: "stylesheet" href: "../tufte.css"]
  @script[src: "https://polyfill.io/v3/polyfill.min.js?features=es6"]
  @script[id: "MathJax-script" async:"" src:"https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js"]
 }
 @body{
  @article{
   @section{
    @p{
     @span[class: "newthought"]{This note} defines a notion of @i{similarity} for @i{labelled-transition systems} (LTS) and shows how, by placing certain finiteness conditions
     on the LTS, similarity can be iteratively computed. In the process, we will see how similarity can be a concrete example of the trick for "commuting quantifiers" described in
     @a[href: "https://tildeweb.au.dk/au571806/blog/commuting_quantifiers/"]{Amin Timany's blog}. None of what follows is novel, and is sourced from Davide Sangiorgi's excellent
     @a[href: "https://www.cambridge.org/core/books/introduction-to-bisimulation-and-coinduction/8B54001CB763BAE9C4BA602C0A341D60"]{introduction to coinduction and
      bisimulation}.
    }
   }
   @section{
    @p{
     @span[class: "newthought"]{A labelled-transition system} is a triple \((Pr, Act, \rightarrow)\), where \(Pr\) is the set of @i{processes} (states), \(Act\) is a set of
     @i{actions} (labels), and \( \rightarrow \subseteq Pr \times Act \times Pr \) is the @i{transition relation}. We will write
     \( P \rightarrow_{\mu} Q \) for \( (P, \mu, Q) \).
    }
    @p{A @i{simulation} is a relation \( R \subseteq Pr \times Pr \) such that if \( (P, Q) \in R \), then for all \( P' \) such that \( P \rightarrow_{\mu} P'  \), there exists a \( Q' \) such that
     \( Q \rightarrow_{\mu} Q' \) and \( (P', Q') \in R \).
    }
    @p{@i{Similarity}, denoted by \( \le \), is the union of all simulations.
     When \( P \le Q \) we say that \( Q \) @i{simulates} \( P \) (note the order is reversed). 
     For example, the following LTS models a @a[href:"https://en.wikipedia.org/wiki/Two-phase_commit_protocol"]{two-phase commit} (2PC) protocol with two clients,
     while keeping track of which clients have committed (C) or aborted (A). The transitions are unlabelled because we have only one action (e.g. \( \mu \)):}
    @img[src: "2pc.png" style:"height:300px"]
    @p{If we want to model the protocol at a higher level, we can decide to not keep track of the client state:}
    @img[src: "2pc-simple.png" style:"height:200px"]
    @p{We then need a way to relate the two models: we can use similarity to that effect. We can see that \( Init \le Init' \), all the C and A states are simulated by Procc, \( Commit \le Commit' \), and \( Abort \le Abort' \).
     For example, the sequence \( [Init, C_1, A_2, Abort] \) is simulated by \( [Init', Procc, Procc, Abort'] \).}
   }
   @section{
    @p{
     @span[class: "newthought"]{Working on the complete} @i{powerset lattice} \( \mathcal{P}(Procc \times Procc) \), we can obtain similarity as the greatest @i{fixpoint} of a @i{functional}
     \( F : \mathcal{P}({Procc \times Procc}) \rightarrow \mathcal{P}({Procc \times Procc}) \) given by
     @label[for: "sn-demo" class:"margin-toggle sidenote-number"]
     @input[type:"checkbox" id:"sn-demo" class: "margin-toggle"]
     @span[class: "sidenote"]{The intuition for \( F \) is that it gives us all pairs  \( (P, Q) \) where \( Q \) can simulate  \( P \) @i{for one step} and after that one step @i{we end up in a pair of states in \( R \). } }     
     \[ F(R) = \{ (P, Q) | \forall P', P \rightarrow_\mu P' \implies \exists Q', Q \rightarrow_\mu Q' \land (P', Q') \in R \} \]
     @b{Fact 1. } \( R \) is a simulation iff \( R \) is a post-fixpoint of \( F \) (i.e. \( R \subseteq F(R) \) ).
     @br{}
     @b{Corollary 2. } similarity is  F's greatest fixpoint (follows by @a[href: "https://en.wikipedia.org/wiki/Knaster%E2%80%93Tarski_theorem"]{Knaster-Tarski}).
    }
    @p{
     Moreover, we can stratify similarity through a family of relations \( \{ \le_n \} \) capturing @i{similarity up to \(n\) steps}:                                                                 
     @ul{
      @li{\( \le_0 = Pr \times Pr \)}
      @li{ \( \le_{n + 1} = F(\le_n) \)}
     }
    }
    @p{
     To compute similarity, we'd like to know that \( P \le Q \) iff  \( P \le_n Q \) @i{for all n}; i.e.
     $$ \le = \bigcap_{i \ge 0} \le_i $$
     If so, we could compute \( \le_0, \le_1, \ldots, \le_n, \ldots \)
     Since \( F \) is monotone, then we can stop computing as soon as we reach a fixpoint \( \le_n = F(\le_{n}) = \le_{n + 1} \). In that case
     $$  \le = \bigcap_{i \ge 0} \le_i = \le_n $$
     The fixpoint algorithm can be implemented more or less verbatim (@a[href: "simil-src.html"]{Scala source}).
     For the 2PC models above, we indeed get that \( Init \le Init' \) as expected.
     @label[for: "sn-sim" class:"margin-toggle sidenote-number"]
     @input[type:"checkbox" id:"sn-sim" class: "margin-toggle"]
     @span[class: "sidenote"]{
     The full relation is
     { A1 ≤ Init',
     A1 ≤ Procc,
     A2 ≤ Init',
     A2 ≤ Procc
     Abort ≤ Abort',
     Abort ≤ Commit',
     Abort ≤ Init'
     Abort ≤ Procc,
     C1 ≤ Init',
     C1 ≤ Procc,
     C12 ≤ Init',
     C12 ≤ Procc,
     C2 ≤ Init',
     C2 ≤ Procc,
     Commit ≤ Abort',
     Commit ≤ Commit',
     Commit ≤ Init',
     Commit ≤ Procc,
     Init ≤ Init',
     Init ≤ Procc }
     }
    }
   }
  }
 }
}