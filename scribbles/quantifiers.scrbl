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
     @p{
     @fact{} \( R \) is a simulation iff \( R \) is a post-fixpoint of \( F \) (i.e. \( R \subseteq F(R) \) ).
     @br{}
     @corollary{} similarity is  F's greatest fixpoint (follows by @a[href: "https://en.wikipedia.org/wiki/Knaster%E2%80%93Tarski_theorem"]{Knaster-Tarski}).
     }
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
    @p{Unfortunately the method above doesn't always work. In the example below, \( A \) we can take \( n \) a-steps @i{for any} \( n \),
     so \( C \le_n A \) and \( (C, A) \in \bigcap_{ i \ge 0} \le_i \). However, \( A \) @i{cannot} simulate \( C \) because \( C \) can take infinitely many steps whereas \( A \) needs to "commit" to
     one of the \( B_i \), and from then on it can only take a finite number of steps. }
    @img[src: "sim-inf.png" style:"height:200px" float:"left"]
    @img[src: "sim-n.png" style:"height:200px"]
    @p{
    To see what the problem is, it helps to try to carry out the proof that \( \le = \bigcap_{i \ge 0} \le_i \) and see where it breaks.
    For this, we need to show that \( \le \subseteq \bigcap_{i \ge 0}  \) and \( \bigcap_{i \ge 0} \subseteq \le \). The first goal goes through without problems.
    Notice that
    $$ \begin{align}
     \le & \subseteq Pr \times Pr &= \le_0 \\
     \le = F(\le) & \subseteq F(\le_0) &= \le_1 \\
     \le = F(\le) & \subseteq F(\le_1) &= \le_2 \\
     \ldots & &
    \end{align} $$
    Using the fact that \( \le \) is a fixpoint and \( F \) is monotone we can proceed by induction to show that \( \le \subseteq \le_n \) for all \( n \), and
    the result follows.
    }
    @p{
    It's the second goal that gives us trouble. We need to show that \( \bigcap_{i \ge 0} \le_i \subseteq \le \). Since similarity is the largest simulation,
    it's enough to show that  \( \bigcap_{i \ge 0} \le_i \) is a simulation. That is, given that \( (P, Q) \in \bigcap_{i \ge 0} \le_i \) and assuming that \( P \rightarrow_\mu P' \), we
    have to show that there exists a Q' such that \( Q \rightarrow_\mu Q\ \) and \( (Q, Q') \in \bigcap_{i \ge 0} \le_i \). Because  \( (P, Q) \in \bigcap_{i \ge 0} \le_i \) we know that @i{for each \(i\)}
    we can find a \( Q'_i \) such that \( Q \rightarrow_\mu Q'_i \) and \( (P', Q'_i ) \in \le_i \). That is, we know
    $$ \forall i, \exists Q', Q \rightarrow_\mu Q' \land (P', Q') \in \le_i $$
    But we need
    $$ \exists Q', \forall i, Q \rightarrow_\mu Q' \land (P', Q') \in \le_i $$
    Of course, we know we can't simply swap the quantifiers, which is consistent with the counterexample we saw above.
    In the counterexample, process \( A \) had infinitely-many outgoing transitions, so one (not very intuitive) question to ask is whether restricting the LTS to being @i{finitely branching} solves the problem.
    }
    @p{
    @definition{} An LTS is finitely-branching if for every process \( P \) the set \( \{ (\mu, Q) | P \rightarrow_\mu Q \in \rightarrow \} \) is finite.
    We now finally get to the meat of the matter: if the LTS is finitely branching, then we can exchange the quantifiers.
    }
    @p{
    @lemma{} If the underlying LTS is finitely-branching, then
    $$ \forall i, \exists Q', Q \rightarrow_\mu Q' \land (P', Q') \in \le_i $$
    implies
    $$ \exists Q', \forall i, Q \rightarrow_\mu Q' \land (P', Q') \in \le_i $$
    @b{@u{Proof.}}
    }
   }
  }
 }
}