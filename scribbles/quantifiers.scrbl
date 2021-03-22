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
   @h1{Simulations and Commuting Quantifiers}
   @h3{March, 2021}
   @section{
    @p{
     @span[class: "newthought"]{How sloppy can we be with Math} and still be right? Amin Timany recently wrote an interesting @a[href: "https://tildeweb.au.dk/au571806/blog/commuting_quantifiers/"]{blog post}
      about this. Amin is interested in situations when it's ok to @i{commute the order of quantifiers} in a proposition and still arrive at something that's valid.
      Formally, if we know
      $$ \forall x \in A. \exists y \in B. P(x, y) $$
      when can we conclude
      $$ \exists y \in B. \forall x \in A. P(x, y) $$
      This is of course not always true: every person has a parent
      @label[for: "ex1" class:"margin-toggle sidenote-number"]
      @input[type:"checkbox" id:"ex1" class: "margin-toggle"]
      @span[class: "sidenote"]{\( \forall x \in Person. \exists y \in Person. parent(x, y) \)}
      but no one is a parent to everyone
      @label[for: "ex2" class:"margin-toggle sidenote-number"]
      @input[type:"checkbox" id:"ex2" class: "margin-toggle"]
      @span[class: "sidenote"]{ \( \exists y \in Person. \forall x \in Person. parent(x, y) \)}.
      But nor is it @i{always wrong} to commute quantifiers: everyone has an ancestor, but it is at least plausible that @a[href: "https://en.wikipedia.org/wiki/Adam_and_Eve"]{someone} is an ancestor to everyone.
      While reading Davide Sangiorgi's excellent
      @a[href: "https://www.cambridge.org/core/books/introduction-to-bisimulation-and-coinduction/8B54001CB763BAE9C4BA602C0A341D60"]{@i{Introduction to Bisimulation and
      Coinduction}} I was only happy to find out that the notion of @i{simulation between labelled-transition systems}
      @label[for: "lts" class:"margin-toggle sidenote-number"]
      @input[type:"checkbox" id:"lts" class: "margin-toggle"]
      @span[class: "sidenote"]{ These transition systems are useful for, among many other purposes, modelling distributed systems.
      In this context, simulations give us a way to relate a system specification to another, more abstract one. More details in Leslie Lamport's @a[href: "https://lamport.azurewebsites.net/tla/book.html"]{@i{Specifying Systems}} book. }
      is a nice concrete example of why we would ever care
      about commuting quantifiers. This note shows how by placing certain finiteness conditions on transition systems, we can @i{compute} simulations. The correctness of the computation
      is given by our ability to commute quantifiers.
    }
   }
   @section{
    @p{
     @span[class: "newthought"]{A labelled-transition system} is a triple \((Pr, Act, \rightarrow)\), where \(Pr\) is the set of @i{processes} (states), \(Act\) is a set of
     @i{actions} (labels), and \( \rightarrow \subseteq Pr \times Act \times Pr \) is the @i{transition relation}. We will write
     \( P \rightarrow_{\mu} Q \) for \( (P, \mu, Q) \in \rightarrow \).
    }
    @p{A @i{simulation} is a relation \( R \subseteq Pr \times Pr \) such that if \( (P, Q) \in R \), then for all \( P' \) such that \( P \rightarrow_{\mu} P'  \), there exists a \( Q' \) such that
     \( Q \rightarrow_{\mu} Q' \) and \( (P', Q') \in R \).
    }
    @p{@i{Similarity}, denoted by \( \le \), is the union of all simulations.
     When \( P \le Q \) we say that \( Q \) @i{simulates} \( P \) (note the order is reversed). 
     For example, the following LTS models a @a[href:"https://en.wikipedia.org/wiki/Two-phase_commit_protocol"]{two-phase commit} (2PC) protocol with two clients,
     while keeping track of which clients have committed (C) or aborted (A). The transitions are unlabelled because we have only one action:}
    @img[src: "2pc.png" style:"height:300px"]
    @p{If we want to model the protocol at a higher level, we can decide to not keep track of the client state:}
    @img[src: "2pc-simple.png" style:"height:200px"]
    @p{We then need a way to relate the two models: we can use similarity to that effect. We can see that \( Init \le Init' \), all the C and A states are simulated by Procc, \( Commit \le Commit' \), and \( Abort \le Abort' \).
     For example, the sequence \( [Init, C_1, A_2, Abort] \) is simulated by \( [Init', Procc, Procc, Abort'] \).}
   }
   @section{
    @p{
     @span[class: "newthought"]{Working in the complete} @i{powerset lattice} \( \mathcal{P}(Pr \times Pr) \), we can obtain similarity as the greatest @i{fixpoint} of a @i{functional}
     \( F : \mathcal{P}({Pr \times Pr}) \rightarrow \mathcal{P}({Pr \times Pr}) \) given by
     @label[for: "sn-demo" class:"margin-toggle sidenote-number"]
     @input[type:"checkbox" id:"sn-demo" class: "margin-toggle"]
     @span[class: "sidenote"]{The intuition for \( F(R) \) is that it gives us all pairs  \( (P, Q) \) where \( Q \) can simulate  \( P \) @i{for one step} and after that one step @i{we end up in a pair of states in \( R \). } }     
     \[ F(R) = \{ (P, Q) | \forall P', P \rightarrow_\mu P' \implies \exists Q'. Q \rightarrow_\mu Q' \land (P', Q') \in R \} \]
     @p{
     @fact{} \( F \) is @i{monotone}.
     @label[for: "sn-mono" class:"margin-toggle sidenote-number"]
     @input[type:"checkbox" id:"sn-mono" class: "margin-toggle"]
     @span[class: "sidenote"]{This means that if \( S \subseteq R \) then \( F(S) \subseteq F(R) \). }
     }
     @p{
     @fact{} \( R \) is a simulation iff \( R \) is a post-fixpoint of \( F \) (i.e. \( R \subseteq F(R) \) ).
     }
     @p{
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
     Since \( F \) is monotone, then we can stop computing as soon as we reach a fixpoint \( \le_n = F(\le_{n}) = \le_{n + 1} \), In that case
     $$  \le = \bigcap_{i \ge 0} \le_i = \le_n $$
     This is justified by the following lemma:
    }
    @p{
     @lemma{} For \( i \ge 0 \), if \( P \le_{i + 1} Q \), then \( P \le_i Q \).
    }
    @p{
     @b{@u{Proof.}} Intuitively, this makes sense. If \( Q \) can simulate \( P \) for \( i + 1 \) steps, then surely it can also simulate it
     for \( i \) steps. Formally, we have to show that \( \le_{i + 1} \subseteq \le_i \).
     Note that
     $$ \le_1 \subseteq Pr \times \Pr = \le_0 $$
     Since \( F \) is monotone we can (repeatedly) apply it on both sides to get
     $$ \begin{align}
        \le_2 = F(\le_1) \subseteq F(\le_0) = \le_1 \\
        \le_3 = F(\le_2) \subseteq F(\le_1) = \le_2 \\
        \ldots
        \end{align}
     $$
     The proof follows by induction. \( \blacksquare \)
    }
    @p{
       @corollary{} If \( n \ge m \), then \( P \le_n Q \) implies \( P \le_m Q \).
    }
   }
   @section{
   @p{
     @span[class: "newthought"]{The fixpoint algorithm} can be implemented more or less verbatim (below in Scala, full source @a[href: "simil-src.html"]{here}):

   @pre{
    @code[class: "scala"]{
// Compute the similarity relation on nodes of a
// labelled-transition system (LTS) via fixpoints.

object Trans {
  // LTS processes and actions
  type Procc = String 
  type Act = Int

  // A labelled-transition system is a set of processes (nodes)
  // and transitions between them.
  case class LTS(
    procc: Set[Procc],
    trans: Map[Procc, List[(Act, Procc)]])

  // A relation is a set of pairs of processes.
  type Rel = Set[(Procc, Procc)]
}

import Trans._

class Simil(L1: LTS, L2: LTS) {
  // The _functional_ computes the pairs (p, q) where
  // q simulates p for one step and we end up in elements
  // in R.
  def funct(R : Rel): Rel = {
    for {
      s1 <- L1.procc
      s2 <- L2.procc
      if L1.trans.getOrElse(s1, List()).forall(
        { case (a1, p1) =>
          // s1 ->_a1 p1
          L2.trans.getOrElse(s2, List()).exists(
            { case (a2, p2) =>
              // s2 ->_a2 p2
              a2 == a1 && R.contains(p1, p2)  })
        })
    } yield (s1, s2)
  }

  // Compute the fixpoint of a function f from the sequence
  // [R, f(R), f(f(R)), ...]
  @"@"tailrec
  private def fixpoint(R : Rel, f : Rel => Rel): Rel = {
    val next = f(R)
    if (next == R) R else fixpoint(next, f)
  }

  // Compute the similarity relation between processes in
  // two LTSs (i.e. which processes in the second LTS simulate
  // the ones in the first).
  val simil: Rel = {
    // Initially, consider all pairs of processes.
    var R0: Rel = for {
      p1 <- L1.procc
      p2 <- L2.procc
    } yield (p1, p2)
    // Now iterate until we reach a fixpoint.
    fixpoint(R0, funct)
  }
}
   }}}
   
  @p{For the 2PC models above, we indeed get that \( Init \le Init' \) as expected.
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
     C12 ≤ W,
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
   @section{
    @p{@span[class: "newthought"]{Unfortunately the method above} doesn't always work. In the example below, \( A \) we can take \( n \) a-steps @i{for any} \( n \),
     so \( C \le_n A \) and \( (C, A) \in \bigcap_{ i \ge 0} \le_i \). However, @i{\( A \) cannot simulate \( C \)} because \( C \) can take infinitely many steps whereas \( A \) needs to "commit" to
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
    $$ \forall i. \exists Q'. Q \rightarrow_\mu Q' \land (P', Q') \in \le_i $$
    But we need
    $$ \exists Q'. \forall i. Q \rightarrow_\mu Q' \land (P', Q') \in \le_i $$
    Of course, we know we can't simply swap the quantifiers, which is consistent with the counterexample we saw above.
    In the counterexample, process \( A \) had infinitely-many outgoing transitions, so one (not very intuitive) question to ask is whether restricting the LTS to being @i{finitely branching} solves the problem (it does).
    }
    @p{
    @definition{} An LTS is finitely branching if for every process \( P \) the set \( \{ (\mu, Q) | P \rightarrow_\mu Q \in \rightarrow \} \) is finite.
    }
    @p{
    We now finally get to the meat of the matter: if the LTS is finitely branching, then we can exchange the quantifiers.
    }
    @p{
    @lemma{} If the underlying LTS is finitely branching, then
    $$ \forall i. \exists Q'. Q \rightarrow_\mu Q' \land (P', Q') \in \le_i $$
    implies
    $$ \exists Q'. \forall i. Q \rightarrow_\mu Q' \land (P', Q') \in \le_i $$
    @b{@u{Proof.}}
    Let \( M = \{ Q\ | Q \rightarrow_\mu Q' \in \rightarrow \} \). Since the LTS is finitely branching, then \( M \) is finite.
    From the assumption, we can construct a function \( f(i) = Q_i \) that assigns to every index \( i \) an element \( Q_i \in M \) such that \( Q \rightarrow_\mu Q_i \land (P', Q_i) \in \le_i \).
    Now define the @i{fiber} \( f^{-1}(e) \) of an element \( e \) to be the inverse image of the singleton set containing \( e \):
    $$ f^{-1}(Q') = \{ i | f(i) = Q' \} $$
    Notice that the set of natural numbers can be partitioned as the union of the fibers of elements of \( M \):
    $$ \mathbb{N} = \bigcup_{Q' \in M} f^{-1}(Q') $$
    Now look at the cardinalities on each side of the equation above. \( \mathbb{N} \) is infinite, and there are finitely many \( Q' \in M \).
    This means that at least one of the elements has an @i{infinite} fiber. Let \( Q' \) be one such element.
    Now consider an arbitrary index \( i \). Since \( f^{-1}(Q') \) is infinite, there exists a \( j > i \) such that \( j \in f^{-1}(Q') \),
    meaning that \( f(j) = Q' \).
    In turn, this means that
    $$ Q \rightarrow_\mu Q' \land (P', Q') \in \le_i $$
    Since \( i \) was arbitrarily chosen, we get
    $$ \forall i, Q \rightarrow_\mu Q' \land (P', Q') \in \le_i $$
    which is allows us to instantiate the existential in our goal. \( \blacksquare \)
   }
   }
   @section{
    @p{
     @span[class: "newthought"]{The abstract view} of Lemma 7 above is given in Theorem 1 (Regular Quantification) of @a[href: "https://tildeweb.au.dk/au571806/blog/commuting_quantifiers/"]{Amin's blog post}:
     @blockquote{
      @p{
       Let A be a regular ordinal, [...] and B be a set with strictly smaller cardinality [...].
       The following holds for any \( P \) that is downwards closed with respect to the
       relation on A:
       $$ (\forall x \in A. \exists y \in B. P(x, y) ) \implies \exists y \in B. \forall x \in A. P(x, y) $$
     }}
    }
    @p{
     Contrast with a version of Lemma 7 massaged to highlight the parallels
     $$ ( \forall i \in \mathbb{N}. \exists Q' \in succ(Q, \mu). \mathcal{S}(i, Q') ) \implies  \exists Q' \in succ(Q, \mu). \forall i \in \mathbb{N}. \mathcal{S}(i, Q') $$
     where
     $$ \begin{align}
        succ(Q, \mu) &= \{ Q' | Q \rightarrow_\mu Q' \} \\
        \mathcal{S}(i, Q') &= (P', Q') \in \le_i
        \end{align}
     $$
    }
    @p{
     In order to use Theorem 1, we need
     @ul{
      @li{ @i{\( \mathbb{N} \) must be a @a[href: "https://en.wikipedia.org/wiki/Regular_cardinal"]{regular ordinal}}. For our purposes, this means the following: suppose we have an @i{unbounded} subset \( S \) of \( \mathbb{N} \)
           (i.e. for any natural number \( n \) no matter how large, we can always find an element \( e \in S \) such that \( e > n \)). Then we need to show
           there exists an @i{injective} function \( f : \mathbb{N} \rightarrow S \).
           We can recursively construct one such function. We will set \( f(0) \) to an arbitrary element of \( S \). For the recursive case,
           we are given \( f(n - 1) \) and have to define \( f(n) \). Since \( S \) is unbounded, there's an element \( e \in S \) such that \( e > f(n - 1) \). We set \( f(n) = e \).
           It's easy to see that if \( n < m \) then \( f(n) < f(m) \); this means \( f \) is injective as needed. \( \blacksquare \)
      }
      @li{ @i{\( succ(Q, \mu) \) must have strictly smaller cardinality than  \( \mathbb{N} \)}. This is easy, because since the LTS is finitely branching \( succ(Q, \mu) \) must be finite, and \( \mathbb{N} \) is infinite.  \( \blacksquare \)}
      @li{ @i{\( \mathcal{S}(i, Q') \) is downwards-closed}. Here we need to show that if \( n \ge m \) then
      $$ P' \le_n Q' \implies P' \le_m Q' $$
      This is precisely the previously shown Corollary 5. \( \blacksquare \)
      }
     }
    }
   }
   @section{
            @h2{References}
            @ul{
            @li{Sangiorgi, Davide. Introduction to Bisimulation and Coinduction. Cambridge University Press, 2011.}
            @li{Timany, Amin. Commuting Quantifiers. @a[href: "https://tildeweb.au.dk/au571806/blog/commuting_quantifiers/"]{https://tildeweb.au.dk/au571806/blog/commuting_quantifiers/}.}
            @li{Lamport, Leslie. Specifying systems. Vol. 388. Boston: Addison-Wesley, 2002. @a[href: "https://lamport.azurewebsites.net/tla/book.html"]{https://lamport.azurewebsites.net/tla/book.html}}
    }
   }
  }
 }
}