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
  @link[rel:"stylesheet" href:"../highlight/styles/a11y-light.css"]
  @script[src: "../highlight/highlight.pack.js"]
  @script{hljs.highlightAll();}
 }
 @body{
  @article{

   @pre{
    @code[class: "scala"]{
import scala.annotation.tailrec

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

object Main {
  // We have only one action.
  val action = 0
  def to(P: Procc) = (action, P)

  // "Detailed" specification of two-phase commit.
  val twoPC = LTS(
    Set("Init", "C1", "C2", "C12", "A1", "A2", "Commit", "Abort"),
    Map("Init" -> List(to("C1"), to("C2"), to("A1"), to("A2")),
        "C1" -> List(to("C12"), to("A2")),
        "C2" -> List(to("C12"), to("A1")),
        "C12" -> List(to("Commit")),
        "A1" -> List(to("Abort")),
        "A2" -> List(to("Abort"))
    )
  )

  // "Abstract" specification of two-phase commit.
  val twoPCSimpl = LTS(
    Set("InitP", "Procc", "CommitP", "AbortP"),
    Map("InitP" -> List(to("Procc")),
        "Procc" -> List(to("Procc"), to("CommitP"), to("AbortP"))
    )
  )

  def main(args: Array[String]): Unit = {
    val S = new Simil(twoPC, twoPCSimpl)
    for ((p1, p2) <- S.simil.toList.sorted)
      println(s"$p1 ≤ $p2")
  }
}
                          
/*
Output:

A1 ≤ InitP
A1 ≤ Procc
A2 ≤ InitP
A2 ≤ Procc
Abort ≤ AbortP
Abort ≤ CommitP
Abort ≤ InitP
Abort ≤ Procc
C1 ≤ InitP
C1 ≤ Procc
C12 ≤ InitP
C12 ≤ Procc
C2 ≤ InitP
C2 ≤ Procc
Commit ≤ AbortP
Commit ≤ CommitP
Commit ≤ InitP
Commit ≤ Procc
Init ≤ InitP
Init ≤ Procc
*/

    }
   }
  }
 }
}