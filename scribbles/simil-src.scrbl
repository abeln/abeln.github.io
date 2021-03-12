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
  @link[rel:"stylesheet" href:"https://cdnjs.cloudflare.com/ajax/libs/highlight.js/10.6.0/styles/default.min.css"]
  @script[src: "https://cdnjs.cloudflare.com/ajax/libs/highlight.js/10.6.0/highlight.min.js"]
  @script{hljs.highlightAll();}
 }
 @body{
  @article{

   @pre{[
    @code[class: "scala"]{
     // Compute similarity between two labelled-transition systems using
     // iteration until fixpoint.
     object Main {

      type Procc = String 
      type Act = Int

      case class LTS(
      procc: Set[Procc],
      trans: Map[Procc, List[(Act, Procc)]])

      type Rel = Set[(Procc, Procc)]

      def F(L1 : LTS, L2 : LTS, R: Rel): Rel = {
       for {
        s1 <- L1.procc
        s2 <- L2.procc
        if L1.trans.getOrElse(s1, List()).forall(
        { case (a1, p1) =>
         L2.trans.getOrElse(s2, List()).exists(
         { case (a2, p2) => a2 == a1 && R.contains(p1, p2)  })
         })
        } yield (s1, s2)
      }

      def simil(L1: LTS, L2: LTS): Rel = {
       var res: Rel = for {
        p1 <- L1.procc
        p2 <- L2.procc
        } yield (p1, p2)
       var done = false
       while (!done) {
        val next = F(L1, L2, res)
        if (next == res) done = true
        else res = next
       }
       res
      }

      val action = 0                 // unique action
      def to(P: Procc) = (action, P)

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

      val twoPCSimpl = LTS(
      Set("InitP", "Procc", "CommitP", "AbortP"),
      Map("InitP" -> List(to("Procc")),
          "Procc" -> List(to("Procc"), to("CommitP"), to("AbortP"))
        )
      )

      def main(args: Array[String]): Unit = {
       for ((p1, p2) <- simil(twoPC, twoPCSimpl).toList.sorted)
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