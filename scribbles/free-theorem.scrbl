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
    @p{
       @b{Theorem.} If \(\cdot; \cdot \vdash e : \forall \alpha. ((\tau \rightarrow \alpha) \rightarrow \alpha)\) and
       \( \cdot; \cdot \vdash k : \tau \rightarrow \tau_k \), then \( \cdot; \cdot \vdash e[\tau_k] k \approx k (e[\tau] \lambda x: \tau.x) : \tau_k \).
    }
    @p{
       @b{Proof.} From \(\cdot; \cdot \vdash e : \forall \alpha. ((\tau \rightarrow \alpha) \rightarrow \alpha)\) we get
       \( \cdot; \cdot \vdash e \approx e : \forall \alpha. ((\tau \rightarrow \alpha) \rightarrow \alpha) \).
       @br{}
       After unfolding definitions, this means that \(e\) steps to \( \Lambda \alpha. e' \) such that
       \( (\Lambda \alpha. e', \Lambda \alpha. e') \in V[\forall \alpha. ((\tau \rightarrow \alpha) \rightarrow \alpha)]_\emptyset \).
       @br{}
       We pick \(\sigma = [\alpha \mapsto (\tau_k, \tau, R])\), where \(R\) is defined as
       \[ R = \{ (v_k, v_\tau) | \forall v_w. (v_w, v_\tau) \in V[\tau]_\emptyset \implies (v_k, k v_w) \in E[\tau_k]_\emptyset \} \]
       We get \( (e'[\tau_k / \alpha], e'[\tau / \alpha]) \in E[(\tau \rightarrow \alpha) \rightarrow \alpha]_\sigma \), from where we obtain values \((v_k, v_\tau) \in
       V[(\tau \rightarrow \alpha) \rightarrow \alpha]_\sigma \)
       such that
       \( e[\tau_k / \alpha] \rightarrow^* v_k \) and
       \( e[\tau / \alpha] \rightarrow^* v_\tau \).
       @br
       @br
       Now we use the following helper lemma and its corollary.
       @br
       @b{Lemma.} \( (k, \lambda x : \tau. x) \in E[\tau \rightarrow \alpha]_\sigma \)
       @br
       @b{Corollary.} \( k \rightarrow^* v_{kv} \) such that \( (v_{kv}, \lambda x : \tau. x) \in V[\tau \rightarrow \alpha]_\sigma \).
       @br
       @br
       Back to the theorem, we know that \( v_k = \lambda f : \tau \rightarrow \tau_k. e_k \) and \( v_\tau = \lambda f : \tau \rightarrow \tau. e_\tau \). Unfolding the
       value interpretation and using the corollary, we obtain
       \[ (e_k[v_{kv} / f], e_\tau[(\lambda x : \tau. x) / f]) \in E[\alpha]_\sigma \]
       In turn, this means there exist two values \( v_{fk} \) and \( v_{f\tau} \) that the two expressions above step to, such that
       \[ (v_{fk}, v_{f\tau}) \in V[\alpha]_\sigma \]
       or equivalently
       \[ (v_{fk}, v_{f\tau}) \in R \]
       From the definition of R, we get \( (v_{fk}, k v_{f\tau}) \in E[\tau_k]_\emptyset \).
       @br
       Consider the sequence of reductions
       \begin{align}
       e[\tau_k] k & \rightarrow^* (\Lambda \alpha. e') [\tau_k] k \\
       & \rightarrow e'[\tau_k / \alpha] k \\
       & \rightarrow^* v_k k \\
       & \rightarrow e_k [k / f] \\
       & \rightarrow^* v_{fk}
       \end{align}
       and
       \begin{align}
       e[\tau] (\lambda x : \tau. x) & \rightarrow^* (\Lambda \alpha. e') [\tau] (\lambda x: \tau. x) \\
       & \rightarrow e'[\tau / \alpha] (\lambda x: \tau. x) \\
       & \rightarrow^* v_\tau (\lambda x: \tau. x) \\
       & \rightarrow e_\tau [\lambda x: \tau. x / f] \\
       & \rightarrow^* v_{f\tau}
       \end{align}
      Together with properties of reductions, this implies \( (e [\tau_k] k, k (e [\tau] (\lambda x: \tau. x))) \in E[\tau_k]_\emptyset \), which is what we want to show. \( \blacksquare \)
      @br
      @br
      Now we go back to the lemma.
      @br
      @b{Lemma.} \( (k, \lambda x : \tau. x) \in E[\tau \rightarrow \alpha]_\sigma \).
      @br
      @b{Proof.}
    }
  }
 }
}