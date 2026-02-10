#import "/cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

#card("ptribu", "Tribu", ("Maths.Probabilités",))

Définition et propriétés de tribu.

#answer

Soit $Omega$ un ensemble non vide. Une tribu sur $Omega$ est un $cal(T) subset.eq cal(P)(Omega)$ tel que

- $emptyset in cal(T)$.

- $cal(T)$ est stable par passage au complémentaire.

- $cal(T)$ est stable par union dénombrable.

$(Omega, cal(T))$ est appelé espace probabilisable.

On a alors

- $Omega in cal(T)$.
- $cal(T)$ est stable par union finie.
- $cal(T)$ est stable par intersection dénombrable.
- Pour tout $A, B in cal(T)$, $A \\ B in cal(T)$.

*Démonstration*

- $Omega = overline(emptyset)$
- Pour $(A_i)_i in cal(T)^I$, #h(1fr)
  $
    inter.big_(i in I) A_i = overline(union.big_(i in I) overline(A_i)) in cal(T)
  $
- Pour $A, B in cal(T)$
  $
    A \\ B = A inter overline(B) in cal(T)
  $

#card("espprob", "Espace probabilisé", ("Maths.Probabilités",))

Définition et propriétés des espaces probabilisés.

#answer

Soit $(Omega, cal(T))$ un espace probabilisable. Une probabilité sur $(Omega, cal(T))$ est la donné d'un
$
  PP : cal(T) -> [0, 1]
$
Tel que

- $PP(Omega) = 1$.

- Pour tout $(A_n)_n in cal(T)^NN$ deux à deux disjoints
  $
    PP(union.plus.big_(n in NN) A_n) = sum_(n in NN) PP(A_n)
  $
  Avec convergence de la somme.

Dans ce cas

- $PP(emptyset) = 0$. #h(1fr)

- Pour tout $A subset.eq B in cal(T)$
  $
    PP(A) <= PP(B) \
    PP(B \\ A) = PP(B) - PP(A)
  $

- Pour tout $A in cal(T)$
  $
    PP(overline(A)) = 1 - PP(A)
  $

- Pour tout $(A_n)_n in cal(T)^NN$ une suite croissante d'évenements
  $
    PP(union.big_(n in NN) A_n) = lim_(n -> oo) PP(A_n)
  $

- Pour tout $(A_n)_n in cal(T)^NN$ une suite décroissante d'évenements
  $
    PP(inter.big_(n in NN) A_n) = lim_(n -> oo) PP(A_n)
  $

*Démonstration*

- On pose $(A_n)_n = (emptyset)_n$ deux à deux disjoints #h(1fr)
  $
    PP(emptyset) = PP(union.plus.big_(n in NN) A_n) = sum_(n in NN) PP(emptyset)
  $
  Qui converge d'où $PP(emptyset) = 0$.

- Soit $A subset.eq B in cal(T)$, on a
  $
    B = A union.plus (B \\ A) \
    PP(B) = PP(A) + PP(B \\ A)
  $

- Cas croissant :
  $
  B_0 = A_0 \
  B_(n + 1) = A_(n + 1) \\ A_n
  $
  Ainsi
  $
    A_n &= union.plus.big_(k = 0)^n B_k \
    &= union.big_(k = 0)^n A_n
  $
  De même
  $
    union.big_(n in NN) A_n &= union.plus.big_(n in NN) B_n \
    PP (union.big_(n in NN) A_n) &= sum_(n in NN) PP(B_n) \
    &= lim_(n -> oo) sum_(k = 0)^n PP(B_k) \
    &= lim_(n -> oo) PP(A_n)
  $

- Cas décroissant : On pose $B_n = overline(A_n)$, suite croissante.

#card("borcant", "Lemme de Borel-Cantelli", ("Maths.Probabilités",))

Énoncé et démonstration du lemme de Borel-Cantelli, version faible et version forte.

#answer

*Borel-Cantelli faible*

Pour $(A_n)_in in cal(T)^NN$ où $(Omega, cal(T), PP)$ est un ep, on pose
$
  S &= inter.big_(N in NN) union.big_(n >= N) A_n \
  &= lim sup A_n
$
Si $sum PP(A_n)$ converge, alors $PP(S) = 0$.

*Démonstration*

On pose $B_N = union.big_(n >= N) A_n$, une suite décroissante d'évenements, d'où
$
  PP(S) &= PP(inter.big_(N in NN) B_N) \ 
  &= lim_(N -> oo) PP(B_N) \
  &<= lim_(N -> oo) sum_(n = N)^(+oo) PP(A_n) = 0
$

*Borel-Cantelli fort*

Avec les même notations, si $sum PP(a_n)$ diverge et $(A_n)_n$ mutuellement indépendants, alors $PP(S) = 1$.

*Démonstration*

On a
$
  overline(S) = union.big_(N in NN) inter.big_(n >= N) overline(A_n)
$
Ainsi
$
  PP(S) &= 1 - PP(overline(S)) \
  &>= 1 - sum_(N in NN) PP(inter.big_(n >= N) overline(A_n))
$
Or
$
  PP(inter.big_(n >= N) overline(A_n)) &= lim_(n -> oo) PP(inter.big_(k = N)^(n) overline(A_k)) \
  &= lim_(n -> oo) product_(k = N)^(n) (1 - PP(A_n))
$
Et
$
  product_(k = N)^(n) (1 - PP(A_n)) &<= product_(k = N)^n e^(-PP(A_k)) \
  &= exp(-sum_(k = N)^n PP(A_k)) \
  &tends(n -> oo) 0
$

#card("vadp", "Variables aléatoires discrètes", ("Maths.Probabilités",))

Définition de variable aléatoire discrète.

#answer

Soit $(Omega, cal(T), PP)$ un ep, $E != emptyset$ un ensemble. Une variable aléatoire discrète sur $Omega$ à valeur dans $E$ est une application $X : Omega -> E$ tel que
- $X(Omega)$ est fini ou dénombrable.

- $forall x in X(Omega), X^(-1){x} in cal(T)$

Qui détermine une distribution de probabilité discrète sur $E$ ou $X(Omega)$.

// NOTE: Indépendance d'évenements, formules de probabilité totales, de Bayes, conditionelles...

#card("loibas", "Lois classique de probabilité", ("Maths.Probabilités",))

Lois classique de probabilité, définition, espérance, variance et série génératrice.

#answer

#align(center, table(
  stroke: none,
  columns: 1,
  table.hline(),
  [*Bernoulli* ($p in [0, 1]$)],
  table.hline(),
  $
    X(Omega) &= {0, 1} quad quad& PP(X = 1) &= p\ 
    EE(X) &= p quad quad& VV(X) &= p q \
  $,
  $
    G_X (t) = p t + q \
    X ~ cal(B)(p)
  $,
  table.hline(),
  [*Binomiale* ($n in NN, p in [0, 1]$)],
  table.hline(),
  $
    X(Omega) &= [|0, n|] quad& PP(X = k) &= vec(n, k) p^k q^(n - k) \
    EE(X) &= n p quad quad& VV(X) &= n p quad \
  $,
  $
    G_X (t) &= (p t + q)^n \
    X &~ cal(B)(n, p)
  $,
  table.hline(),
  [*Géométrique* ($p in Ioc(0, 1)$)],
  table.hline(),
  $
    X(Omega) &= NN^* quad& PP(X = k) &= q^(n - 1) p \
    EE(X) &= 1 / p quad quad& VV(X) &= q / p^2 quad \
  $,
  $
    G_X (t) = (p t) / (1 - q t) \
    X ~ cal(G)(p)
  $,
  table.hline(),
  [*Poisson* ($lambda > 0$)],
  table.hline(),
  $
    X(Omega) &= NN quad& PP(X = k) &= e^(-lambda) lambda^k / (k!) \
    EE(X) &= lambda quad quad& VV(X) &= lambda quad \
  $,
  $
    G_X (t) = e^(lambda (t - 1)) \
    X ~ cal(P) (lambda)
  $,
))

// NOTE: lois usuels - M287, resultats connus qui existent
// - indépendance de variable à faire ?

#card("lemdescoal", "Lemme des coalitions", ("Maths.Probabilités",))

Lemme des coalitions.

#answer

Soit $(X_1, dots, X_(n + m))$ une famille de variables aléatoires discrètes indépendantes sur $(Omega, cal(T), PP)$.
$
  f : product_(i = 1)^n X_i (Omega) -> E \
  g : product_(j = n+1)^(n + m) X_j (Omega) -> F \
$
Alors $f(X_1, dots, X_n)$ et $g(X_(n+1), dots, X_(n+m))$ sont des variables aléatoires discrètes indépendantes.

*Démonstration*

Calculs pas très beau, fubini.

// NOTE: Interpretation des lois usuels M289
