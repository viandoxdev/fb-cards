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

#card("esppb", "Espérance d'une variable aléatoire", ("Maths.Probabilités",))

Définition et propriétés élémentaires de l'ésperance d'une variable aléatoire.

#answer

- Pour $X$ une variable aléatoire sur $(Omega, cal(T), PP)$ complexe, on dit que $X$ est d'ésperance finie si $(x P(X = x))_(x in X^(-1) (Omega))$ est sommable, on note $X in LL^1$ et on pose
  $
    EE(X) = sum_(x in X^(-1) (Omega)) x PP(X = x)
  $

- Pour $X$ à valeur dans $RR_+$ on définit l'ésperance dans $RR_+ union {+oo}$, avec $EE(X) = +oo$ si la somme diverge.

- Pour $X$ à valeur dans $NN$ on a
  $
    EE(X) = sum_(n = 0)^(+oo) PP(X >= n)
  $

- Si $X$ est à valeur dans $NN$ et $EE(X) < +oo$, alors
  $
    PP(X >= n) tends(n -> oo) 0 \
    PP(X >= n) = o_(n -> oo) (1/n)
  $

*Démonstration*

- $X$ à valeur dans $NN$ #h(1fr)
  $
    sum_(n = 0)^(+oo) PP(X >= n) &= sum_(n = 0)^(+oo) sum_(k = n)^(+oo) PP(X = k) \
    &= sum_(k = 0)^(+oo) sum_(n = 0)^(k) PP(X = k) \
    &= sum_(k = 0)^(+oo) k PP(X = k) \
    &= EE(X)
  $

- La première ligne est toujours vraie car 
  $
    sum_(n = 0)^(+oo) PP(X >= n) = EE(X) < +oo
  $
  Pour la deuxième
  $
    n PP(X >= n) &= n sum_(k = n)^(+oo) PP(X = k) \
    &<= sum_(k = n)^(+oo) k PP(X = k) tends(n -> oo) 0
  $
  Car série reste d'une série convergente.

#card("ldtpb", "Lemme de tranfert", ("Maths.Probabilités",))

Énoncé et démonstration du lemme de transfert.

#answer

Soit $X$ variable aléatoire discrète à valeur dans $E$, et $f : E -> CC$.

Alors $f(X) in LL^1$ ssi $(f(x)P(X = x))_(x in X^(-1)(Omega))$ est sommable et 
$
  EE(f(X)) = sum_(x in X^(-1)(Omega)) f(x) PP(X = x)
$

On en déduit que $X in LL^1$ ssi $EE(abs(X)) < +oo$.

*Démonstration*

Sommation par paquets.

#card("propesppb", "Propriétés de l'ésperance", ("Maths.Probabilités",))

Propriétés de l'ésperance.

#answer

On a les propriétés suivantes

- Toute variable aléatoire bornée est d'ésperance finie.
- $EE$ est linéaire : #h(1fr)
  $
  EE(alpha A + beta B) = alpha EE(A) + beta EE(B)
  $
- $EE$ est croissante :
  $
    X <= Y => EE(X) <= EE(Y)
  $
- On à l'inégalité triangulaire
  $
    abs(EE(X)) <= EE(abs(X))
  $
- Pour $X tack.t.double Y$
  $
    EE(X Y) = EE(X) EE(Y)
  $
- Pour $A in cal(T)$
  $
    EE(bb(1)_A) = PP(A)
  $
- Pour $X, Y in LL^2$
  $
    EE(X Y)^2 <= EE(X^2) EE(Y^2)
  $
  avec égalité ssi $X = alpha Y$ ps.

// NOTE: Démonstrations M294 et avant

#card("varvapb", "Variance d'une variable aléatoire", ("Maths.Probabilités",))

Définition et propriétés élémentaires de la variance d'une variable aléatoire.

#answer

*Variance*

Pour $X$ une variable aléatoire discrète réelle, on note $X in LL^2$ si $X^2 in LL^1$.

Dans ce cas $X in LL^1$, et on définie
$
  VV(X) &= EE((X - EE(X))^2) \
  &= underbrace(EE(X^2) - EE(X)^2, "Koenig-Huygens")
$

On a alors

- Si $Y = a X + b$ #h(1fr)
  $
    VV(Y) = a^2 VV(X)
  $

- $VV(X) = 0$ ssi $X$ ps constante.

*Covariance*

On définit de plus la covariance de $X, Y in LL^2$
$
"Cov" (X, Y) \ = EE((X - EE(X))(Y - EE(Y))) \
= EE(X Y) - EE(X) EE(Y)
$
Qui est une forme bilinéaire, symétrique, positive.

Si $"Cov"(X, Y) = 0$ on dit que $X$ et $Y$ sont décorélées, et dans ce cas
$
  VV(X + Y) = VV(X) + VV(Y)
$

- Deux variables indépendantes sont décorélées.

- Pour $X, Y in LL^2$
  $
    "Cov"(X, Y)^2 <= VV(X) VV(Y)
  $

*Démonstration*

- Pour $X in LL^2$ #h(1fr)
  $
    EE((X - EE(X))^2) \ = EE(X^2 - 2X EE(X) + EE(X)^2) \
   = EE(X^2) - 2 EE(X) EE(X) + EE(X^2) \
   = EE(X^2) - EE(X)^2
  $

- Pour $Y = a X + b$ \
  $
    VV(Y) &= EE((a X + b - EE(a X + b))^2) \ 
    &= EE((a X - a EE(X))^2) \
    &= a^2 EE((X - EE(x))^2) \
    &= a^2 VV(X)
  $

#card("inegprob", "Premières inégalités de probabilités", ("Maths.Probabilités",))

Premières inégalités de probabilités.

#answer

*Markov*

Pour $X in LL^1$ reélle, et pour tout $delta > 0$
$
  EE(abs(X) >= delta) <= EE(|X|) / delta
$
Et de plus pour $f : RR_+ -> RR_+$ strictement croissante et $X >= 0$
$
  PP(X >= delta) <= EE(f(X)) / f(delta)
$

*Bienaymé-Tchebychev*

Soit $X in LL^2$, $m = EE(X)$ et $delta > 0$
$
  PP(abs(X - m) >= delta) <= VV(X) / delta^2
$

*Démonstration*

Pour $X >= 0$
$
  X = X bb(1)_(X < delta) + X bb(1)_(X >= delta)
$
$
  EE(X) &= underbrace(EE(X bb(1)_(X < delta)), >= 0) + EE(X bb(1)_(X >= delta)) \ 
  &>= EE(delta bb(1)_(X >= delta)) = delta PP(X >= delta)
$

Et ainsi pour $X in LL^2$
$
  PP(abs(X - m) >= delta) &= PP((X - m)^2 >= delta^2) \
  &<= EE((X - m)^2) / delta^2 \
  &= VV(X) / delta^2
$

#card("loigrandnmbr", "Loi des grands nombres", ("Maths.Probabilités",))

Loi faible et loi forte des grands nombres.

#answer

*Faible*

Soit $(X_n)_(n in NN^*)$ vaiid de $LL^2$. On note $m = EE(X_1)$ et $sigma = sigma(X_1)$, pour $n in NN, S_n = sum_(k = 1)^n X_k$.

Pour tout $delta > 0$
$
  PP(abs(S_n / n - m) >= delta) tends(n -> oo) 0
$
$(S_n / n)_n$ converge en probabilité vers $m$.

*Forte*

*Démonstration*

$
  PP(abs(S_n / n - m) >= delta) \ <= VV(S_n / n) / delta^2 = VV(sum_(k = 1)^n X_k) / (n^2 delta^2) = delta^2 / (n delta^2) \
  tends(n -> oo) 0
$

#card("exweieprob", "Exercice : Démonstration probabiliste du théorème de Weierstrass", ("Maths.Exercices.Probabilités",))

Démonstration probabiliste du théorème de Weierstrass.

#answer

Soit $f in C^0 ([0, 1], RR)$, pour $n in NN$
$
  B_n = sum_(k = 0)^n vec(n, k) f(k / n) X^k (1 - X)^(n - k)
$
Montrons que $(B_n)_n$ CVU vers $f$ sur $[0, 1]$.

Soit $x in [0, 1]$, $(X_n)_(n in NN^*)$ vaiid tel que $X_k ~ cal(B)(x)$. Et $S_n = sum_(k = 1)^n X_k ~ cal(B)(n, x)$. On remarque que
$
  B_n (x) &= sum_(k = 0)^n f(k / n) PP(S_n = k) \ &= EE(f(S_n / n))
$

Soit $epsilon > 0$, par uniforme continuité de $f$ sur $[0,1]$, on dispose de $delta > 0$ associé.

$
  abs(B_n (x) - f(x)) = abs(EE(f(S_n / n) - f(x))) \
$
$
  = abs(EE[ &underbrace((f(S_n / n) - f(x)), <= 2 norm(f)_oo) bb(1)_(abs(S_n / n - x) >= delta) \
  + &underbrace((f(S_n / n) - f(x)), < epsilon) bb(1)_(abs(S_n / n - x) < delta) ]) \
  <= & 2norm(f)_oo PP(abs(S_n / n - x) >= delta) + epsilon \
  <= & 2norm(f)_oo (x(1 - x)) / (n delta^2) + epsilon
$
