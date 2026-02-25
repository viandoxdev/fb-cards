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

#card("exinegconc1", "Exercice : première inégalité de concentration", ("Maths.Exercice.Probabilités",))

Première inégalité de concentration (Exercice 57) :

Soit $(X_k)_(1 <= k <= n)$ vad réelles centrées indépendantes tel que pour tout $k in [|1, n|]$, $abs(X_k) < 1$.

On pose $S_n = sum_(k = 1)^n X_k$, montrer que
$
  PP(S_n / n >= epsilon) <= e^(-(epsilon^2 n) / 2) \
  "puis" \
  PP(abs(S_n / n) >= epsilon) <= 2 e^(-(epsilon^2 n) / 2)
$

#answer

+ Pour tout $x in [-1, 1]$, $t in RR$, #h(1fr)
  $
    s = (1 - x) / 2 in [0, 1] \
    t x = s (-t) + (1 - s) t 
  $
  D'où
  $
    e^(t x) &= e^(s (-t) + (1 - s) t) \
    &<= s e^(-t) + (1 - s) e^t \
    &= (1 - x) / 2 e^(-t) + (1 + x) / 2 e^t
  $

+ Soit $t in RR^+$, $X$ vad réelle centrée à valeur dans $[-1, 1]$
  $
    EE(e^(t X)) &<= EE((1 - X) / 2 e^(-t) + (1 + X) / 2 e^t) \
    &= (1 - EE(X)) / 2 e^(-t) + (1 + EE(X)) / 2 e^t \
    &= ch(t)
  $
  Donc
  $
    EE(e^(t S_n)) &= EE(product_(k = 1)^n e^(t X_k)) \
    (tack.t.double) quad &= product_(k = 1) EE(e^(t X_k)) \
    &<= ch(t)^n
  $

  Or pour tout $t in RR^+$
  $
    ch(t) = sum_(n = 0)^(+oo) t^(2 n) / (2 n)! quad e^(t^2 / 2) = sum_(n = 0)^(+oo) t^(2 n) / (2^n n!) \
    (2 n)! / (2^n n!) = product_(k = 0)^(n - 1) (2 k + 1) >= 1 \
  $
  Donc $ch(t) <= e^(t^2 / 2)$

  Et ainsi
  $
    EE(e^(t S_n)) <= e^((t^2 n) / 2)
  $

+ Soit $a > 0$
  $
    PP(abs(S_n) >= a) = PP(S_n >= a) + PP(-S_n >= a)
  $
  Soit $t in RR^+$
  $
    PP(S_n >= a) &= PP(e^(t S_n) >= e^(t a)) \
    ("Markov") space &<= EE(e^(t S_n)) / e^(t a) \
    &<= e^((t^2 n) / 2 - t a)
  $
  Pour $t = a / n$
  $
    PP(S_n >= a) <= e^(- a^2 /( 2 n))
  $
  Et comme les $(-X_k)_k$ verifient les mêmes hypothèses
  $ 
    PP(-S_n >= a) <= e^(- a^2 / (2 n)) 
  $
  Ainsi
  $
    PP(abs(S_n) >= a) <= 2 e^(- a^2 / (2 n)) 
  $

+ Avec $a = n epsilon$
  $
    PP(abs(S_n / n) >= epsilon) &= PP(abs(S_n) >= n epsilon) \
    &<= 2 e^(- (n  epsilon^2) / 2)
  $

*Remarque*

$
  PP(abs(S_n / n - 0) >= epsilon ) &= PP(abs(S_n - EE(S_n)) >= n epsilon) \
  &<= (sum_(k = 1)^n VV(X_k)) / (n^2 epsilon^2) <= 1 / (n epsilon^2)
$

#card("exinegconc2", "Exercice : quelques inégalités", ("Maths.Exercice.Probabilités",))

+ Exercice 62.1 : #h(1fr)

  Soit $X$ une vad réelle positive de $LL^2$ tel que $EE(X^2) > 0$, montrer que
  $
    PP(X > 0) >= EE(X)^2 / EE(X^2)
  $

+ Exercice 56 :

  Soit $X$ une vad réelle positive de $LL^2$ tel que $PP(X > 0) > 0$, et $theta in Ioo(0, 1)$, montrer que
  $
    PP(X >= theta EE(X)) >= ((1 - theta)^2 EE(X)^2) / (EE(X^2))
  $

#answer

+ Par Cauchy-Schwartz #h(1fr)
  $
    EE(X)^2 &= EE(X bb(1)_(X > 0))^2 \
    &<= EE(X^2) EE(bb(1)_(X > 0)) \
    &= EE(X^2) PP(X > 0)
  $

+ Similairement
  $
    EE(X bb(1)_(X >= theta EE(X)))^2 <= EE(X^2) PP(X >= theta EE(X))
  $
  Et
  $
    X bb(1)_(X >= theta EE(X)) = X - underbrace(X bb(1)_(X < theta EE(X)), <= theta EE(X)) \
    EE(X bb(1)_(X >= theta EE(X))) >= (1 - theta) EE(X)
  $
  Ainsi
  $
  (1 - theta)^2 EE(X)^2 <= EE(X^2) PP(X >= theta EE(X))
  $

#card("expilepile", "Exercice : probabilité de pile pile, calcul d'espérance par récurrence", ("Maths.Exercice.Probabilités",))

Exercice 14 :

Soit $(X_n)_(n in NN^*)$ vaiid tel que $X_k ~ cal(B)(1/2)$. On note
$
  T &= min Set(k >= 2, X_k = 1 "et" X_(k-1) = 1) \ &in NN union {+oo}
$

+ Montrer que $T$ est une vad.

+ Montrer que $T$ est ps fini.

+ Calculer $EE(T)$.

#answer

+ On sait que $T(Omega) subset.eq NN union {+oo}$ qui est fini ou dénombrable.

  Pour tout $n in NN$
  $
    (T > n) &= inter.big_(k = 2)^(n)  overline((X_k = X_(k - 1) = 1)) in cal(T) \

    (T = n) &= (T > n - 1) \\ (T > n) in cal(T) \ \
    
    (T = +oo) &= inter.big_(n = 1)^(+oo) (T > n) in cal(T)
  $

+ Calculons la loi de $T$ (on note $p_n = PP(T = n)$) :
  $
    p_1 = 0 quad quad p_2 = 1 /4
  $
  Soit $n >= 3$
  $
    p_n = &PP(T = n, X_1 = 1) \ +  &PP(T = n, X_1 = 0)
  $
  On pose $(tilde(X)_k)_(k >= 1) = (X_(k + 1))_k$ et $tilde(T)$ associé aux $(tilde(X)_k)_k$.

  Ainsi pour tout $m >= 2$ (Par le lemme des coalitions)
  $
    (tilde(T) = m) tack.t.double (X_1 = 0)
  $
  D'où
  $
   & PP(T = n, X_1 = 0) \ =& PP(tilde(T) = n - 1, X_1 = 0) \
   =& PP(tilde(T) = n - 1) PP(X_1 = 0)
  $
  Or $tilde(T) ~ T$, d'où
  $
    p_n = p_(n - 1) PP(X_1 = 0)
  $

  De même, on pose $(tilde(tilde(X))_k)_(k >= 1) = (X_(k + 2))_k$ et $tilde(tilde(T))$ associé.
  $
    & PP(T = n, X_1 = 1) \
    =& PP(T = n, X_1 = 1, X_2 = 0) \
    =& PP(tilde(tilde(T)) = n - 2) PP(X_1 = 1) PP(X_2 = 0) \
    =& p_(n - 2) PP(X_1 = 1) PP(X_2 = 0)
  $

  D'où pour $n >= 3$
  $
    p_n = 1/2 p_(n - 1) + 1/4 p_(n - 2) \
    2^n p_n = 2^(n - 1) p_(n - 1) + 2^(n - 2) p_(n - 2)
  $
  Et $(2^n) p_n$ suit la relation de récurrence de Fibonnaci.

  Posons maintenant
  $
    s &= sum_(n = 2)^(+oo) p_n = 1 - PP(T = +oo) \
    &= p_2 + sum_(n = 3)^(+oo) (1/2 p_(n - 1) + 1/4 p_(n - 2)) \
    &= 1/4 + 1/2 s + 1/4 s
  $
  D'où $1/4 s = 1/4$ et $s = 1$, $PP(T = +oo) = 0$.

+ De même
  $
    EE(T) &= sum_(n = 2)^(+oo) n p_n \
    &= 2 p_2 + sum_(n = 3)^(+oo) n(1/2 p_(n - 1) + 1/4 p_(n - 2)) \
    &= 1/2 + 1/2 sum_(n = 3)^(+oo) (n - 1) p_(n - 1) \
    &+ 1/2 sum_(n = 3)^(+oo) p_(n - 1) + 1/4 sum_(n = 3)^(+oo) (n - 2) p_(n - 2) \
    &+ 1/4 sum_(n = 3)^(+oo) 2 p_(n - 2) \
    &= 3/2 + 3/4 EE(T) \
    &= 6
  $

#card("foncgen", "Fonction génératrice d'une variable aléatoire entière naturelle", ("Maths.Probabilités",))

Fonction génératrice d'une variable aléatoire entière naturelle.

#answer

Si $X$ est une vad à valeur dans $NN$, alors $R_"cv" (sum PP(X=n) t^n) >= 1$ et la série entière converge normalement sur $overline(DD(0,1))$
$
  G_X : func([0,1], RR, t, sum_(n = 0)^(+oo) PP(X = n) t^n)
$
Est appelée fonction génératrice de $X$, et les valeurs de $G_X$ sur un $[0, delta]$ avec $delta > 0$ detérminent de manière unique la loi de $X$.

On a de plus

- $G_X (1) = 1$.

- $G_X$ est $C^oo$ sur $Ico(0,1)$ et pour tout $n in NN$
  $
    G_X^((n)) >= 0
  $

- $X$ est d'ésperance finie ssi $G_X$ est dérivable en $1$ et dans ce cas #h(1fr)
  $
    G'_X (1) = EE(X)
  $

- $X^2$ est d'ésperance finie ssi $G_X$ est dérivable deux fois en $1$ et dans ce cas
  $
    G''_X (1) &= EE(X(X-1)) = EE(X^2) - EE(X) \
    VV(X) &= G''_X (1) + G'_X (1) - G'_X (1)^2
  $

- Pour $X, Y$ vad entières naturelles indépendantes sur le même ep
  $
    G_(X+Y) = G_X G_Y
  $

*Démonstration*

Pour la pluspart : les écrires.

- On suppose que $EE(X) < +oo$ #h(1fr)

  On considère $G_X$ comme une série de fonctions, on montre que $sum f'_n$ CVN sur $[0, 1]$ et on applique le théorème de dérivation des séries de fonctions.

- On suppose que $EE(X) = +oo$ (contraposée)

  On exprime le taux d'accroissement en $1$, on le developpe et on montre qu'il diverge.

- Même shéma de preuve pour $X^2$.

- Par le lemme de transfer
  $
    G_X (t) = EE(t^X)
  $
  D'où
  $
    G_(X+Y) (t) &= EE(t^(X + Y)) = EE(t^X t^Y) \
    &= EE(t^X) EE(t^Y) = G_X (t) G_Y (t)
  $

#card("exnbcyclper", "Exercie : nombre de cycles d'une permutation aléatoire", ("Maths.Probabilités",))

Soit $sigma_n ~ cal(U) (frak(S)_n)$ et $X_n$ le nombre de cycle de $sigma_n$.

+ Calculer $G_X_n$.

+ En déduire $EE(X_n)$, $VV(X_n)$.

#answer

+ Soit $k in [|1, n|]$

  $
    X^(-1)_(n+1) {k} &= Set(sigma in frak(S)_n, cases(delim: #none, script(sigma(n+1) = n+1), script(sigma|_([|1,n|]) "a" k - 1 "cycles"))) \
    &union.plus union.plus.big_(l = 1)^n underbrace(Set(sigma in frak(S)_(n+1), cases(delim: #none, script(sigma^(-1)(n+1) = l), script(sigma "a" k "cycles"))), Gamma_l) \
  $
  Avec $Gamma_l tilde.eq X^(-1)_n {k}$ par la bijection
  $
    func(Gamma_l, X^(-1)_n {k}, sigma, func([|1,n |], [|1,n|], j != l, sigma(j), l, sigma(n+1)))
  $

  Ainsi
  $
    abs(X^(-1)_(n+1) {k}) = abs(X^(-1)_n {k - 1}) + n abs(X^(-1)_n {k}) \
  $
  $
    PP(X_(n+1) = k) &= 1/(n+1) PP(X_n = k - 1) \ &+ n / (n+1) PP(X_n = k)
  $
  Qui est aussi vrai pour $k = n+1$.

  Ainsi pour tout $t in [0, 1]$
  $
    G_X_(n+1) (t) &= sum_(n = 1)^(n+1) PP(X_(n+1) = k) t^k \
    &= 1/(n+1) (sum_(k = 1)^(n+1) PP(X_n = k - 1) t^k \ &+ n sum_(k = 1)^(n+1) PP(X_n = k) t^k) \
    &= 1/(n+1) (sum_(k = 1)^(n) PP(X_n = k) t^(k+1) \ &+ n sum_(k = 1)^(n+1) PP(X_n = k) t^k) \
    &= (t + n) / (n+1) G_X_n (t) \
    G_X_1 (t) &= t
  $

  D'où
  $
    G_X_n (t) = 1 / n! product_(k=0)^(n-1) (t + k)
  $

+ On calcul
  $
    G'_X (t) &= 1/n! sum_(j = 0)^(n - 1) (product_(k = 0)^(n-1) (t + k)) / (t + j) \
    G'_X (1) &= 1/n! sum_(j = 0)^(n - 1) n! / (1 + j) = H_n
    
  $
  D'où $EE(X_n) = H_n eqv(n -> oo) ln(n)$.

  Et
  $
    G''_n (t) &= 1/n! sum_(0 <= i, j <= n - 1 \ i != j) (product_(k = 0)^(n-1) (t + k)) / ((t+j)(t+i)) \
    G''_n (1) &= sum_(1 <= i, j <= n - 1 \ i != j) 1 / (i j) = H_n^2 - underbrace(sum_(k = 1)^n 1/k^2, K_n)
  $
  D'où $VV(X_n) = H_n - K_n eqv(n -> oo) ln(n)$.

// NOTE: Dés pipés M304 

#card("loisomvar", "Loi d'une somme de variables aléatoires paramétrée par une variable aléatoire", ("Maths.Probabilités",))

Loi d'une somme de variables aléatoires paramétrée par une variable aléatoire :
$
  sum_(k = 1)^T X_k
$
Avec $(X_k)_(k >= 1)$ et $T$ des variables aléatoires.

#answer

Soient $(X_k)_(k >= 1)$ vaiid à valeur dans $NN$ et $T$ une vad à valeur dans $NN$ indépendante des $X_k$. On pose
$
  S_T = sum_(k = 1)^T X_k quad quad S_n = sum_(k = 1)^n X_k
$

Alors

+ $S_T$ est une vad.

+ $G_S_T = G_T compose G_X_1$

*Démonstration*

+ $S_T (Omega) subset.eq NN$ qui est dénombrable, et pour tout $k in NN$
  $
    S^(-1)_T {k} &= union.plus.big_(j = 0)^(+oo) S^(-1)_T {k} inter (T = j) \
    &= union.plus.big_(j = 0)^(+oo) (S_j = k) inter (T = j) in cal(T) \
  $

+ Pour tout $t in [0,1]$

  $
    G_S_T (t) &= sum_(k = 0)^(+oo) PP(S_T = k) t^k \
    &= sum_(k = 0)^(+oo) (sum_(n = 0)^(+oo) PP(T = n, S_n = k))t^k \
    ("LdC") &= sum_(k = 0)^(+oo) sum_(n = 0)^(+oo) PP(T = n)PP(S_n = k) t^k \
    (>=0) &= sum_(n = 0)^(+oo) PP(T = n) sum_(k = 0)^(+oo) PP(S_n = k) t^k \
    &= sum_(n = 0)^(+oo) PP(T = n) G_S_n (t) \
    (tack.t.double) &= sum_(n = 0)^(+oo) PP(T = n) G_X_1 (t)^n \
    &= G_T (G_X_1 (t))
  $

// NOTE: Galton Watson M306

// TODO: Peut être découper ? Il y a beaucoup sur les marches aléatoires

#card("marchal", "Marches aléatoires sur les entiers relatifs", ("Maths.Probabilités",))

Marches aléatoires sur les entiers relatifs.

#answer

Soit $(X_k)_(k >= 1)$ vaiid et $S_n = sum_(k = 1)^n X_k$ tel que
$
  PP(X_k = 1) = PP(X_1 = 1) = p \
  PP(X_k = -1) = PP(X_1 = -1) = 1 - p \
$

+ On remarque tout d'abord #h(1fr)
  $
    Y_k = (X_k + 1) / 2 quad quad Y_k ~ cal(B)(p)
  $
  Et
  $
    X_k eq.triple 1 space [2] quad quad S_n eq.triple n space [2]
  $
  D'où
  $
    PP(S_(2 n) = 2k + 1) = 0 \
    PP(S_(2 n + 1) = 2k) = 0 \
  $

+ On peut calculer $PP(S_(2 n) = 0)$
  $
    S_(2 n) &= sum_(k = 1)^(2 n) X_k \
    &= 2 sum_(k = 1)^(2 n) Y_k - 2 n
  $
  D'où
  $
    PP(S_(2 n) = 0) &= PP(sum_(k = 1)^(2n) Y_k = n) \
    &= vec(2n, n) p^n (1 - p)^n
  $

// TODO: Le reste...
