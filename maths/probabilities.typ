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

// NOTE: lois usuels - M287, résultats connus qui existent
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

Soit $(X_n)_(n in NN^*)$ vaiid de $LL^2$. On note $m = EE(X_1)$ et $sigma = sigma(X_1)$, pour $n in NN, S_n = sum_(k = 1)^n X_k$.

*Faible*

Pour tout $delta > 0$
$
  PP(abs(S_n / n - m) >= delta) tends(n -> oo) 0
$
$(S_n / n)_n$ converge en probabilité vers $m$.

*Forte*

$(S_n / n)_n$ converge presque surement vers $m$.

*Démonstration : faible*

$
  PP(abs(S_n / n - m) >= delta) \ <= VV(S_n / n) / delta^2 = VV(sum_(k = 1)^n X_k) / (n^2 delta^2) = sigma^2 / (n delta^2) \
  tends(n -> oo) 0
$

*Démonstration : forte*

Si $VV(X) = 0$, $X = m$ presque surement et le résultat est évident.

On peut alors centrer et réduire $X_n$ afin de se ramener à $m = 0$ et $sigma = 1$.

Par la version faible
$
  PP(abs(S_(n^2) / n^2) >= delta) <= 1 / (n^2 delta^2)
$
Qui est le terme général d'une série convergente. Donc par le lemme de Borel-Cantelli faible, on montre que $abs(S_(n^2) / n^2)$ converge presque surement vers $0$.

Soit $m in [|n_m^2, (n_m + 1)^2 - 1|]$
$
  abs(S_m / m) <= underbrace(abs(S_(n_m^2) / m), <= abs(S_(n^2_m)) / n^2_m) + 1/m abs(sum_(j = n_m^2 +1)^m X_j)
$
Or
$
  &PP(abs(1/m sum_(j = n_m^2+1)^m X_j) >= delta) \
  =& PP((sum_(j = n_m^2+1)^m X_j)^2 >= m^2 delta^2) \
  <=& EE((sum_(j = n^2_m + 1)^m X_j)^2) / (m^2 delta^2) \
  =& (m - n^2_m) / (m^2 delta^2) = (sqrt(m)^2 - floor(sqrt(m))^2) / (m^2 delta^2) \
  <=& (2sqrt(m) - 1) / (m^2 delta^2) = O(1/m^(3/2))
$
Qui est le terme général d'une série convergente
$
  PP(abs(1/m sum_(j = n_m^2+1)^m X_j) tends(m -> oo) 0) = 1
$
Et en sommant on a le résultat demandé.

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

+ Temps de retour en $0$ :

  On étudie
  $
    T_0 = min Set(n in NN^*, S_n (omega) = 0)
  $
  On note
  $
    S^((k))_n = sum_(i = k + 1)^(k + n) X_i ~ S_n \
    forall a <= b, n in NN, space ("LdC")\ 
    (T_0 = a) tack.t.double (S^((b))_n = 0)
  $

  Pour $n in NN^*$
  $
    &PP(S_(2 n) = 0)  \
    =& PP(S_(2 n) = 0, T_0 <= 2 n) \
    =& sum_(k = 1)^n  PP(S_(2n) = 0, T_0 = 2k) \
    =& sum_(k = 1)^n  PP(T_0 = 2k, S^((2k))_(2(n - k)) = 0) \
    =& sum_(k = 1)^n  PP(T_0 = 2k) PP(S^((2k))_(2(n - k)) = 0) \
    =& sum_(k = 1)^n  PP(T_0 = 2k) PP(S_(2(n - k)) = 0) \
  $
  On introduit
  $
    F : t |-> sum_(n = 0)^(+oo) PP(S_n = 0) t^n \
    tilde(F) : t |-> sum_(n = 0)^(+oo) PP(S_(2n) = 0) t^n \ 
    F(t) = tilde(F) (t^2) \
    G : t |-> sum_(n = 0)^(+oo) PP(T_0 = n) t^n \
    tilde(G) : t |-> sum_(n = 0)^(+oo) PP(T_0 = 2n) t^n \ 
    G(t) = tilde(G) (t^2)
  $
  Ainsi
  $
    tilde(F) (t) &= sum_(n = 0)^(+oo) vec(2n,n) p^n (underbrace(1 - p, q))^n t^n \
    &= sum_(n = 0)^(+oo) (2n)! / n!^2 (p q t)^n \
    &= sum_(n = 0)^(+oo) (2n)! / (2^n n!)^2 (4 p q t)^n \
    &= 1 / sqrt(1  - 4 p q t)
  $
  Avec $R_"cv" (tilde(F)) = 1 / (4 p q t)$ donc $1$ si $p = 1/2$ et $>1$ sinon.

  Or
  $
    0 <= PP(T_0 = 2 n) <= PP(S_(2n) = 0)
  $
  D'où $R_"cv" (tilde(G)) >= R_"cv" (tilde(F))$. Ainsi pour tout $t in Ioo(-1/(4 p q), 1 / (4 p q)) = I$
  $
    & tilde(F)(t) tilde(G)(t) 
    = sum_(n = 0)^(+oo) u_n t^n \
    =& sum_(n = 0)^(+oo) sum_(k = 0)^n PP(T_0 = 2k) PP(S_(2(n - k)) = 0) t^n \
    =& sum_(n = 0)^(+oo) PP(S_(2n) = 0) bb(1)_(n >= 1) t^n 
    = tilde(F)(t) - 1
  $
  D'où
  $
    tilde(G)(t) &= 1 - 1 / (tilde(F)(t)) \
    &= 1 - sqrt(1 - 4 p q t)
  $
  On a alors
  $
    PP(T_0 < +oo) &= sum_(k = 0)^(+oo) PP(T_0 = 2n) \
    &= tilde(G)(1) \ 
    &= 1 - sqrt(1 - 4 p q) \
    &= cases(space 1 "si" p = 1/2, space < 1 "si" p != 1/2)
  $

  Dans le cas $p = 1/2$
  $
    G(t) = G_T_0 (t) = 1 - sqrt(1 - t^2)
  $

+ On peut alors determiner $EE(T_0)$

  Si $p != 1/2$, $PP(T_0 = +oo) > 0$ et $EE(T_0) = +oo$.

  Sinon $p = 1/2$, or $G_T_0 (t) = 1 - sqrt(1 - t^2)$, qui n'est pas dérivable en $1$, donc $EE(T_0) = +oo$.

+ Temps du $k$-ème retour en $0$
  #let TR(j,k,a) = $attach(tl: #j, tr: #k, br: #a, T)$

  On note
  $
    TR(j,1,a) = min Set(n in NN^*, S^((j))_n = a) \
    TR(j,k,a) = min Set(n > TR(j,k-1,a), S^((j))_n = a) \
    TR(,k,a) = TR(0,k,a) quad quad TR(,,a) = TR(0,1,a)
  $
  Ainsi $TR(j,k,a)$ correspond au temps du $k$-ème retour en $a$ sur la marche decalée de $j$.
  $
    &PP(T^k_0 < +oo)\
    =& PP(T^k_0 < +oo, T^(k-1)_0 < +oo) \
    =& sum_(j = 1)^(+oo) PP(T^k_0 < +oo, T^(k - 1)_0 = j) \
    =& sum_(j = 1)^(+oo) PP(TR(j,1,0) < +oo, T^(k-1)_0 = j) \
    =& sum_(j = 1)^(+oo) PP(TR(j,1,0) < +oo) PP(T^(k-1)_0 = j) \
    =& PP(T_0 < +oo) sum_(j = 1)^(+oo) PP(T^(k-1)_0 = j) \
    =& PP(T_0 < +oo) PP(T^(k-1)_0 < +oo) \
    =& PP(T_0 < +oo)^k \
  $

+ On peut de plus dans le cas symétrique calculer $EE(abs(S_n))$.

  $
    abs(S_(N+1)) = &abs(S_N + 1) bb(1)_(X_(N+1) = 1) \ + &abs(S_N - 1) bb(1)_(X_(N+1) = -1) \
    EE(abs(S_(N+1))) = &EE(abs(S_N + 1)) PP(X_(N+1) = 1) \ + &EE(abs(S_N - 1)) PP(X_(N+1) = -1) \
    = &EE(1/2 (abs(S_N +1) + abs(S_N - 1))) \
    = &EE(abs(S_N) + bb(1)_(S_N = 0)) \
    = &EE(abs(S_N)) + PP(S_N = 0) \
  $
  Ainsi
  $
    EE(abs(S_n)) = sum_(k = 0)^(n - 1) PP(S_n = 0) \
    PP(S_(2 n) = 0) = (2 n)! / (2^n n!)^2 eqv(n -> oo) 1 / sqrt(pi n)
  $
  Qui est le terme général d'une série divergente
  $
    EE(abs(S_(2n))) &eqv(n -> oo) 1/sqrt(pi) sum_(k = 0)^(n - 1) 1/ sqrt(k) \
    &eqv(n -> oo) 2 sqrt(n) / sqrt(pi)
  $

// TODO: Plus de dimensions, cas uniforme, et temps de retour en a (M309-311)

#card("modeconvvad", "Modes de convergence des variables aléatoires", ("Maths.Probabilités",))

Modes de convergence des variables aléatoires.

#answer

On définit deux modes de convergence des variables aléatoires :

+ On dit que $(X_n)_(n in NN)$ converge en probabilité vers $X$ si #h(1fr)
  $
    forall delta > 0, PP(abs(X_n - X) >= delta) tends(n -> oo) 0
  $

+ On dit que $(X_n)_(n in NN)$ converge presque surement vers $X$ si
  $
    PP(X_n tends(n -> oo) X) = 1
  $
  Il s'agit bien d'un évenement : pour tout $omega in Omega$
  $
    &X_n (omega) tends(n -> oo) X(omega) \
    <=> & forall epsilon > 0, exists N in NN, forall n >= N, \ & abs(X_n (omega) - X(omega)) < epsilon \
    <=> & forall k in NN^*, exists N in NN, forall n >= N, \ & abs(X_n (omega) - X(omega)) < 1/k \
  $
  Ainsi
  $
    &(X_n tends(n -> oo) X) \ =& inter.big_(k in NN^*) union.big_(N in NN) inter.big_(n >= N) (abs(X_n - X) <= 1/k) \ in& cal(T)
  $

+ Si on se ramène à $X = 0$, notons pour tout $delta > 0$
  $
    A_(delta,n) = (abs(X_n) >= delta)
  $
  On veut
  $
    &PP(union.big_(N in NN) inter.big_(n >= N) abs(X_n) < delta) = 1 \
    <=>& PP(inter.big_(N in NN) union.big_(n >= N) A_(delta,n)) = 0
  $
  Donc par Borel-Cantelli faible, pour montrer $X_n tends("ps") X$, il suffit de montrer que
  $
    forall delta > 0, sum PP(A_(delta,n)) "converge"
  $

#card("chainmarko", "Chaînes de Markov", ("Maths.Probabilités",))

Chaînes de Markov.

#answer

On considère un ensemble fini d'état $E$, qu'on peut représenter par $[|1, N|]$.

Une chaîne de Markov sur $E$ est une suite $(X_n)_(n in NN)$ de variables aléatoires discrètes à valeur dans $E$ tel que si $n in NN$ et $i_0, dots, i_n in E^(n+1)$ tels que 
$
PP(X_0 = i_0, dots, X_n = i_n) > 0
$
Alors
$
  forall i_(n+1) in E, \
  PP(X_(n+1) = i_(n+1) | X_1 = i_1, dots, X_n = i_n) \
  = PP(X_(n+1) = i_(n+1) | X_n = i_n)
$
On dit de plus que la chaîne est homogène si
$
  forall i,j in E, n in NN, \
  PP(X_0 = j) > 0 \ => PP(X_(n+1) = i | X_n = j) = p_(i,j)
$
Ainsi par la formule des probabilités totales
$
  &PP(X_(n+1) = i) \ 
  =& sum_(j = 1)^N PP(X_(n+1) = i | X_n = j) PP(X_n = j) \
  =& sum_(j = 1)^N p_(i,j) PP(X_n = j)
$
Et donc en notant
$
  V_n = vec(PP(X_n = 1), dots.v, PP(X_n = N))
$
On a $V_(n+1) = P V_n$ avec
$
  P = (p_(i,j))_(i,j) in cal(M)_N (RR) \
$

*Propriétés*

On remarque que pour tout $j in [|1, N|]$
$
  sum_(i = 1)^N p_(i,j) &= sum_(i = 1)^N PP(X_1 = i | X_0 = j) \
  &= PP(X_1 in E | X_0 = j) = 1
$
Donc $P$ est une matrice stochastique, ainsi
$
  P^TT vec(1, dots.v, 1) = vec(1, dots.v, 1) \ 1 in "Sp"(P^TT) = "Sp"(P)
$
Et pour tout $lambda in "Sp"(P)$ et $vec(x_1, dots.v, x_N)$ vecteur propre non nul associé.
$
  P^TT vec(x_1, dots.v, x_N) = lambda vec(x_1, dots.v, x_N) quad abs(x_i_0) = max_(i in [|1, N|]) abs(x_i) \
  abs(lambda) dot abs(x_i_0) <= sum_(j = 1)^N abs(p_(j, i_0)) abs(x_i_0) = abs(x_i_0)
$
D'où $abs(lambda) <= 1$

// TODO: Exemple Markov M313

#card("jensenine", "Inégalité de Jensen pour les espérances", ("Maths.Probabilités",))

Inégalité de Jensen pour les espérances.

#answer

Soit $f : I -> RR$ convexe, et $X$ une vad à valeur dans $I$. Alors
$
  EE(f(X)) >= f(EE(X))
$
*Démonstration*

+ Cas $f$ $C^1$, pour tout $x in I$ #h(1fr)
  $
    f(x) >= f'(EE(X)) (x - EE(X)) + f(EE(X))
  $
  Ainsi, comme $X(Omega) subset.eq I$
  $
    f(X) >= f'(EE(X)) (X - EE(X)) + f(EE(X)) \
    EE(f(X)) >= f(EE(X))
  $

+ Dans le cas général, $f$ admet une droite d'appuis en tout points

  Pour tout $x in I$
  $
    f(x) >= f(EE(X)) + alpha(x - EE(X))
  $
  Avec $alpha in [f'_g (EE(X)), f'_d (EE(X))]$.

  Et on conclus de même.

#card("exingedf", "Exercice : troisième inégalité classique", ("Maths.Exercice.Probabilités",))

Soit $(X_k)_k in (LL^2)^NN^*$ indépendantes et centrées. 

On pose $S_n = sum_(k = 0)^n X_k$ et on suppose que
$
  sum_(k = 1)^(+oo) VV(X_k) = sum_(k = 1)^(+oo) EE(X_k^2) = sigma^2
$
Montrer que
$
  PP(max_(k in NN^*) abs(S_k) >= c) <= sigma^2 / c^2
$

#answer

Soit $(X_k)_k in (LL^2)^NN^*$ indépendantes et centrées.

On pose $S_n = sum_(k = 0)^n X_k$ et on suppose que
$
  sum_(k = 1)^(+oo) VV(X_k) = sum_(k = 1)^(+oo) EE(X_k^2) = sigma^2
$

On a déjà
$
  PP(abs(S_n) >= c) &= PP(S_n^2 >= c^2) <= EE(S_n^2) / c^2 \
  &= VV(S_n) / c^2 = sigma^2 / c^2
$

On pose
$
  A_k = (inter.big_(1 <= j <= k - 1) abs(S_j) <= c) inter (abs(S_k) > c) \
  B_n = (max_(1 <= k <= n) abs(S_n) > c) = union.plus.big_(k = 1)^n A_k
$
Ainsi
$
  bb(1)_B_n = sum_(k = 1)^n bb(1)_A_k \
  EE(S^2_n bb(1)_B_n) = sum_(k = 1)^n EE(S^2_n bb(1)_A_k)
$
Or
$
  S^2_n &= (S_k + sum_(j = k + 1)^n X_j)^2 \
  &= S_k^2 + 2 S_k (sum_(j = k + 1)^n X_j) + underbrace((sum_(j = k + 1)^n X_j)^2, >= 0)
$
D'où
$
  EE(S^2_n bb(1)_A_k) &>= EE(S^2_k bb(1)_A_k) \ 
  &+ 2 EE((S_k bb(1)_A_k) (sum_(j = k +1)^n X_j)) \
  &= EE(S^2_k bb(1)_A_k) \
  &+ 2 EE(S_k bb(1)_A_k) underbrace(EE(sum_(j = k +1)^n X_j), 0) \
  &= EE(S^2_k bb(1)_A_k)
  >= EE(c^2 bb(1)_A_k) \
  &>= c^2 PP(A_k)
$
Ainsi
$
  EE(S^2_n) &>= EE(S^2_n bb(1)_B_n) = sum_(k = 1)^n EE(S^2_n bb(1)_A_k) \
  &>= c^2 sum_(k = 1)^n PP(A_k) = c^2 PP(B_k)
$
D'où
$
  PP(B_k) <= EE(S_n^2) / c^2 = sigma^2 / c^2
$
Et par continuité croissante des probabilité on a le résultat.

#card("espsomein", "Espérance d'une série", ("Maths.Probabilités",))

Espérance d'une série.

#answer

Si $(A_k)_k in cal(T)^NN$ est une suite d'évenements, alors
$
  S = sum_(k = 0)^(+oo) bb(1)_A_k
$
Est une variable aléatoire discrète à valeur dans $NN union {+oo}$ et
$
  EE(sum_(k = 0)^(+oo) bb(1)_A_k) = EE(S) = sum_(k = 0)^(+oo) EE(bb(1)_A_k)
$

On peut généraliser ce résultat à $(X_k)_(k in NN)$ une suite de vad à valeur dans $NN$.

*Démonstration*

On pose
$
  S_n = sum_(k = 0)^n bb(1)_A_k
$

+ Montrons que $S$ est une variable aléatoire discrète. #h(1fr)
  $
    S(Omega) = underbrace(NN union {+oo}, "au plus dénombrable") \
    (S = k) = underbrace(union.big_(n >= k) (script(sum_(j = 0)^n bb(1)_A_j = k)) inter inter.big_(j >= n+1) overline(A_j), in cal(T)) \
    (S = +oo) = inter.big_(N in NN) union_(n >= N) A_n in cal(T)
  $

+ On remarque déjà que
  $
    sum_(k = 0)^n PP(A_k) = EE(S_n) <= EE(S)
  $
  Donc si $EE(S) < +oo$, $sum PP(A_n)$ converge.

  On suppose que $sum PP(A_n)$ converge.

  Par le lemme de Borel-Cantelli faible
  $
    PP(S = +oo) = PP(lim sup A_n) = 0
  $
  Or $EE(S) = sum_(n = 1)^(+oo) PP(S >= n)$, d'où par union croissante d'évenements
  $
    PP(S >= n) &= lim_(k -> oo) PP(S_k >= n) \
    sum_(n = 1)^N PP(S >= n) &= lim_(k -> oo) underbrace(sum_(n = 1)^N PP(S_k >= n), <= EE(S_k) = sum_(j = 0)^k PP(A_j)) \
    &<= sum_(k = 0)^(+oo) PP(A_k)
  $
  Donc $EE(S) <= sum_(n = 0)^(+oo) PP(A_n) < +oo$.

  On a ainsi l'équivalence de la convergence des deux sommes et leur égalité.

// NOTE: Correction marche aléatoires M316
