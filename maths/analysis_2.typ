#import "/cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/cetz:0.4.2"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

#card("derivevn", "Dérivabilité", ("Maths.Analyse.Espaces vectoriels normés",))

Définition de dérivabilité pour une fonction à valeur dans un evn.

#answer

Pour $f in cal(F)(I, E)$, où $I$ est un intervalle et $E$ un $RR$ ou $CC$-evn.

Soit $a in I$, on a équivalence entre

+ #h(1fr)
  $
    tau_a : func(I \\ {a}, E, x, (f(x) - f(a)) / (x - a)) 
  $
  Admet une limite finie $l in E$ en $a$.

+ On dispose de $l in E$ et $epsilon in cal(F)(I, E)$ tel que
  $
    f(x) = f(a) + (x - a)l + (x - a) epsilon(x) \
    "et " lim_(x -> a) epsilon(x) = 0
  $

Dans ce cas on dit que $f$ est dérivable en $a$ et on note
$
  l = f'(a) = lim_(x -> a) (f(x) - f(a)) / (x - a)
$

#card("linder", "Applications multi-linéaires et dérivation", ("Maths.Analyse.Espaces vectoriels normés",))

Formules de dérivation de $L(f)$, $B(f, g)$ et $M(f_1, dots, f_n)$.

#answer

Soient $E_1, dots, E_n, F$ des evn de dimension finie.

- Soit $L in cal(L)(E_1, F)$ et $f in cal(F)(I, E)$, si $f$ dérivable en $a in I$ :
  $
    (L compose f)'(a) = L(f') (a)
  $

- Soit $B : E_1 times E_2 -> F$ bilinéaire, $f, g in cal(F)(I, F)$, si $f$ et $g$ sont dérivables en $a in I$ :
  $
    (B(f, g))'(a) \ = B(f', g)(a) + B(f, g')(a)
  $

- Soit $M : product_(k = 1)^n E_k -> F$ $n$-linéaire, $f_1, dots, f_n in cal(F)(I, F)$. Si $f_1, dots, f_n$ sont dérivables en $a in I$ alors :
  $
    (M(f_1, dots, f_n))'(a) \
      = sum_(k = 1)^n M(f_1, dots, f_(k - 1), f'_k, f_(k+1), dots, f_n)(a)
  $

#card("derbout", "Théorème de Darboux", ("Maths.Analyse.Espaces vectoriels normés",))

Énoncé et démonstration du théorème de Darboux.

#answer

Soit $F in D^1(I, RR)$, pour tout $gamma in [F'(a), F'(b)]$ pour $a, b in I$ on dispose de $x in [a, b]$ tel que $F'(x) = gamma$.

*Démonstration*

Pour $gamma = 0$, supposons $F'(a) < 0, F'(b) > 0$
$
  min_[a,b] F in.not {F(a), F(b)}
$
Et $F C^0$ sur $[a, b]$

Donc on dispose de $x in [a, b]$ tel que $F(x) = min_[a, b] F$ et ainsi $F'(x) = 0$.

#card("inegevnfun", "Inégalités utiles", ("Maths.Analyse.Espaces vectoriels normés",))

Inégalités utiles qui tiennent pour les fonctions à valeur dans un evn de dimension finie.

#answer

+ Soit $f in C^1(I, E)$, pour tout $a, b in I$ : #h(1fr)
  $
    norm(f(a) - f(b)) <= abs(b - a) dot sup_[a, b] norm(f')
  $

+ Soit $f in C^(n+1)(I, E)$, pour tout $a, b in I$ :
  $
    norm(f(b) - sum_(k = 0)^n (b - a)^k / k! f^((k)) (a)) \
    <= abs(b - a) / (n+1)! sup_[a, b] norm(f^((n+1)))
  $

#card("cvs", "Convergence simple", ("Maths.Analyse.Suites et séries de fonctions",))

Propriétés, définition de la convergence simple.

#answer

Soit $(f_n)_n in cal(F) (A, E)^NN$, on dit que $(f_n)_n$ converge simplement vers $f in cal(F)(A, E)$ si
$
  forall x in A, lim_(n -> oo) f_n (x) = f(x)
$

La convergence simple conserve les propriétés suivantes :

- Si les $f_n$ sont croissants, $f$ aussi.
- Si les $f_n$ sont $k$-lipschitzien, $f$ aussi.
Si $A = I$ intervalle et $E = RR$

- Si les $f_n$ sont bornés par $M$, $f$ aussi.
- Si les $f_n$ sont convexes, $f$ aussi.

#card("exsuitesdepol", "Exercice : suite de polynômes, convergence uniforme", ("Maths.Exercice.Analyse",))

+ Soit $(P_n)_n in RR[X]^NN tends(n -> oo, above: "CVU") f in cal(F)(RR, RR)$, montrer que $f$ est polynômiale.

+ Soit $(P_n)_n in RR_d [X]^NN tends(n -> oo, above: "CVS") Q in RR_d [X]$, montrer que $(P_n)_n$ converge uniformement sur tout segment.

+ Soit $(P_n)_n in RR_d [X]^NN tends(n -> oo, above: "CVS") f in cal(F)(RR, RR)$, montrer que $f in RR_d [X]$.

#answer

+ Soit $N in NN$ tel que pour tout $n >= N$, $P_n - f$ bornée (possible car $norm(P_n - f)_oo -> 0$).

  $
    P_N - P_n = (P_N - f) - (P_n - f)
  $
  Différence de fonctions bornées, donc bornée et somme de polynômes de polynômiale.

  D'où
  $
    P_N - P_n &= alpha_n in RR \
    &tends(n -> oo) P_N - f = beta in RR
  $
  Donc $f = P_N + beta in RR[X]$.

+ Soit $[a, b] subset.eq RR$, $alpha_0, dots, alpha_d in [a, b]$ distincts.
  $
    N_d : func(RR_d [X], RR_+, P, max_(k in [|0, d|]) abs(P(alpha_k)))
  $
  Par CVS, $(P_n)_n$ converge vers $Q$ au sens de la norme $N_d$, qui est équivalente à la norme infinie car en dimension finie.

+ De même, par interpollation de Lagrange on prend $Q$ coincident avec $f$ en $d + 1$ points, et on définit la même norme :
  $
    N_d (P_n - Q) tends(n -> oo) 0
  $
  Donc au sens de la norme infinie : $P_n -> Q = f$.

#card("thc0sfn", "Théorème de continuité pour les suites de fonctions", ("Maths.Analyse.Suites et séries de fonctions", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé, démonstration du théorème de continuité pour les suites de fonctions.

#answer

Soit $(f_n)_n in cal(F)(A, F)^NN tends(n -> oo, above: "CVS") f in cal(F)(A, F)$, $a in A$. Si

+ $(f_n)_n$ CVU sur un voisinage de $a$.

+ $forall n in NN, f_n C^0$ en $a$.

Alors $f$ est $C^0$ en $a$.

*Démonstration*

Soit $epsilon > 0$, $N in NN$ associé par CVU, $delta > 0$ associé par continuité de $f_N$, ainsi pour tout $x in B(a, delta) inter A$
$
  norm(f(x) - f(a))  <=& underbrace(norm(f(x) - f_N (x)), < epsilon)\ +& underbrace(norm(f_N (x) - f_N (a)), < epsilon) \ +& underbrace(norm(f_N (a) - f(a)), < epsilon) \
  < & 3 epsilon
$

#card("thdbllimsfn", "Théorème de la double limite pour les suites de fonctions", ("Maths.Analyse.Suites et séries de fonctions", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé, démonstration du théorème de la double limite pour les suites de fonctions.

#answer

Soit $(f_n)_n in cal(F)(A, F)^NN tends(n -> oo, above: "CVS") f in cal(F)(A, F)$, $a in overline(A)$. Si

+ $(f_n)_n$ CVU sur un voisinage de $a$.

+ $forall n in NN, lim_(x -> a) f_n (x) = l_n$.

Alors
$
  lim_(n -> oo) l_n &= l in overline(F) \ &= lim_(n -> oo) lim_(x -> a) f_n (x) \ &= lim_(x -> a) lim_(n -> oo) f_n (x)
$

*Démonstration (Idée)*

$
  norm(l_n - l_m) <= norm(f_n - f_m)_oo "de Cauchy"
$

#card("thprimsfn", "Théorème de primitivation pour les suites de fonctions", ("Maths.Analyse.Suites et séries de fonctions", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé, démonstration du théorème de primitivation pour les suites de fonctions.

#answer

Soit $(f_n)_n in C^0_"pm" (I, G)^NN$ ($G$ evn de dimension finie, $I$ intervalle de $RR$), $a in A$. Si

+ $(f_n)_n$ CVU sur tout segment de $I$ vers $f in C^0_"pm"$.

En notant 
$
  F_n : func(I, G, x, integral_a^x f_n (t) dif t) \
  F : func(I, G, x, integral_a^x f(t) dif t) \
$

Alors $F_n$ CVU sur tout segment vers $F$

*Corolaire*

Pour $(f_n)_n in C^0_"pm" ([a, b], F)^NN tends([a, b], above: "CVU") f in C^0_"pm" ([a, b], F)$.

$
  integral_a^b f_n (t) dif t tends(n -> oo) integral_a^b f(t) dif t
$

*Démonstration*

Soit $K$ segment, $M = abs(sup K - inf K)$, quitte à le grandire, $a in K$.

Soit $epsilon > 0$, on dispose de $N in NN$ tel que pour tout $n >= N$,
$
  norm(f_n - f)_oo < epsilon
$
Ainsi
$
  norm(F(x) - F_n (x)) &= norm(integral_a^x (f(t) - f_n (t) ) dif t) \
  &<= abs(x - a) epsilon \
  &<= M epsilon
$

#card("thc1sfn", "Théorème de dérivation pour les suites de fonctions", ("Maths.Analyse.Suites et séries de fonctions", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé, démonstration du théorème de dérivation pour les suites de fonctions.

#answer

Soit $(f_n)_n in C^1(I, G)^NN tends(n -> oo, above: "CVS") f$. Si

+ $(f'_n)_n$ CVU sur tout segment vers $g$.

Alors $(f_n)_n$ CVU vers $f$ sur tout segment et $f in C^1$ et $f' = g$ :
$
  (lim_(n -> oo) f_n)' = lim_(n -> oo) f'_n
$

*Démonstration*

Par théorème de primitivation.

#card("thcksfn", "Théorème de dérivation k-ème pour les suites de fonctions", ("Maths.Analyse.Suites et séries de fonctions", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé, démonstration du théorème de dérivation k-ème pour les suites de fonctions.

#answer

Soit $(f_n)_n in C^k (I, F)^NN$, si

+ Pour tout $j in [|0, k-1|]$, $(f^((j))_n)_n$ CVS vers $g_j$.

+ $(f^((k))_n)_n$ CVU sur tout segment vers $g_k$.

Alors

Pour tout $j in [|0, k|]$, $(f^((j))_n)_n$ CVU sur tout segment vers $g_j = g_0^((j))$, $g_0$ qui est $C^k$.

*Démonstration*

Récurrence à l'aide du théorème de dérivation.

#card("thc0serfn", "Théorème de continuité pour les séries de fonctions", ("Maths.Analyse.Suites et séries de fonctions", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé, démonstration du théorème de continuité pour les séries de fonctions.

#answer

Soit $(f_n)_n in cal(F) (A, F)^NN$, $a in A$. Si

+ $sum f_n$ CVS.

+ $sum f_n$ CVU sur un voisinage de $a$.

+ Pour tout $n in NN$, $f_n$ est continue en $a$.

Alors $S : x |-> sum_(n = 0)^(+oo) f_n (x)$ est continue en $a$.

*Démonstration*

On applique le théorème de continuité pour les suites de fonctions à $S_n = sum_(k = 0)^n f_n$.

#card("thdbllimserfn", "Théorème de la double limite pour les séries de fonctions", ("Maths.Analyse.Suites et séries de fonctions", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé, démonstration du théorème de la doulbe limite pour les séries de fonctions.

#answer

Soit $(f_n)_n in cal(F)(A, F)^NN$, $a in overline(A)$. Si

+ $sum f_n$ CVS.

+ Pour tout $n in NN$, $lim_(x -> a) f_n (x) = l_n in overline(F)$.

+ $sum f_n$ CVU sur un voisinage de $a$.

Alors $sum l_n$ converge et
$
  sum_(n = 0)^(+oo) l_n &= sum_(n = 0)^(+oo) lim_(x -> a) f_n (x) \ &= lim_(x -> a) sum_(n = 0)^(+oo) f_n (x)
$

*Démonstration*

On applique le théorème de la double limite pour les suites de fonctions à $S_n = sum_(k = 0)^n f_n$.

#card("thc1serfn", "Théorème de dérivation pour les séries de fonctions", ("Maths.Analyse.Suites et séries de fonctions", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé, démonstration du théorème de dérivation pour les séries de fonctions.

#answer

Soit $(f_n)_n in C^1 (I, F)^NN tends(n -> oo, above: "CVS") S$. Si

+ $sum f'_n$ CVU sur tout segment de $I$.

Alors $sum f_n$ CVU sur tout segment de $I$, et $S in C^1 (I, F)$ et $S' = sum_(n = 0)^(+oo) f'_n$.

*Démonstration*

On applique le théorème de dérivation pour les suites de fonctions à $S_n = sum_(k = 0)^n f_n$.

#card("thckserfn", "Théorème de dérivation k-ème pour les séries de fonctions", ("Maths.Analyse.Suites et séries de fonctions", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé, démonstration du théorème de dérivation k-ème pour les séries de fonctions.

#answer

Soit $(f_n)_n in C^1 (I, F)^NN$. Si

+ Pour tout $j in [|0, k - 1|]$, $sum f^((j))_n$ CVS sur $I$.

+ $sum f^((k))_n$ CVU sur tout segment de $I$.

Alors pour tout $j in [|0, k|]$, $sum f^((j))_n$ CVU sur tout segment de $I$ et 
$
  S = sum_(n = 0)^(+oo) f_n in C^k (I, F) \
  forall j in [|0, k|], space S^((j)) = sum_(n = 0)^(+oo) f^((j))_n
$

*Démonstration*

On applique le théorème de dérivation k-ème pour les suites de fonctions à $S_n = sum_(k = 0)^n f_n$.

#card("thprimserfn", "Théorème de primitivation pour les séries de fonctions", ("Maths.Analyse.Suites et séries de fonctions", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé, démonstration du théorème de primitivation pour les séries de fonctions.

#answer

Soit $(f_n)_n in C^0_"pm" (I, F)^NN$, $a in I$. Si

+ $sum f_n$ CVU sur tout segment.

+ $s = sum_(n = 0)^(+oo) f_n in C^0_"pm" (I, F)$.

En notant
$
  F_n (x) = integral_a^x f_n (t) dif t \
  S(x) = integral_a^x s (t) dif t
$

Alors $sum F_n$ CVU sur tout segment vers $S$

*Corolaire*

Pour $(f_n)_n in C^0_"pm" ([a, b], F)^NN$ tel que $sum f_n$ CVU sur $[a, b]$ et $S = sum_(n = 0)^(+oo) f_n$ est $C^0_"pm"$.

$
  integral_a^b sum_(n = 0)^(+oo) f_n (t) dif t = sum_(n = 0)^(+ oo) integral_a^b f_n (t) dif t
$

*Démonstration*

On applique le théorème de primitivation pour les suites de fonctions à $S_n = sum_(k = 0)^n f_n$.

#card("thcvd", "Théorème de convergence dominée", ("Maths.Analyse.Intégration", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé du théorème de convergence dominée.

#answer

Soit $(f_n)_n in C^0_"pm" (I, KK)^NN$, avec $I$ un intervalle. Si

+ $f_n tends(n -> oo, above: "CVS") f$ sur I.

+ $f C^0_"pm"$.

+ Il existe $phi in C^0_"pm" (I, RR_+)$ intégrable sur $I$ tel que #h(1fr)
  $
    forall n in NN, forall t in I, abs(f_n (t)) <= phi(t)
  $

Alors $f_n$ et $f$ sont intégrables sur $I$ et
$
  lim_(n -> oo) integral_I f_n (t) dif t &= integral_I f(t) dif t \ &= integral_I lim_(n -> oo) f_n (t) dif t
$

#card("thtat", "Théorème d'intégration terme à terme", ("Maths.Analyse.Intégration", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé du théorème d'intégration terme à terme.

#answer

- Version positive : #h(1fr)

  Soit $(f_n)_n in C^0_"pm" (I, RR_+)^NN$, avec $I$ un intervalle. Si

  + $sum f_n$ CVS sur $I$.

  + $t |-> sum_(n = 0)^(+oo) f_n (t)$ est $C^0_"pm"$ sur $I$.

  Alors dans $RR_+ union {+oo}$ :
  $
    integral_I sum_(n = 0)^(+oo) f_n (t) dif t = sum_(n = 0)^(+oo) integral_I f_n (t) dif t
  $

- Version générale :

  Soit $(f_n)_n in C^0_"pm" (I, KK)^NN$, avec $I$ un intervalle. Si

  + $sum f_n$ CVS sur $I$.

  + $S : t |-> sum_(n = 0)^(+oo) f_n (t)$ est $C^0_"pm"$ sur $I$.

  + Pour tout $n in NN$, $f_n$ est intégrable sur $I$ et
    $
      sum_(n = 0)^(+oo) integral_I abs(f_n (t)) dif t < +oo
    $

  Alors $S$ est intégrable sur $I$ et
  $
    integral_I S(t) dif t &= integral_I sum_(n = 0)^(+oo) f_n (t) dif t \
    &= sum_(n = 0)^(+oo) integral_I f_n (t) dif t
  $

#card("thcvscont", "Théorème de convergence dominée par un paramètre continue", ("Maths.Analyse.Intégration", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé et démonstration du théorème de convergence dominée par un paramètre continue.

#answer

Soit $A subset.eq RR$, $(f_lambda)_lambda in C^0_"pm" (I, KK)^A$, $a in overline(A)$. Si

+ $forall x in I, f_lambda (x) tends(lambda -> a) f(x)$.

+ $f$ est $C^0_"pm"$ sur $I$.

+ Il existe $phi in C^0_"pm" (I, RR_+)$ intégrable sur $I$ tel que
  $
    forall t in I, forall lambda in A, abs(f_lambda (t)) <= phi(t)
  $

Alors les $f_lambda$ et $f$ sont intégrables sur $I$ et
$
  lim_(lambda -> a) integral_I f_lambda (t) dif t = integral_I lim_(lambda -> a) f_lambda (t) dif t
$

*Démonstration*

Critère séquentiel, on montre que le résultat est vrai pour toute suite $(lambda_n)_n tends(n -> oo) a$.

#card("thc0intp", "Théorème de continuité pour les intégrales à paramètre", ("Maths.Analyse.Intégration", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé et démonstration du théorème de continuité pour les intégrales à paramètre.

#answer

Soit $f: func(A times I, KK, (x, t), f(x, t))$, avec $A subset.eq E$ evn de dimension finie et $I$ intervalle. Si

+ $forall t in I$, $x |-> f(x, t)$ est $C^0$ sur $A$.

+ $forall x in A$, $t |-> f(x, t)$ est $C^0_"pm"$ sur $I$.

+ $forall a in A, exists V_a in cal(V)(a), exists phi_a in C^0_"pm" (I, RR_+), integral_I abs(phi(t)) dif t < +oo$,
  $
    forall t in I, forall x in V_a, abs(f(x, t)) <= phi(t)
  $

Alors
$
  g: func(A, KK, x, integral_I f(x, t) dif t)
$
Est bien définie et continue sur $A$.

*Démonstration*

Critère séquentiel et théorème de convergence dominée.

#card("thc1intp", "Théorème de dérivation pour les intégrales à paramètre", ("Maths.Analyse.Intégration", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé et démonstration du théorème de dérivation pour les intégrales à paramètre.

#answer

Soit $f : func(J times I, KK, (x, t), f(x, t))$, avec $I, J$ des intervalles. Si

+ $forall t in I, x |-> f(x, t)$ est $C^1$ sur $J$.

+ $forall x in J, t |-> f(x, t)$ est $C^0_"pm"$ et intégrable sur $I$.

+ $forall x in J, t |-> pdv(f, x) (x, t)$ est $C^0_"pm"$ sur $I$.

+ $forall K = [a, b] subset.eq J, exists phi_K in C^0_"pm" (I, RR_+)$,$integral_I phi_K (t) dif t < +oo$,
  $
    forall x in K, forall t in I, space abs(pdv(f, x) (x, t)) <= phi_K (t)
  $

Alors
$
  g : func(J, KK, x, integral_I f(x, t) dif t)
$
Est bien définie, est $C^1$ sur $J$ et 
$
g' : func(J, KK, x, integral_I pdv(f, x) (x, t) dif t)
$

*Démonstration*

Récurrence avec le théorème de dérivation.

#card("thckintp", "Théorème de dérivation k-ème pour les intégrales à paramètre", ("Maths.Analyse.Intégration", "Maths.Analyse.Théorèmes d'interversion"))

Énoncé et démonstration du théorème de dérivation k-ème pour les intégrales à paramètre.

#answer

Soit $f : func(J times I, KK, (x, t), f(x, t))$, avec $I, J$ des intervalles. Si

+ $forall t in I, x |-> f(x, t)$ est $C^k$ sur $J$.

+ $forall x in J, forall j in [|0, k - 1|]$, $t |-> pdv(f, x, [j])(x, t)$ est $C^0_"pm"$ et intégrable sur $I$.

+ $forall x in J, t |-> pdv(f, x, [k]) (x, t)$ est $C^0_"pm"$ sur $I$.

+ $forall K = [a, b] subset.eq J, exists phi_K in C^0_"pm" (I, RR_+)$,$integral_I phi_K (t) dif t < +oo$,
  $
    forall x in K, forall t in I, space abs(pdv(f, x, [k]) (x, t)) <= phi_K (t)
  $

Alors
$
  g : func(J, KK, x, integral_I f(x, t) dif t)
$
Est bien définie, est $C^k$ sur $J$ et pour tout $j in [|0, k|]$, 
$
g^((j)) : func(J, KK, x, integral_I pdv(f, x, [j]) (x, t) dif t)
$

*Démonstration*

On montre $C^0$ avec le théorème de continuité, puis on montre la dérivabilité par le théorème de convergence dominée en calculant la limite usuelle.

#card("densifunc", "Espaces denses de fonctions", ("Maths.Analyse.Suites et séries de fonctions",))

Exemples d'espaces denses de fonctions.

#answer

*Fonctions en escaliers*

Les fonctions en escalier sont denses dans les fonctions $(C^0_"pm" ([a,b], E), norm(dot)_oo)$.

*Fonctions polynômiales (Théorème de Weierstrass)*

Les fonctions polynômiales sur $[a, b]$ sont denses dans $(C^0 ([a, b], KK), norm(dot)_oo)$.

// TODO: Exos M230-231

#card("dini1", "Premier théorème de Dini", ("Maths.Analyse.Suites et séries de fonctions",))

Énoncé et démonstration du premier théorèmes de dini (HP).

#answer

Soit $K$ compact, $(f_n)_n in C^0(K, RR)^NN tends(n -> oo, above: "CVS") f in C^0(K, RR)$.

Si pour tout $x in KK$, $(f_n (x))_n$ est monotone, alors $(f_n)_n$ CVU vers $f$.

*Démonstration*

On note
$
  g_n = cases(space f_n - f " si " (f_n (x))_n arrow.br, space f - f_n " sinon" )
$
Ainsi $g_n >= 0$, décroit et CVS vers $0$. On veut montrer que $norm(f_n - f)_oo = norm(g_n)_oo tends(n -> oo) 0$.

Soit $epsilon > 0$, $K_n = Set( x in K, g_n (x) >= epsilon ) = g_n^(-1) Ico(epsilon, +oo)$, fermé dans $K$ donc compact par continuité de $g_n$.

Par décroissance de $g_n$, $(K_n)_n$ est une suite décroissante de compacts.

Supposons que les $K_n$ soient tous non vide, alors on dispose de $x_0 in inter.big_(n in NN) K_n$ (Intersection décroissante de compacts non vide).

Or
$
  inter.big_(n in NN) K_n &= Set(x in K \, forall n in NN, g_n (x) >= epsilon) \
  &= emptyset quad "Par CVS de" (g_n)_n
$

Absurde. Donc on dispose de $N in NN$ tel que pour tout $n >= N$, $K_n = emptyset$, c'est à dire $norm(g_n)_oo < epsilon$.

#card("dini2", "Deuxième théorème de Dini", ("Maths.Analyse.Suites et séries de fonctions",))

Énoncé et démonstration du deuxième théorèmes de dini (HP).

#answer

Soit $(f_n)_n in C^0([a, b], RR)^NN tends(n -> oo, above: "CVS") f in C^0([a, b], RR)$.

Si pour tout $n in NN$, $f_n$ est croissante (ou décroissante), alors $(f_n)_n$ CVU vers $f$.

*Démonstration*

Quitte à prendre $-f_n$ on suppose les $f_n$ croissants, et par CVS $f$ aussi.

Par le théorème de Heine, $f$ est uniformement continue sur $[a, b]$.

Soit $epsilon > 0$, $delta > 0$ associé, et $N in NN^*$ tel que $(b - a) / N < delta$. On pose pour $k in [|0, N|], a_k = a + k (b - a) / N$.

Pour tout $x in [a, b]$, on dispose de $k in [|0, N|]$ tel que $x in [a_k, a_(k + 1)]$.

Par CVS de $(f_n)_n$ vers $f$, pour tout $k in [|0, N|]$, on dispose de $n_k in NN$ tel que pour tout $n >= n_k$
$
  abs(f_n (a_k) - f(a_k)) < epsilon
$
On pose $N_0 = max_(k in [|0, N|]) n_k$.

Ainsi pour tout $n >= N_0$
$
  underbrace(f_n (a_k) - f(a_k), -epsilon < " par CVS") + underbrace(f(a_k) - f(a_(k+1)), - epsilon < " par UC") \
  = f_n (a_k) - f(a_(k+1)) <= f_n (x) - f(x) \
  <= underbrace(f_n (a_(k+1)) - f(a_(k + 1)), < epsilon " par CVS") + underbrace(f(a_(k + 1)) - f(a_k), < epsilon " par UC") \
  - 2 epsilon < f_n (x) - f(x) < 2 epsilon
$

#card("equicont", "Équicontinuité", ("Maths.Analyse.Suites et séries de fonctions",))

Définitions, propriétés de (uniforme) équicontinuité.

#answer

Soit $cal(F) : (f_i)_i in C^0 (A, F)^I$ une famille de fonctions continues, on dit que $cal(F)$ est équicontinue en $a in A$ si
$
  forall epsilon > 0, exists delta > 0, forall i in I, \ forall x in B(a, delta), d(f_i (x), f_i (a)) < epsilon
$

On dit de plus que $cal(F)$ est uniformement équicontinue si
$
  forall epsilon > 0, exists delta > 0, forall i in I,
  forall x, y in A, \ d(x, y) < delta => d(f_i (x), f_i (y)) < epsilon
$

*Propriétés*

- Si $(f_n)_n in C^0 (A, F)^NN tends("sur " A, above: "CVU") f in C^0 (A, F)$, alors $(f_n)_n$ est équicontinue sur $A$.

- Soit $K$ compact, si $(f_n)_n in C^0 (K, F)^NN tends("sur " K, above: "CVU") f in C^0 (A, F)$, alors $(f_n)_n$ est uniformement équicontinue.

- Soit $(f_i)_i in cal(F)(A, F)^I$, si les $f_i$ sont tous $k$-lipschitz, alors $(f_i)_i$ est uniformement équicontinue.

*Démonstration*

- Découpage : on fixe $N$ par CVU associé à $epsilon$, et on prend $delta$ le min des $delta_k$ associés aux $f_k$ pour $k in [|0, N - 1|]$ et $delta_N$ associé à $f$.

- La même avec Heine pour en déduire l'uniforme continuité des $(f_n)$ et de $f$.

- Soit $epsilon > 0$, on pose $delta = epsilon / k$ qui convient pour tout $i in I$.

#card("cvscvuuec", "Convergence uniforme par convergence simple et uniforme équicontinuité", ("Maths.Analyse.Suites et séries de fonctions",))

Démonstration de la convergence uniforme par convergence simple et uniforme équicontinuité.

#answer

Soit $(f_n)_n in C^0 ([a, b], F)^NN tends(n -> oo, above: "CVS") f$.

Si $(f_n)_n$ est uniformement équicontinue, alors $(f_n)_n$ CVU vers $f$.

($f_n$ $k$-lipschitz pour tout $n in NN$ suffit car implique uniforme équicontinue).

*Démonstration*

Soit $epsilon > 0$, $delta > 0$ associé par uniforme équicontinuité. $N in NN$ tel que $(b - a) / N < delta$, et pour $k in [|0, N|]$, $a_k = a + k (b - a) / N$.

Pour tout $x, y in [a, b]$ tel que $abs(x - y) < delta$, comme pour tout $n in NN$
$
  norm(f_n (x) - f_n (y)) < epsilon
$
Par CVS, à la limite
$
  norm(f(x) - f(y)) < epsilon
$

Soit $N_0 in NN$ tel que pour tout $n >= 0, k in [|0, N|]$,
$
  norm(f(a_k) - f_n (a_k)) < epsilon
$

Soit $x in [a, b]$, $k in [|0, N|]$ tel que $x in [a_k, a_(k + 1)]$.

$
  norm(f(x) - f_n (x)) &<= underbrace(norm(f(x) - f(a_k)), < epsilon) \ &+ underbrace(norm(f(a_k) - f_n (a_k)), < epsilon) \ &+ underbrace(norm(f_n (a_k) - f_n (x)), < epsilon) \ &< 3 epsilon
$

On peut montrer ce resultat pour $K$ compact quelconque (au lieu de $[a, b]$), le découpage se faisant par précompacité.

#card("modeconvseries", "Modes de convergence des séries de fonctions", ("Maths.Analyse.Suites et séries de fonctions",))

Modes de convergence des séries de fonctions.

#answer

Soit $(f_n)_n in cal(F)(A, F)^NN$, pour tout $n in NN$
$
  S_n = sum_(k = 0)^n f_n
$

- On dit que $sum f_n$ CVS (simplement) sur $A$ si pour tout $x in A$, $sum f_n (x)$ converge.
  
  On peut alors écrire #h(1fr)
  $
    S : func(A, F, x, sum_(n = 0)^(+oo) f_n (x))
  $

- On dit que $sum f_n$ CVU (uniformement) sur $A$ si $(S_n)$ CVU sur $A$.

  Ce qui est équivalent à $sum f_n$ CVS et
  $
    R_n = sum_(k = n + 1)^(+oo) f_k tends(n -> oo, above: "CVU") 0
  $

- On dit que $sum f_n$ CVA (absolument) sur $A$ si pour tout $x in A$, $sum f_n (x)$ est ACV.

  Si $F$ est de dimension finie, alors CVA implique CVS.

- On dit que $sum f_n$ CVN (normalement) sur $A$ si
  - Pour tout $n in NN$, $f_n$ est bornée.
  - $sum norm(f_n)_(oo, A)$ converge.

  La CVN implique la CVA et CVU, donc CVS.

// TODO: exp matrices, (voir chapitre suivant ?) (M236)

// TODO: Méthodes équivalents / limites séries de fonctions (M240-241)

// TODO: Développement en série de cotan (M241-242)

#card("ascoli", "Théorème d'Ascoli", ("Maths.Analyse.Suites et séries de fonctions",))

Énoncé, démonstration du Théorème d'Ascoli.

#answer

Soit $F$ de dimension finie, $K$ compact et $E = C^0 (K, F)$ muni de $norm(dot)_oo$. Soit $cal(F) subset.eq E$, on a équivalence entre

+ $cal(F)$ relativement compact.

+ $cal(F)$ est uniformement équicontinue et pour tout $x in K$, $Gamma(x) = {f(x), f in cal(F)}$ est bornée (c'est à dire relativement compact).

*Démonstration*

- (i $=>$ ii) On suppose $overline(cal(F))$ compact, soit $x in K$. On pose #h(1fr)
  $
    theta_x : func(E, F, f, f(x)) 
  $
  Qui est linéaire et $norm(theta_x (f)) <= norm(f)_oo$ donc continue.

  Comme $Gamma(x) = theta_x (cal(F)) subset.eq theta_x (overline(cal(F)))$, $Gamma(x)$ est relativement compact.

  $cal(F)$ est relativement compact donc donc précompact. 

  Soit $epsilon > 0$, on dispose alors de $f_1, dots, f_d subset.eq cal(F)$ tels que $cal(F) subset.eq union.big_(k = 0)^d B(f_k, epsilon)$.

  Les $f_k$ sont continue sur $K$, donc uniformement continue, soit $delta > 0$ associé à $epsilon$ pour l'ensemble.

  Soit $x, y in K$ tel que $norm(x - y) < delta$, $f in cal(F)$, on dispose donc de $k in [|0, d|]$ tel que $norm(f - f_k)_oo < epsilon$ 
  $
    norm(f(x) - f(y)) &<= underbrace(norm(f(x) - f_k (x)), < epsilon) \
    &+ underbrace(norm(f_k (x) - f_k (y)), < epsilon) \
    &+ underbrace(norm(f_k (y) - f(y)), < epsilon) \
    &< 3 epsilon
  $

  Donc $cal(F)$ est uniformement équicontinue.

- (ii $=>$ i) On introduit $(a_n)_n in K^NN$ dense.

  Si $K = [a, b]$, $K inter QQ$ convient.

  Sinon par précompacité, avec $epsilon_n = 1 / 2^n$, on dispose de $D_n$ fini tel que $K subset.eq union.big_(x in D_n) B(x, epsilon_n)$, d'où $D = union.big_(n in NN) D_n$ convient.

  Montrons que $cal(F)$ est relativement compact.

  Soit $(f_n)_n in cal(F)^NN$.

  + On construit $psi$ tel que pour tout $k in NN$, $(f_psi(n) (a_k))_n$ converge.

    $(f_n (a_0)) in Gamma (a_0)^NN$, par hypothèse on dispose de $phi_0$ tel que $(f_(phi_0 (n)) (a_0)) -> z_0 = g(a_0)$.

    Supposons construits $phi_0, dots, phi_(k - 1)$ tel que pour tout $j in [|0, k - 1|]$.
    $
      (f_(phi_0 compose dots.c compose phi_(k - 1) (n)) (a_j))_n -> z_j = g(a_j)
    $
    Comme $Gamma(a_(k +1))$ est relativement compact, on dispose de $phi_(k + 1)$ tel que
    $
      (f_(phi_0 compose dots.c compose phi_k (n)) (a_k))_n -> z_k = g(a_k)
    $
    On pose
    $
    psi : func(NN, NN, n, phi_0 compose dots.c compose phi_n (n) )
    $
    Qui est strictement croissante et pour tout $k in NN$
    $
    (f_psi(n) (a_k)) tends(n -> oo) z_k = g(a_k)
    $

  + Par uniforme équicontinuité et densité de $(a_k)_k$, montrons que $(f_psi(n))_n$ CVS sur $K$.

    Soit $x in K$, posons $g_n = f_psi(n)$.

    On sait que $(g_n (x))_n in Gamma(x)^NN$ donc on dispose de $theta$ tel que
    $
      g_theta(n) (x) tends(n -> oo) y in F
    $
    Soit $epsilon > 0$, $delta > 0$ associé par uniforme équicontinuité de $cal(F)$, et par densité de $(a_k)_k$, on dispose de $k in NN$ tel que $norm(a_k - x) < delta$.

    Comme $g_n (a_k) tends(n -> oo) z_k$, on dispose de $N in NN$ tel que pour tout $n >= N$.

    Ainsi pour tout $n >= N$
    $
      &norm(g_n (x) - g_theta(n) (x)) \
      <=& underbrace(norm(g_n (x) - g_n (a_k)), < epsilon) \
      +& underbrace(norm(g_n (a_k) - z_k), < epsilon) \
      +& underbrace(norm(z_k - g_theta(n) (a_k)), < epsilon) \
      +& underbrace(norm(g_theta(n) (a_k) - g_theta(n) (x)), < epsilon) \
      <& 4 epsilon
    $

    Soit $N_0 >= N$ tel que pour tout $n >= N_0$
    $
      norm(g_theta(n) (x) - y) < epsilon \
      norm(g_n (x) - y) < 5 epsilon
    $

    Ainsi pour tout $x in K$, $(f_psi(n) (x))_n$ converge vers un $y = g(x)$.

  + On a $(f_psi(n))_n$ uniforme équicontinue qui CVS vers $g$, donc qui CVU, c'est à dire qui converge au sens de la norme infinie : $cal(F)$ est relativement compact.

// TODO: Exos (M244.1-246)

// TODO: Fourier (M253)

#card("methequiintp", "Méthodes de recherche de limite ou d'équivalent pour les intégrales à paramètre", ("Maths.Analyse.Intégration",))

Méthodes de recherche de limite ou d'équivalent pour les intégrales à paramètre.

#answer

- Théorème de convergence dominée, ou domination "à la main" (Limite).

- Changement de variable.

- Intuition (i.e intégration d'équivalent).

- IPP : séparation en un terme plus simple et un terme négligeable.

- Méthode de Laplace // Cf M256

// TODO: Carte inutile ? (M255)

// TODO: Gamma (M257)

#card("rayconv", "Rayon de convergence d'une séries entière", ("Maths.Analyse.Séries entières",))

Propriétés, définition du convergence d'une séries entière.

#answer

Soit $sum a_n z^n$ une série entière. On appelle $R = R_"cv" (sum a_n z^n)$ le rayon de convergence de $sum a_n z^n$
$
  R = sup space Set(r in RR_+, (a_n r^n) "bornée")
$

- (Lemme d'Abel) : Si $(a_n z_0^n)$ est bornée, alors pour tout $z in CC$ tel que $abs(z) < abs(z_0)$, $sum a_n z^n$ est ACV.

- Pour tout $z in CC$ (conséquence) : #h(1fr)
  $
    abs(z) < R quad quad sum a_n z^n "ACV" \
    abs(z) > R quad quad sum a_n z^n "DVG" \
  $

- Pour tout $alpha in CC^*$
  $
    R_"cv" (sum alpha a_n z^n) = R_"cv" (sum a_n z^n)
  $

- Pour tout $alpha in CC^*$
  $
    R_"cv" (sum a_n alpha^n z^n) = (R_"cv" (sum a_n z^n)) / abs(alpha)
  $

- Si pour tout $n in NN$, $abs(a_n) <= abs(b_n)$
  $
    R_"cv" (sum a_n z^n) >= R_"cv" (sum b_n z^n)
  $

- Si $a_n = O_(n -> oo)(b_n)$
  $
    R_"cv" (sum a_n z^n) >= R_"cv" (sum b_n z^n)
  $

- Si $a_n eqv(n -> oo) b_n$
  $
    R_"cv" (sum a_n z^n) = R_"cv" (sum b_n z^n)
  $

- Soient $(a_n)_n, (b_n)_n in CC^NN$
  $
    R_"cv" (sum (a_n + b_n) z^n) >= min(R_a, R_b)
  $
  Avec égalité si $R_a != R_b$.

- Soient $(a_n)_n, (b_n)_n in CC^NN$.
  $
      c_n = sum_(k = 0)^n a_k b_(n - k) \

      R_"cv"(sum c_n z^n) >= min (R_a, R_b) \

      forall z in DD(0, R_"cv"), \ sum_(n = 0)^(+oo) c_n z^n = (sum_(n = 0)^(+oo) a_n z^n) (sum_(n = 0)^(+oo) b_n z^n)
  $

#card("regse", "Régularité des séries entières", ("Maths.Analyse.Séries entières",))

Régularité des séries entières.

#answer

Soit $(a_n)_n in CC^NN$ et $R = R_"cv" (sum a_n z^n)$.

Pour tout $0 < r < R$
$
  f : func(DD(0, r), CC, z, sum_(n = 0)^(+oo) a_n z^n)
$
Est $C^0$ sur $DD(0, r)$,
$
  g : func(Ioo(-R, R), CC, x, sum_(n = 0)^(+oo) a_n x^n)
$
Est $C^oo$ sur $Ioo(-R, R)$. Et pour tout $k in NN$
$
  f^((k)) : x |-> sum_(n = 0)^(+oo) (n + k)! / n! a_(n + k) x^n
$

*Démonstration*

- Pour tout $r < R$ on a CVU de 
  $
    f : func(DD(0, r), CC, z, sum_(n = 0)^(+oo) a_n z^n)
  $
  Et donc par le théorème de continuité des séries de fonctions, $f$ est $C^0$ sur $DD(0, r)$.

- $R_"cv" (sum n a_n z^n) = R_"cv" (sum a_n z^n)$ :

  Soit $z in DD(0, R), r = abs(z)$, pour $r_0 in Ioo(r, R)$, $(a_n r_0^n)$ est bornée.
  $
    abs(n a_n z^n) = underbrace(abs(a_n r_0^n), "bornée") dot underbrace(n (r / r_0)^n, -> 0) \
    R_"cv" (sum n a_n z^n) >= R_"cv" (sum a_n z^n)
  $
  L'autre sens est évident :
  $
    R_"cv" (sum n a_n z^n) = R_"cv" (sum a_n z^n)
  $

- On applique le théorème $C^1$, qui donne la dérivée comme un série entière de même rayon de convergence (puis récurrence).

#card("regidse", "Rigidité des séries entières", ("Maths.Analyse.Séries entières",))

Rigidité des séries entières.

#answer

Soit $sum a_n z^n$ une série entière de rayon de convergence $R$.
$
  f : func(Ioo(-R, R), CC, x, sum_(n = 0)^(+oo) a_n x^n)
$
Pour tout $n in NN$
$
  a_n = (f^((n)) (0)) / n!
$
*Corolaire*

Si deux séries entières coincident sur un intervalle $Ico(0, delta)$ avec $delta > 0$, alors ce sont les mêmes.

*Démonstration*

- Pour tout $k in NN$ #h(1fr)
  $
    f^((k)) (x) = sum_(n = 0)^(+oo) (n + k)! / n! a_(n + k) x^n \
    f^((k)) (0) = k! a_k 
  $

- Soit 
  $
  g : func(Ioo(-R', R'), CC, x, sum_(n = 0)^(+oo) b_n x^n)
  $
  et $delta in Ioc(0, min(R, R'))$ tel que
  $
    forall x in Ico(0, delta), space f(x) = g(x)
  $
  Alors pour tout $k in NN$
  $
    f^((k)) = g^((k))
  $
  D'où (par continuité)
  $
    a_k = b_k
  $

#card("lemradabel", "Lemme radiale d'Abel", ("Maths.Analyse.Séries entières",))

Lemme radiale d'Abel.

#answer

Soit $sum a_n z^n$ une série entière de rayon de convergence $R > 0$.
$
  f : func(Ioo(-R, R), CC, x, sum_(n = 0)^(+oo) a_n x^n)
$
Si $sum a_n R^n$ converge alors $f$ CVU sur $[0, R]$. Ainsi
$
  lim_(x -> R) f(x) = sum_(n = 0)^(+oo) a_n R^n
$

*Démonstration*

- Cas $R = 1$ : #h(1fr)

  On a $sum a_n$ qui converge, et $x |-> sum a_n x^n$ CVS sur $[0, 1]$.

  $
  rho_n = sum_(k = n+1)^(+oo) a_k tends(n -> oo) 0 \
  $
  Soit $epsilon > 0$ et $N in NN$ tel que pour tout $n >= N$, $abs(rho_n) < epsilon$. Pour tout $x in Ico(0, 1)$
  $
  abs(R_n (x)) &= abs(sum_(k = n + 1)^(+oo) a_k x^k) \
  &= abs(rho_n x^(n+1) + sum_(k = n+1)^(+oo) rho_k (x^(k+1) - x^k) ) \
  &<= abs(rho_n) + sum_(k = n + 1)^(+oo) abs(rho_k) (x^k - x^(k+1)) \
  &< epsilon + epsilon sum_(k = n+1)^(+oo) (x^k - x^(k-1)) \
  &< epsilon + epsilon x^(n + 1) < 2 epsilon
  $
  Et
  $
    abs(R_n (1)) = abs(rho_n) < epsilon
  $
  D'où
  $
    sup_(x in [0, 1]) abs(R_n) < 2 epsilon
  $
  Donc CVN sur $[0, 1]$.

- Cas général :
  $
    b_n = a_n R^n quad quad R_"cv" (sum b_n x^n) = 1
  $
  Comme $sum b_n$ converge, le cas $R = 1$ s'applique et
  $
    sup_(x in [0, R]) abs(sum_(k = n + 1)^(+oo) a_n x^n) = sup_(t in [0, 1]) abs(sum_(k = n+1)^(+oo) underbrace(a_n R^n, b_n) x^n)
  $

// NOTE: M169 Fractions rationnelles (+ Exo)

#card("somosurlebord", "Sommation des petit o sur le bord", ("Maths.Analyse.Séries entières",))

Sommation des petit $o$ sur le bord (HP).

#answer

Pour
$
  f : func(Ioo(-1, -1), RR, x, sum_(n = 0)^(+oo) alpha_n x^n) \
  g : func(Ioo(-1, -1), RR, x, sum_(n = 0)^(+oo) a_n x^n) \
  forall n in NN, alpha_n >= 0 quad quad sum alpha_n "diverge" \
$
Alors
- Si $a_n = o_(n -> oo) (alpha_n)$ : #h(1fr)
  $
    g(x) = o_(x -> 1^-) (f(x))
  $
- Si $a_n eqv(n -> +oo) alpha_n$ : #h(1fr)
  $
    g(x) eqv(x -> 1^-) f(x)
  $

*Démonstration*

On montre que le cas du $o$ car il implique l'équivalent.

Soit $epsilon > 0$, on dispose de $N in NN$ tel que pour tout $n >= N$, 
$
  abs(a_n) <= epsilon alpha_n
$
Pour tout $x in Ico(0, 1)$
$
  abs(g(x)) &<= (sum_(n = 0)^(N - 1) abs(a_n)) + sum_(n = N)^(+oo) underbrace(abs(a_n), <= epsilon alpha_n) x^n \
  &<= C_N + epsilon f(x)
$
Comme $f(x) tends(x -> 1) +oo$, on dispose de $delta > 0$ tel que pour tout $x in Ioo(1 - delta, 1)$
$
  f(x) >= C_N / epsilon
$
Ainsi
$
  abs(g(x)) <= 2epsilon f(x) \
  g(x) = o_(x -> 1^-) (f(x))
$

#card("exabelcesaro", "Exercice : Lemme radiale d'Abel version Césaro", ("Maths.Exercice.Séries entières",))

Soit
$
  f : func(Ioo(-1, 1), RR, x, sum_(n = 0)^(+oo) a_n x^n) \
  forall k in NN, s_k = sum_(n = 0)^(k) a_k \
  forall N in NN, sigma_k = 1 / (N+1) sum_(k = 0)^(N) s_k
$
On suppose que $sigma_n tends(n -> oo) l$, montrer que $f(x) tends(x -> 1^-) l$

#answer

On pose
$
  g(x) &= sum_(n = 0)^(+oo) s_n x^n \
  &= sum_(n = 0)^(+oo) sum_(k = 0)^n a_k x^k x^(n - k) \
  &= f(x) / (1 - x)
$
Avec un rayon de convergence de $1$. Et
$
  h(x) &= sum_(n = 0)^(+oo) (n+1) sigma_n x^n \
  &= g(x) / (1 - x) = f(x) / (1 - x)^2
$
Or $sigma_n = l + o(1)$
$
  (n+1) sigma_n = (n+1) l + o(n + 1) \
  h(x) = sum_(n = 0)^(+oo) (n+1) l x^n + sum_(n = 0)^(+oo) c_n x^n
$
Avec $c_n = o(n + 1)$, or $sum_(n = 0)^(+oo) (n+1) x^n = 1 / (1 - x)^2$ et comme $sum (n+1)$ diverge, par sommation des petits $o$ sur le bord (à redémontrer)
$
  sum_(n = 0)^(+oo) c_n x^n = o_(x -> 1)( 1 /(1 - x)^2) \
$
$
  h(x) &= l / (1 - x)^2 + o (1 / (1 - x)^2) \
  &= f(x) / (1 - x)^2
$
Donc
$
  f(x) = l + o(1)
$

#card("premformcauch", "Première formule de Cauchy", ("Maths.Analyse.Séries entières",))

Première formule de Cauchy (HP).

#answer

Soit ($R in RR^*_+ union {+oo}$)
$
  f : func(DD(0, R), CC, z, sum_(n = 0)^(+oo) a_n z^n)
$
On a
$
  1 / (2 pi) integral_0^(2pi) f(r e^(i n theta)) dif theta = a_n r^n bb(1)_(n >= 0)
$

*Démonstration*

Montrons la CVN de la série
$
  sup_(theta i [0, 2pi]) abs(a_n r^n e^(i n theta)) = abs(a_n) r^n
$
Qui est le terme général d'une série convergente ($r < R$). Et
$
  integral_0^(2pi) abs(a_n r^n e^(i n theta)) dif theta = 2pi abs(a_n) r^n
$
Qui est aussi le terme général d'une série convergente.

Par le théorème d'intégration terme à terme (verifier les hypothèses) :

$
  space& 1 / (2pi) integral_0^(2pi) f(r e^(i n theta)) e^(- i n theta) dif theta \
  =& 1 / (2pi) integral_0^(2pi) sum_(k = 0)^(+oo) a_k r^k e^(i k theta) e^(- i n theta) dif theta \
  =& 1 / (2pi) sum_(k = 0)^(+oo) a_k r^k underbrace(integral_0^(2pi) e^(i(k - n) theta) dif theta, 2 pi delta_(k,n)) \
  =& a_n r^n bb(1)_(n >= 0)
$

#card("formparce", "Formule de Parseval", ("Maths.Analyse.Séries entières",))

Formule de Parseval.

#answer

Soit ($R in RR^*_+ union {+oo}$)
$
  f : func(DD(0, R), CC, z, sum_(n = 0)^(+oo) a_n z^n)
$
Pour tout $r in Ioo(0, R)$ on a
$
  1 / (2pi) integral_0^(2pi) abs(f(r e^(i theta)))^2 dif theta = sum_(n = 0)^(+oo) abs(a_n)^2 r^(2n)
$

*Démonstration*

Pour tout $r < R$ et $theta in RR$
$
  abs(f(r e^(i theta)))^2 &= f(r e^(i theta)) overline(f(r e^(i theta))) \
$
$
  &= (sum_(k = 0)^(+oo) a_k r^k e^(i k theta)) (sum_(k = 0)^(+oo) overline(a_k) r^k e^(- i k theta)) \
  &= sum_(k, n in NN) a_k overline(a_n) r^(k +n) e^(i (k - n) theta)
$
Puis on applique le théorème d'intégration terme à terme (par bijection de $NN^2$ dans $NN$)
$
  & 1 / (2 pi) integral_0^(2pi) abs(a_k overline(a_n) r^(k + n) e^(i (k - n) theta)) dif theta  \
  =& abs(a_k) abs(a_n) r^(k + n)
$
Et 
$
sum_(k, n in NN) abs(a_k) abs(a_n) r^(k + n) &= (sum_(k = 0)^(+oo) abs(a_k) r^k)^2 \  &< +oo
$
D'où
$
& 1 / (2pi) integral_0^(2pi) abs(f(r e^(i theta)))^2 dif theta \ 
=& sum_(k,n in NN) a_k overline(a_n) r^(k + n) 1 / (2pi) underbrace(integral_0^(2pi) e^(i (k - n) theta) dif theta, delta_(k,n)) \
=& sum_(n = 0)^(+oo) abs(a_n)^2 r^(2n)
$

#card("princmax", "Principe du maximum", ("Maths.Analyse.Séries entières",))

Principe du maximum.

#answer

Soit ($R in RR^*_+ union {+oo}$)
$
  f : func(DD(0, R), CC, z, sum_(n = 0)^(+oo) a_n z^n)
$

+ Si $abs(f)$ admet un maximum local en $0$, alors $f$ est constante sur $DD(0, R)$.

+ Si $abs(f)$ admet un maximum local en $z_0 in DD(0, R)$, alors $f$ est constante sur $DD(0, R)$.

+ Si $f$ est prolongeable par continuité sur $overline(DD(0, R))$, alors #h(1fr)
  $
    max_DD(0, R) abs(f) = max_(SS(0, R)) abs(f)
  $

*Démonstration*

+ On suppose (pour un $epsilon in Ioo(0, R)$) #h(1fr)
  $
  abs(a_0) = abs(f(0)) = max_(overline(DD(0, epsilon))) abs(f)
  $
  Pour tout $r in Ioc(0, epsilon)$
  $
    abs(a^0)^2 &= abs(f(0))^2  \ 
    &>= 1/(2pi) integral_0^(2pi) abs(f(r e^(i theta)))^2 dif theta \
    &= sum_(n = 0)^(+oo) abs(a_n)^2 r^(2n) >= abs(a_0)^2
  $
  Donc $forall n in NN^*, a_n = 0$, et $f$ est constante.

+ On suppose que $abs(f)$ admet un maximum local en $z_0 in DD(0, R)$.

  On redemontre que $f$ est DSE en $z_0$ :

  Pour tout $h in DD(0, delta)$ ou $delta = R - abs(z_0)$
  $
    f(z_0 + h) = sum_(n = 0)^(+oo) b_n h^n
  $
  Où $(b_n) in CC^n$, et $h |-> f(z_0 + h)$ vérifie 1. donc est constante sur $DD(0, delta)$, et tout point de $overline(DD(0, delta))$ est un maximum local. On peut dont repéter ce raisonnement pour atteindre $0$ puis appliquer 1.

  #align(center, cetz.canvas(length: 4em, {
    import cetz.draw: *

    let r = 0.8
    let i = 0
    let a = 45deg

    circle((0, 0), radius: 1, stroke: _colors.text)

    while r >= 0.25 {
      circle((angle: a, radius: r), radius: 0.02, fill: _colors.text)
      content((), anchor: "north-west", $z_#i$)
      circle((angle: a, radius: r), radius: 1.0 - r, stroke: red)
      
      r = (3 * r - 1) / 2
      r = calc.floor(r * 1024) / 1024.0
      i = i + 1
    }

    circle((0, 0), radius: 0.02, fill: _colors.text)
    content((), anchor: "north-west", $O$)

  }))

+ Par disjonction de cas :
  - Si le $max_(overline(DD(0, R))) abs(f)$ est atteint dans $DD(0, R)$, alors par 2., $f$ est constante, donc il est aussi atteint sur $SS(0, R)$
  - Sinon il ne peut être atteint que sur $SS(0, R)$.

#card("deuxformca", "Deuxième formule de Cauchy", ("Maths.Analyse.Séries entières",))

Deuxième formule de Cauchy.

#answer

Soit $f in C^0(DD(0, R), CC)$, $r < R$, $z in DD(0, r)$.
$
  g(z) = 1/(2pi) integral_0^(2pi) (f(r e^(i theta))) / (r e ^(i theta) - z) r e^(i theta) dif theta
$

Alors $g : DD(0, r) -> CC$ est DSE et si $f$ est DSE sur $DD(0, R)$, alors $g(z) = f(z)$ sur $DD(0, r)$.

On en déduit que si pour $n in NN$ on a
$
  f_n : func(DD(0, R), CC, z, sum_(k = 0)^(+oo) a_(n,k) x^k)
$
Et $r < R$, $(f_n)$ CVU sur $overline(DD(0, R))$ vers $f$, alors $f$ est DSE sur $DD(0, r)$.

*Démonstration*

Soit $z in DD(0, r)$, comme $abs(z) / abs(r e^(i theta)) < 1$
$
  r e^(i theta) / (r e^(i theta) - z) = 1 / (1 - z / (r e^(i theta))) = sum_(n = 0)^(+oo) z^n / r^n e^(-i n theta)
$
On pose $f_n : theta |-> z^n / r^n e^(-i n theta) f(r e^(i theta))$
$
theta |-> sum_(n = 0)^(+oo) f_n (theta) = f(r e^(i theta)) / (r e^(i theta) - z) r e^(i theta)
$
Qui est continue sur $[0, 2pi]$
$
  integral_0^(2pi) abs(f_n (theta)) dif theta <= 2 pi norm(f)_(oo, overline(DD(0, R))) dot abs(z / r)^n 
$
Qui est le terme général d'une série convergente, donc par intégration terme à terme :
$
g(z) = sum_(n = 0)^(+oo) ( 1 / (2pi r^n) integral_0^(2pi) f(r e^(i theta)) e^(- i n theta) dif theta) z^n
$
Et $g$ est bien DSE sur $DD(0, r)$

On suppose de plus que
$
  f : func(DD(0, R), CC, z, sum_(n = 0)^(+oo) a_n z^n)
$
Alors par la première formule de cauchy, $f(z) = g(z)$ pour $z in DD(0, r)$.

Ainsi pour
$
  f_n : func(DD(0, R), CC, z, sum_(k = 0)^(+oo) a_(n,k) x^k)
$
avec $r < R$ et $(f_n)$ CVU vers $f$ sur $overline(DD(0, R))$, on a pour tout $n in NN, z in DD(0, r)$
$
  f_n (z) = 1 / (2pi) integral_0^(2pi) (f_n (r e^(i theta))) / (r e^(i theta) - z) r e^(i theta) dif theta
$
Donc par CVU sur $[0, 2pi]$ quand $n$ tends vers $+oo$
$
 f(z) = 1 / (2pi) integral_0^(2pi) (f(r e^(i theta)) / (r e^(i theta) - z)) r e^(i theta) dif theta
$
Et par 1. $f$ est DSE.

#card("exprodcauch", "Exercice : Produit de cauchy par les séries entières", ("Maths.Exercice.Séries entières",))

Soient $(a_n)_n, (b_n)_n in CC^NN$ et
$
  forall n in NN, c_n = sum_(k = 0)^n a_n b_(n - k)
$
On suppose que $sum a_n$, $sum b_n$ et $sum c_n$ convergent, montrer que
$
  sum_(n = 0)^(+oo) c_n = (sum_(n = 0)^(+oo) a_n)(sum_(n = 0)^(+oo) b_n)
$

#answer

Par hypothèse, pour $u in {a, b, c}$ :
$
  R_u = R_"cv" (sum u_n z^n) >= 1 \
  f_u : func(DD(0, 1), CC, z, sum_(n = 0)^(+oo) u_n z^n)
$
Et par produit de Cauchy :
$
  forall z in DD(0,1), quad f_c (z) = f_a (z) f_b (z)
$
Or par le lemme radiale d'Abel, pour $u in {a, b, c}$
$
  sum_(n = 0)^(+oo) u_n = lim_(z -> 1^-) f_u (z)
$
Ainsi
$
  sum_(n = 0)^(+oo) c_n &= lim_(z -> 1^-) f_c (z) \
  &= lim_(z -> 1^-) f_a (z) f_b (z) \
  &= (sum_(n = 0)^(+oo) a_n) (sum_(n = 0)^(+oo) b_n) \
$

#card("exsederang", "Exercice : nombre de dérangements par les séries entières", ("Maths.Exercice.Séries entières",))

On pose 
$
  D_n = Set(sigma in frak(S)_n, "Fix" (sigma) = emptyset) \
  d_n = abs(D_n)
$
Donner une formule pour $d_n$ en utilisant les séries entières.

#answer

On cherche une relation sur $d_k$ :

+ On peut écrire #h(1fr)
  $
    frak(S)_n = union.big.plus_(k = 0)^(n) union.big.plus_(A subset.eq [|1, n|] \ abs(A) = k) Set(sigma in frak(S)_n, "Fix" (sigma) = A) \
    n! = sum_(k = 0)^n vec(n, k) d_(n - k) = sum_(k = 0)^n vec(n, k) d_k \
    1 = sum_(k = 0)^n 1 / (n - k)! dot d_k / k!
  $
  Ainsi en posant
  $
    f : func(Ioo(-1, 1), RR, x, sum_(n = 0)^(+oo) d_n / n! x^n)
  $
  On trouve, pour $x in Ioo(-1, 1)$
  $
    1 / (1 - x) &= sum_(n = 0)^(+oo) 1 dot x^n \
    &= sum_(n = 0)^(+oo) (sum_(k = 0)^n 1 / (n - k)! d_k / k!) x^n \
    &= (sum_(n = 0)^(+oo) x^n / n!) (sum_(n = 0)^(+oo) d_n / n! x^n) \
    &= f(x) e^x
  $
  Ainsi
  $
    f(x) &= e^(-x) / (1 - x) \ 
    &= (sum_(n = 0)^(+oo) (-1)^n / n! x^n) (sum_(n = 0)^(+oo) x^n) \
    d_n / n! &= sum_(k = 0)^(n) (-1)^k / k!
    
  $

+ On construit une bijection 
  $
  theta : D_(n+1) -> [|1, n|] times (d_(n-1) union.plus d_n)
  $

  Soit $sigma in D_(n+1)$, on pose $k = sigma(n+1)$.

  - Si $sigma(k) = n+1$ : on pose #h(1fr)
    $
      tilde(sigma) = sigma|_([|1, n|]\\{k}) in D_(n-1)
    $
  - Sinon, $j = sigma^(-1) (n+1)$ : on pose
    $
      tilde(sigma) = func([|1, n|], [|1,n|], i != j, sigma(i), j, k) in D_n
    $
  Ainsi
  $
    theta(sigma) = (k, tilde(sigma))
  $

  On montre que c'est une bijection (l'écrire).

  Ainsi
  $
  d_(n+1) = n (d_n + d_(n-1))
  $

  On en déduit
  $
    (1 - x)f'(x) = x f(x) 
  $
  D'où
  $
    f(x) = e^(-x) / (1 - x)
  $
  Et on conclut de même.

#card("excatalan", "Exercice : nombres de Catalan avec les séries entières", ("Maths.Exercice.Séries entières",))

On définit le $n$-ème nombre de Catalan
$
  C_0 = 1, forall n in NN^*, C_n = sum_(k = 0)^(n - 1) C_k C_(n - k) \
  f : func(Ioo(-R, R), RR, x, sum_(n = 0)^(+oo) C_n x^n)
$
Donner une forme explicite de $f$ et son rayon de convergence, en déduire une expression de $C_n$.

#answer

*Analyse*

On suppose que $R > 0$, pour tout $x in Ioo(-R, R)$
$
  f(x) &= 1 + x sum_(n = 0)^(+oo) C_(n+1)x^n \
  &= 1 + x sum_(n = 0)^(+oo) (sum_(k = 0)^n C_n C_(n - k)) x^n \
  &= 1 + x f(x)^2
$
D'où pour $x in Ioo(-1/4, 1/4)$
$
  f(x) = (1 - sqrt(1 - 4x)) / (2 x)
$

*Synthèse*

On considère
$
  f : x |-> (1 - sqrt(1 - 4x)) / (2 x)
$
On sait que $x |-> sqrt(1 - 4x)$ est DSE sur $Ioo(-1/4, 1/4)$ :
$
  sqrt(1 - 4x) = 1 + sum_(n = 1)^(+oo) b_n x^n
$
D'où
$
f(x) = - sum_(n = 1)^(+oo) b_n / 2 x^(n-1) = sum_(n = 0)^(+oo) c_n x^n
$
Or $x f(x)^2 - f(x) + 1 = 0$, donc par unicité du DSE
$
  c_n = sum_(k = 0)^(n-1) c_k c_(n - k) \
  c_0 = 1
$
Donc $c_n = C_n$ et $R = 1/4$.

On peut ensuite calculer $c_n$ à partire du DSE de $sqrt(1 + x)$.

#card("compdse", "Composée du développement en série entière", ("Maths.Analyse.Séries entières",))

Composée du développement en série entière.

#answer

Soient
$
  f : func(DD(0, R), CC, z, sum_(n = 0)^(+oo) a_n z^n) \
  g : func(DD(0, R'), CC, z, sum_(n = 0)^(+oo) b_n z^n) \
  g(0) = 0
$
Alors $f compose g$ est DSE en $0$ pour un rayon de convergence $r > 0$.

*Démonstration*

Pour tout $z in DD(0, R)$, $sum abs(b_n z^n)$ converge et
$
  g_0 : func(Ico(0, R'), RR, x, sum_(n = 0)^(+oo) abs(b_n) x^n)
$
Est continue et $g_0 (0) = 0$. 

Donc on dispose de $r > 0$ tel que $g_0 ([0, r]) subset.eq Ico(0,R)$.

Ainsi pour tout $z in DD(0, r)$, $g(z) in DD(0, R)$ et
$
  f(g(z)) = sum_(n = 0)^(+oo) a_n (sum_(k = 0)^(+oo) b_k z^k)^n
$
Par produit de Cauchy
$
  (sum_(k = 0)^(+oo) b_k z^k)^n = sum_(k = 0)^(+oo) c_(k,n) z^k \
  c_(k,n) = sum_(i_1, dots, i_n \ sum_(j = 1)^n i_j = k) product_(j = 1)^n b_i_j
$
Or
$
  abs(c_(k,n)) <= sum_(i_1, dots, i_n \ sum_(j = 1)^n i_j = k) product_(j = 1)^n abs(b_i_j)
$
Donc
$
  sum_(k = 0)^(+oo) abs(c_(k,n)) dot abs(z^k) <= (underbrace(sum_(k = 0)^(+oo) abs(b_k) dot abs(z^k), alpha in Ico(0, R)))^n
$
Et donc pour tout $z in DD(0, r)$
$
  & sum_(n = 0)^(+oo) sum_(k = 0)^(+oo) abs(a_n c_(k,n)) dot abs(z^k) \
  =& sum_(n = 0)^(+oo) abs(a_n) (sum_(k = 0)^(+oo) abs(c_(k,n)) dot abs(z^k)) \
  =& sum_(n = 0)^(+oo) abs(a_n) alpha^n
$
Qui converge, et donc par Fubini
$
  f(g(z)) &= sum_(n = 0)^(+oo) a_n sum(k = 0)^(+oo) c_(k,n) z^k \
  &= sum_(k = 0)^(+oo) (sum_(n = 0)^(+oo) a_n c_(k,n)) z^k
$
Donc $f compose g$ est bien DSE.

#card("fekete", "Suites sous-additive et lemme de Fekète", ("Maths.Analyse.Suites Réelles",))

Soit $(a_n)_n in RR^NN$ sous-additive :
$
  forall n, m in NN, a_(n + m) <= a_n + a_m
$
Montrer que 
$
lim_(n -> oo) a_n / n &= inf {a_k / k, k in NN^*} \ &= alpha in RR union {-oo}
$

#answer

Soit $epsilon > 0$, on pose
$
  A = cases(space 0 "si" alpha = -oo, space alpha + epsilon "sinon")
$
Par caractérisation de la borne inférieur, on dispose de $q in NN^*$ tel que
$
  a_q / q < A - epsilon / 2
$
Pour $n >= q$ on fait la division euclidienne de $n$ par $q$ : 
$
n = k_n q + r_n
$
Et ainsi
$
  a_n <= a_(k_n q) + a_r_n <= k_n a_q + a_r_n \
$
$
  a_n / n &<= k_n / n a_q +  a_r_n / n \
  &= a_q / q + underbrace((-(r_n a_q) / q + a_r_n), "bornée par" M "car" r_n in [|0, q-1|]) 1 / n
$
Donc pour $n >= N$ avec $N$ assez grand
$
  M / n <= epsilon / 2 \
  alpha <= a_n / n <= A - epsilon / 2 + epsilon / 2 = A
$

#card("exinttnpol", "Exercice : integrale nulle sur un ségment du produit d'une fonction continue avec une puissance", ("Maths.Exercice.Intégration",))

Deux exercices à ne pas confondre :

Soit $f in C^0 ([a, b], RR)$

+ Pour tout $n in NN$ #h(1fr)
  $
    integral_a^b f(t) t^n dif t = 0
  $
  Montrer que $f = 0$

+ Pour tout $n in [|0, d|]$
  $
    integral_a^b f(t) t^n dif t = 0
  $
  Montrer que $f$ s'annule en $d+1$ points.

#answer

Par linéarité de l'intégrale on a

+ Pour tout $P in RR[X]$ #h(1fr)
  $
    integral_a^b f(t) P(t) dif t = 0
  $

  On dispose de $(P_n)_n in RR[X]^NN$ tel que
  $
    norm(f - P_n)_(oo,[a,b]) tends(n -> oo) 0
  $
  Or pour tout $t in [a, b]$
  $
    &abs(f^2(t) - P_n (t) f(t)) \ =& abs(f(t)) abs(P_n(t) - f(t)) \
    <=& norm(f)_oo norm(f - P_n)_oo
  $
  D'où
  $
    norm(f^2 - P_n f)_oo tends(n -> oo) 0
  $
  Et par CVU sur $[a, b]$
  $
    integral_a^b f^2(t) dif t = lim_(n -> oo) integral_a^b P_n (t) dif t = 0
  $
  Donc $f^2 = 0 = f$.

+ Pour tout $P in RR_d [X]$
  $
    integral_a^b f(t) P(t) dif t = 0
  $

  Par l'aburde supposons que
  $
    abs(f^(-1) {0}) <= d
  $
  Soient $a_1 < dots.c < a_q$ les points où $f$ s'annule en changeant de signe ($0 <= q <= d$).
  $
    P(X) = product_(j = 1)^q (X - a_j) in RR_d [X]
  $
  Et $t |-> f(t)P(t)$ s'annule en au plus $d$ points et ne change pas de signe. Or
  $
    integral_a^b f(t) P(t) dif t = 0
  $
  Donc $f P = 0$ et $f$ est presque nulle, absurde.

#card("ex63dse", "Exercice : CNS de DSE en bornant les dérivées successives", ("Maths.Exercice.Séries entières",))

Soit $f in C^oo (Ioo(-delta, delta), RR)$, montrer que $f$ est DSE en $0$ ssi
$
  exists a, M in RR^*_+, V in cal(V)(0), \ forall x in V, n in NN, \
  abs(f^(n) (x)) <= M a^n n!
$

#answer

*Sens indirecte*

On dispose de $a, M$ et $V$ comme énoncé, pour tout $x in V$ on a
$
  & abs(f(x) - sum_(k = 0)^n f^((k)) (0) / k! x^k) \ <=& sup_V abs(f^((n+1))) dot abs(x^(n+1)) / (n+1)! \ 
  <=& M abs(a x)^(n+1)
$
Soit $eta > 0$ tel que $a eta < 1$ et $Ioo(-eta, eta) subset.eq V$.

Pour tout $x in Ioo(-eta, eta)$
$
  abs(f(x) - sum_(k = 0)^n f^((k)) (0) / k! x^k) &<= M abs(a eta)^n+1 \
  &tends(n -> oo) 0
$
D'où
$
  f(x) = sum_(k = 0)^(+oo) f^((k)) (0) / k! x^k
$
Avec convergence de la série.

*Sens directe*

On suppose que pour tout $x in Ioo(-eta, eta)$
$
  f(x) = sum_(k = 0)^(+oo) b_k x^k \
  f^((n)) (x) = sum_(k = n)^(+oo) b_k k! / (k - n)! x^(k - n)
$

Or la suite $(b_k (eta / 2)^k)_(k in NN)$ est bornée par $M$.

Ainsi pour tout $k in NN$, $abs(b_k) <= M (2 / eta)^k$.
$
  abs(f^((k))(x)) &<= M sum_(k = n)^(+oo) k! (k - n)! (2 / eta)^k abs(x)^(k - n) \
  &<= M (2 / eta)^n sum_(k = n)^(+oo) k! / (k - n)! abs((2 x) / eta)^(k - n)
$
Or pour $y in Ioo(-1, 1)$
$
  sum_(k = n)^(+oo) k! (k - n)! y^(k - n) = g^((n))(y) \
  g(y) = 1 / (1 - y) \
  g^((n)) (y) = n! / (1 - y)^(n + 1)
$
D'où pour tout $n in NN$, $x in Ioo(-eta / 2, eta/2)$
$
  abs(f^((n))(x)) <= M (2 / eta)^n n! / (1 - (2 abs(x)) / eta)^(n+1)
$
Ainsi pour tout $x in Ioo(-eta / 4, eta / 4)$
$ 
  (2 abs(x)) / eta < 1/2
$
Donc pour tout $n in NN$
$
  abs(f^((n))(x)) <= (2 M) n! (4 / eta)^n
$
