#import "/cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
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
