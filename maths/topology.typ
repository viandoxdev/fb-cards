#import "/cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

#card("norm", "Norme", ("Maths.Topologie",))

Définition d'une norme sur un $KK$-ev $E$.

#answer

Une norme sur un $KK$-ev $E$ est une application $N : E -> RR_+$ tel que

+ Homogénéité : $forall lambda in KK, x in E$ #h(1fr)
  $
    N(lambda x) = abs(lambda) N(x)
  $

+ Inégalité triangulaire : $forall x, y in E$
  $
    N(x + y) <= N(x) + N(y)
  $

+ Séparation : $forall x in E$
  $
    N(x) = 0 => x = 0
  $

#card("normeeuclidienne", "Norme euclidienne", ("Maths.Topologie",))

Définition et propriétés des normes euclidiennes.

#answer

Pour $E$ un $RR$-ev un produit scalaire est une forme bilinéaire symétrique définie positive.

Pour un produit scalaire $scl(dot, dot)$ on a l'Inégalité de Cauchy-Schwartz :
$
  forall x, y in E \
  scl(x, y)^2 <= scl(x, x) dot scl(y, y)
$
Avec cas d'égalité si $(x, y)$ liée.

D'un produit scalaire dérive une norme (euclidienne)
$
  norm(dot) : func(E, RR_+, x, sqrt(scl(x, x)))
$

*Démonstration*

- Si $x = 0$ ou $y = 0$ : évident. Sinon pour $x, y in E\\{0}, t in RR$ : #h(1fr)
  $
    scl(x + t y, x + t y) \ = t^2 scl(y, y) + 2 t scl(x, y) + scl(x, x) \ = P(t)
  $
  Comme $scl(y, y) > 0$, $deg P = 2$. De plus par positivité de $scl(dot, dot)$ :
  $
    Delta = 4scl(x, y)^2 - 4 scl(x, x) dot scl(y, y) &<= 0 \
    scl(x, y)^2 <= scl(x, x) dot scl(y, y)
  $
  Avec cas d'égalité si $Delta = 0$, c'est à dire $x + t y = 0$.

- Vérifions les axiomes

  + Soit $lambda in RR, x in E$ #h(1fr)
    $
      norm(lambda x) &= sqrt(scl(lambda x, lambda x)) \
      &= abs(lambda) sqrt(scl(x, x))  \
      &= abs(lambda) norm(x)
    $

  + Soit $x in E$ tel que $norm(x) = 0$
    $
      sqrt(scl(x, x)) &= 0 \
      scl(x, x) &= 0 \
      x &= 0
    $

  + Soit $x, y in E$ \
    $
      & space norm(x + y)^2 \
      &= scl(x + y, x + y) \
      &= norm(x)^2 + norm(y)^2 + 2 scl(x, y) \
      &<= norm(x)^2 + norm(y)^2 + 2 underbrace(abs(scl(x, y)), "C-S") \
      &<= norm(x)^2 + norm(y)^2 + 2 norm(x) norm(y) \
      &= (norm(x) + norm(y))^2
    $

  Avec égalité ssi $scl(x, y) >= 0$ et égalité dans C-S : ssi $x, y$ positivement liés.

#card("normprod", "Norme produit", ("Maths.Topologie",))

Définition de la norme produit.

#answer

Soit $(E_1, norm(dot)_1), dots, (E_d, norm(dot)_d)$ des $KK$-evn.

On définit la norme produit sur $product_(k = 1)^d E_k$ comme
$
  N : func(display(product_(k = 1)^d E_k), RR_+, vec(x_1, dots, x_n), display(max_(k in [|1, n|]) norm(x_k)_k))
$

#card("dist", "Distance", ("Maths.Topologie",))

Définition de distance.

#answer

Soit $X$ un ensemble non vide. On appelle distance une application $d : X^2 -> RR_+$ tel que

+ Symétrie : $forall x, y in X$ #h(1fr)
  $
    d(x, y) = d(y, x)
  $

+ Inégalité triangulaire : $forall x, y, z in X$
  $
    d(x, z) <= d(x, y) + d(y, z)
  $

+ Séparation : $forall x, y in X$
  $
    d(x, y) = 0 => x = y
  $

Dans un evn $(E, norm(dot))$ on peut définir la distance sur $E$ associé à la norme $norm(dot)$ :
$
  d : func(E^2, RR_+, (x, y), norm(x - y))
$

#card("bouleetbil", "Boules et sphères", ("Maths.Topologie",))

Définition, propriétés des boules et sphères.

#answer

Soit $E$ un espace métrique, $a in E$ et $r in RR_+$. On définit les ensembles suivants
$
  B(a, r) &= {x in E | d(a, x) < r} \
  B_f (a, r) &= {x in E | d(a, x) <= r} \
  SS(a, r) &= {x in E | d(a, x) = r} \
$

Si $E$ est un $KK$-evn alors on a de plus la convexité de $B(a, r)$ et $B_f (a, r)$.

#card("ptsextremaux", "Points extrémaux d'un convexe", ("Maths.Topologie",))

Définition des points extrémaux d'un convexe et points extrémaux d'une boule.

#answer

Soit $(E, norm(dot))$ un evn, $K subset.eq E$ convexe. On dit que $x in K$ est extrémal si
$
  forall y, z in K, forall t in Ioo(0,1), \ x = (1 - t) y + t z => x = y = z
$

Si $norm(dot)$ dérive d'un produit scalaire, alors pour tout $a in E$ et $r in RR_+$, l'ensemble des points extrémaux de $B_f (a, r)$ est $SS(a, r)$.

*Démonstration*

Pour $r = 1$ et $a = 0$ : (auxquels on peut se ramener)

- Soit $x in B(0, 1)$ #h(1fr)
  $
    x = (1 - norm(x)) 0 + norm(x) x / norm(x)
  $
  D'où $x$ pas extrémal (on traite le cas $x = 0$ séparément).

- Soit $x in SS(0, 1)$, $y, z in B_f (0, 1), t in Ioo(0, 1)$ tel que
  $
    x = (1 - t) y + t z \
    norm(x) = 1 <= (1 - t) underbrace(norm(y), <= 1) + t underbrace(norm(z), <= 1)
  $
  On a égalité dans l'inégalité triangulaire : $y$ et $z$ positivement liés (car produit scalaire) et $norm(y) = norm(z)$ d'où $y = z = x$.

#card("topologies", "Topologie, espace topologique", ("Maths.Topologie",))

Définition d'une topologie.

#answer

Soit $X$ un ensemble, $T subset.eq cal(P)(X)$ est une topologie sur $X$ si

+ ${emptyset, X} subset.eq T$

+ Pour toute famille $(Omega_i)_i in T^I$
  $
    union.big_(i in I) Omega_I in T
  $

+ Pour tout $Omega_1, dots, Omega_n in T$
  $
    inter.big_(k = 1)^n Omega_k in T
  $

Les éléments de $T$ sont appelés ouverts de $X$.

$X$ muni de $T$ est appelé espace topologique.

#card("topem", "Topologie sur un espace métrique", ("Maths.Topologie",))

Définitions des ouverts / fermés d'un espace métrique.

#answer

Soit $(E, d)$ un espace métrique.

On dit que $Omega subset.eq E$ est un ouvert de $E$ si
$
  forall x in Omega, exists delta > 0, B(x, r) subset.eq Omega
$
De manière équivalente
$
  forall x in Omega, Omega in cal(V)(x)
$
L'ensemble $T$ des ouverts de $E$ forme une topologie :

+ $emptyset$ et $E$ sont ouverts.

+ $T$ est stable par union quelconque.

+ $T$ est stable par intersection finie.

On définit de plus les fermés : le complémentaire d'un ouvert.

*Démonstration*

+ Évident.

+ Soit $(Omega_i)_i in T^I$ une famille d'ouverts. Soit $x in W = union.big_(i in I) Omega_i$.

  On dispose de $i in I$ tel que $x in Omega_i$, ainsi on dispose de plus de $delta > 0$ tel que
  $
    B(x, delta) subset.eq Omega_i subset.eq W
  $

  Donc $W in T$ : c'est un ouvert.

+ Soit $F_1, dots, F_n in T$, soit $x in W = inter.big_(k = 1)^n F_k$. Pour tout $k in [|1, n|]$ on dispose de $delta_k > 0$ tel que
  $
    B(x, delta_k) subset.eq F_k \
    delta = min_(k in [|1; n|]) delta_k \
  $
  Ainsi on a pour tout $k in [|1,n|]$ :
  $
    B(x, delta) subset.eq B(x, delta_k) subset.eq F_k \
  $
  Donc
  $
    B(x, delta) subset.eq W
  $

#card("limsuit", "Limites de suites", ("Maths.Topologie",))

Définitions équivalentes de limites d'une suite.

#answer

Soit $(E, d)$ un espace métrique, $u = (u_n)_n in E^NN$. On dit que $l in E$ est limite de la suite $u$ si l'une des définitions suivantes équivalentes s'applique :

+ $forall epsilon > 0, exists N in NN, forall n >= N, d(u_n, l) < epsilon$.

+ $forall epsilon > 0, exists N in NN, forall n >= N, u_n in B(l, epsilon)$.

+ $(d(u_n, l))_n tends(n -> oo) 0$.

+ $forall V in cal(V)(l), exists N in NN, forall n >= N, u_n in V$.

Si la limite existe, alors elle est unique.

*Démonstration*

- Équivalence : l'écrire.

- Si $l = lim_(n -> oo) u_n$, prendre $l' != l$ et montrer que $(d(l', u_n))_n tendsnot(n->oo) 0$.

#card("vadh", "Valeurs d'adhérance d'une suite", ("Maths.Topologie",))

Définitions et propriétés sur les valeurs d'adhérance d'une suite.

#answer

Soit $(E, d)$ un espace métrique, $u = (u_n)_n in E^NN$ une suite.

On dit que $l in E$ est une valeur d'adhérance de $u$ s'il existe $phi$ extractrice tel que $(u_(phi(n)))_n tends(n -> oo) l$.

Une suite qui à deux valeurs d'adhérance diverge.

#card("compnorm", "Comparaison de normes", ("Maths.Topologie",))

Définitions de comparaison de normes, propriétés.

#answer

Soit $E$ un $KK$-ev, $norm(dot)_1$ et $norm(dot)_2$ deux normes sur $E$.

On dit que $norm(dot)_2$ est plus fine de $norm(dot)_1$ s'il existe $alpha > 0$ tel que
$
  forall x in E, space norm(x)_1 <= alpha norm(x)_2
$

Dans ce cas :

+ Pour tout $a in E$ et $r > 0$ #h(1fr)
  $
    B_2 (a, r) subset.eq B_1 (a, alpha r)
  $

+ Si $Omega subset.eq E$ est ouvert pour $norm(dot)_1$ est ouvert pour $norm(dot)_2$

+ Toute suite bornée pour $norm(dot)_1$ l'est pour $norm(dot)_2$.

+ Toute suite convergente pour $norm(dot)_1$ l'est pour $norm(dot)_2$.

On dit que $norm(dot)_1$ et $norm(dot)_2$ sont équivalentes si chacune est plus fine que l'autre. C'est une relation d'équivalence.

#card("adh", "Adhérance", ("Maths.Topologie",))

Définition de l'adhérance, caractérisation séquentielle.

#answer

Soit $(E, d)$ un espace métrique, $A subset.eq E$ une partie. Un point $x in A$ est dit adhérant à $A$ s'il vérifit une des conditions équivalentes suivantes :

+ $forall r > 0, B(x, r) inter A != emptyset$

+ $exists (u_n)_n in A^NN, lim_(n -> oo) u_n = x$

+ $d(x, A) = 0$

On définit alors l'adhérance d'un ensemble (noté $overline(A)$) comme l'ensemble de ses points d'adhérance.

- $A subset.eq overline(A)$.

- $A$ est fermée ssi $A = overline(A)$.

- $overline(A)$ est le plus petit (au sens de l'inclusion) fermé contenant $A$ :
  $
    overline(A) = inter.big_(A subset.eq B subset.eq E \ B "fermé") B
  $

- $overline(E \\ A) = E \\ circle(A)$

*Démonstration*

- (1 $=>$ 2) Pour tout $n in NN$, on pose $x_n$ tel que $x_n in B(x, 1/(n+1))$, qui existe par hypothèse.

  Ainsi $d(x_n, x) < 1/(n+1)$ d'où $(d(x_n, x))_n -> 0$ donc $(x_n)_n -> x$.

- (2 $=>$ 1) Par hypothèse on dispose de $(x_n)_n in A^NN -> x$. Soit $r > 0$.

  On dispose de $N in NN$ tel que $d(x_N, x) < r$, donc
  $
    x_N in B(x, r) inter A != emptyset
  $

- (2 $<=>$ 3) 
  $
    x in overline(A) &<=> exists (a_n)_n in A^NN, space a_n -> x \
    &<=> exists (a_n)_n in A^NN, space d(x, a_n) -> 0 \
    &<=> d(x, A) <= 0 \
    &<=> d(x, A) = 0
  $

- Supposons que $F != overline(F)$, on dispose donc de $x in overline(F) \\ F$.

  Soit $epsilon > 0$, comme $x in overline(F)$
  $
    B(x, epsilon) inter F != emptyset \
    B(x, epsilon) subset.eq.not E \\ F
  $
  Donc $E \\ F$ n'est pas un ouvert : $F$ n'est pas fermée.

- Supposons que $F$ n'est pas fermée, on dispose donc de $x in E \\ F$ tel que
  $
    forall epsilon > 0, B(x, epsilon) subset.eq.not E \\ F
  $
  Donc pour tout $epsilon > 0$
  $
    B(x, epsilon) inter F != emptyset
  $
  D'où $x in overline(F)$, mais $x in.not F$ : $F != overline(F)$.

#card("vois", "Voisinage", ("Maths.Topologie",))

Définition de voisinage.

#answer

Soit $(E, d)$ un espace métrique et $x in E$.

On dit que $V subset.eq E$ est un voisinage de $x$ dans $E$ s'il existe $r > 0$ tel que $B(x, r) subset.eq V$.

On note $cal(V)(x)$ l'ensemble des voisinages de $x$ dans $E$.

#card("densite", "Densité", ("Maths.Topologie",))

Définition de densité.

#answer

Soit $(E, d)$ un espace métrique, on dit que $A subset.eq E$ est dense dans $E$ si
$
  overline(A) = E
$

#card("interieur", "Interieur", ("Maths.Topologie",))

Définition de l'interieur d'une partie.

#answer

Soit $(E, d)$ un espace métrique, $A subset.eq E$ et $x in E$.

On dit que $x$ est un point interieur de $A$ s'il existe $r > 0$ tel que
$
  B(x, r) subset.eq A
$
C'est à dire $A in cal(V)(x)$.

On note $circle(A)$ l'ensemble des points interieurs de $A$.

- $circle(A) subset.eq A$

- $A$ est ouvert ssi $circle(A) = A$

- $circle(A)$ est le plus grand ouvert inclus dans $A$

- $circle(overparen(E \\ A)) = E \\ overline(A)$

On définie aussi la frontière d'une partie $partial A = "Fr" A = overline(A) \\ circle(A)$ qui est un fermé.

#card("limfunctop", "Limite d'une fonction", ("Maths.Topologie",))

Définition de la limite d'une fonction.

#answer

Soit $(E, d_E), (F, d_F)$ deux espaces métriques et $X subset.eq E$.

Soit $f in cal(F)(X, F)$, $a in overline(X)$, on dit que $f$ admet $l in F$ comme limite en $a$ si l'une des conditions équivalentes suivantes est vérifiée.

+ $forall epsilon > 0, exists delta > 0, f(B(a, delta) inter X) subset.eq B(l, epsilon)$

+ $forall V in cal(V)(l), exists W in cal(V)(a), f(W inter X) subset.eq V$.

+ $forall (x_n)_n in X^NN -> a, lim_(n -> oo) f(x_n) = l$.

*Démonstration*

- (1 $=>$ 2) Soit $V in cal(V)(l)$, on dispose donc de $B(l, epsilon) subset.eq V$, et donc de $delta > 0$ tel que 
  $
  f(underbrace(B(a, delta), W in cal(V)(a)) inter X) subset.eq B(l, epsilon) subset.eq V
  $

- (2 $=>$ 1) Soit $epsilon > 0$, comme $V = B(epsilon, l) in cal(V)(l)$, on dispose de $W in cal(V)(a)$, et donc de $delta > 0$ tel que 
  $
  f(B(a, delta) inter X) subset.eq f(W inter X) subset.eq V
  $

- L'écrire.

#card("continuite", "Continuité d'une fonction en un point", ("Maths.Topologie",))

Définition de continuité en un point.

#answer

Soit $(E, d_E), (F, d_F)$ deux espaces métriques, $X subset.eq E$ et $f in cal(F)(X, F)$.

On dit que $f$ est continue en $a in X$ si:
$
  lim_(x -> a) f(x) = f(a)
$

Ce qui équivaut à
$
  forall V in cal(V)(f(a)), f^(-1) (V) in cal(V)(a)
$ 

Il suffit d'ailleur que $f$ admette une limite en $a$, car dans ce cas cette limite est forcément $f(a)$.

*Démonstration*

- Supposons $f$ continue en $a$ : comme $lim_(x -> a) f(x) = f(a)$, pour tout $V in cal(V)(f(a))$ on dispose de $W in cal(V)(a)$ tel que #h(1fr)
  $
    f(W inter X) subset.eq V \
    cal(V) (a) in.rev W inter X supset.eq f^(-1) (V)
  $

- Soit $V in cal(V)(f(a))$ :
  $
    W = f^(-1)(V) in cal(V)(a) \
    f(W inter X) subset.eq V
  $

#card("contglob", "Continuité d'une fonction", ("Maths.Topologie",))

Définition de continuité (sur un ensemble) d'une fonction.

#answer

Soit $(E, d_E), (F, d_F)$ deux espaces métriques, $X subset.eq E$ et $f in cal(F)(X, F)$.

On dit que $f$ est continue sur $X$ ($f in C^0 (X, F)$) si pour tout $a in X$, $f$ est continue en $a$.

Ce qui est équivalent à
$
  forall Omega "ouvert de" F, f^(-1) (Omega) "ouvert de" X
$
On en déduit que
$
  forall F "fermé de" F, f^(-1) (F) "fermé de" X
$

*Démonstration*

- Supposons $f in C^0 (X, F)$, soit $Omega subset.eq F$ ouvert et $a in f^(-1)(Omega)$.

  Comme $f(a) in Omega$, $Omega in cal(V)(f(a))$, et par continuité en $a in X$ : $f^(-1)(Omega) in cal(V)(a)$.

- Soit $a in X, epsilon > 0$, comme $B(f(a), epsilon)$ est ouvert, $f^(-1)(B(f(a), epsilon))$ est un ouvert contenant $a$ : on dispose de $delta > 0$ tel que
  $
    B(a, delta) subset.eq f^(-1)(B(f(a), epsilon)) \
    f(B(a, delta) inter X) subset.eq B(f(a), epsilon)
  $
