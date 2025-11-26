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
