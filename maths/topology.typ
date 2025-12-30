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

#card("ptsextremaux", "Points extrémaux d'un convexe", ("Maths.Topologie.Connexité",))

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

#card("lipschitz", "Fonctions K-Lipschitziennes", ("Maths.Topologie",))

Définition des fonctions $K$-lipschitziennes.

#answer

Soit $(E, d_E), (F, d_F)$ deux espaces métriques et $X subset.eq E$.

Une fonction $f in cal(F)(X, F)$ est dite $k$-lipschitzienne pour un $k > 0$ si
$
  forall x, y in X, \ d_F (f(x), f(y)) <= k d_E (x, y)
$

Toute fonction lipschitzienne est uniformement continue, donc continue.

Exemples (notons $d = d_E$) :

- Pour tout $a$ in $E$, $x |-> d (x, a)$ est $1$-lipschitzienne.

- Pour tout $A subset.eq E$, $x |-> d (x, A)$ est $1$-lipschitzienne.

Si $E = KK^n$ un $KK$-ev de dimension finie muni de $norm(dot)_oo$ et $d$ qui en dérive.

- Pour tout $k in [|1, n|]$ : #h(1fr)
  $
    phi_k : func(KK^n, KK, x = vec(x_1, dots.v, x_n), x_k)
  $
  Est $1$-lipschitzienne.

- Pour tout $P in KK[X_1, dots, X_n]$
  $
    func(KK^n, KK, x = vec(x_1, dots.v, x_n), P(x_1, dots, x_n))
  $
  Est continue (par somme et produit de fonctions qui le sont).

*Démonstration*

- Soit $a in E, x, y in X$ #h(1fr)
  $
    abs(d(x, a) - d(y, a)) \ <= abs(d(x, y) + d(y, a) - d(y , a)) \
    <= d(x, y)
  $

- Soit $A subset.eq E, x, y in X$. Soit $a in A$
  $
    d(x, A) <= d(x, a) <= d(x, y) + d(y, a) \
    d(x, A) - d(x, y) <= d(y, a) \
  $
  Ceci pour tout $a$ d'où
  $
    d(x, A) - d(x, y) <= d(y, A) \
    d(x, A) - d(y, A) <= d(x, y) \
  $
  Et par symétrie
  $
    abs(d(x, A) - d(y, A)) <= d(x, y)
  $

- Soit $k in [|1, n|]$ et $x, y in KK^n$
  $
    abs(x_k - y_k) &<= max_(i in [|1, n|]) abs(x_i - y_i) \ &= norm(x - y)_oo
  $

#card("contapplin", "Continuité des applications linéaires", ("Maths.Topologie",))

Conditions de continuité d'une application linéaire.

#answer

Soit $E, F$ deux $KK$-evn, $f in cal(L)(E, F)$.

On a équivalence entre

+ $f$ continue sur $E$.

+ $f$ continue en $0$.

+ $exists k > 0, forall x in E, space norm(f(x)) <= k norm(x)$

+ $f$ est lipschitzienne.

Enfin en dimension finie toute application linéaire est continue.

*Applications multi-linéaires*

Similairement (démonstrations calculatoires), pour
$
  f : func(product_(k = 1)^d (E_k, norm(dot)_k), (F, norm(dot)_F), (x_1, dots, x_d), f(x_1, dots, x_d))
$
on a équivalence entre

+ $f$ est $C^0$ sur $product_(k = 1)^d E_k$ (muni de la norme produit).

+ $exists k in RR_+^*, forall (x_1, dots, x_n) in product_(k = 1)^d E_k$

  $ norm(f(x_1, dots, x_d)) <= k norm((x_1, dots, x_d))$

*Démonstration*

- (1 $=>$ 2) Par définition.

- (2 $=>$ 3) Par continuité de $f$ en $0$ on dispose de $delta > 0$ tel que
  $
    f(B_E (0, delta)) subset.eq B_F (0, epsilon)
  $
  Donc pour tout $x in E$
  $
    norm(f(delta / 2 x / norm(x))) <= 1 \
    norm(f(x)) <= 2 / delta norm(x)
  $

- (3 $=>$ 4) Soit $x, y in E$
  $
    norm(f(x) - f(y)) &= norm(f(x - y)) \ &<= k norm(x - y)
  $

- (4 $=>$ 1) Immédiat.

En dimension finie, on prend une base $e = (e_1, dots, e_n)$ et la norme $norm(dot)_oo$, et pour $f in cal(L)(E, F)$ et $x in 
E$ on a
$
  norm(f(x)) &= norm(sum_(k = 1)^n x_k f(e_k)) \
  &<= sum_(k = 1)^n norm(x)_oo norm(f(e_k)) \
  &= (sum_(k = 1)^n norm(f(e_k))) norm(x)_oo
$

#card("nonconttopal", "Non continuité d'une application linéaire", ("Maths.Topologie",))

Critères de non continuité d'une application linéaire.

#answer

+ $f$ n'est pas continue sur $E$

+ Il existe $(x_n)_n in E^NN$ tel que #h(1fr)
  $
    forall n in NN, norm(x_n) = 1 \
    (norm(f(x_n)))_n tends(n->oo) +oo
  $

+ Il existe $(x_n)_n in E^NN$ tel que
  $
    (x_n)_n tends(n->oo) 0 \
    forall n in NN, norm(f(x_n)) = 1
  $

*Démonstration*

- (1 $=>$ 2) Comme $f$ n'est pas continue on a #h(1fr)
  $
    forall k > 0, exists x in E, norm(f(x)) > k norm(x)
  $
  Donc pour tout $n in NN$ on dispose de $tilde(x)_n in E$ tel que 
  $
  norm(f(tilde(x)_n)) > n norm(tilde(x)_n) \
  x_n = tilde(x)_n / norm(tilde(x)_n) quad quad norm(x_n) = 1 \
  norm(f(x_n))  > n " donc " norm(f(x_n)) -> oo
  $

- (2 $=>$ 3) Soit $(tilde(x)_n)_n in E^NN$ une telle suite.
  $
    x_n = tilde(x)_n / norm(f(tilde(x)_n)) quad quad norm(f(x_n)) = 1 \
    norm(x_n) = 1 / norm(f(tilde(x)_n)) -> 0
  $

- (3 $=>$ 1) $f$ n'est pas continue en $0$.



#card("hyptopo", "Nature topologique d'un hyperplan", ("Maths.Topologie",))

Nature topologique d'un hyperplan.

#answer

Soit $E$ un $KK$-evn, $H$ un hyperplan de $E$.

$H$ est soit fermé soit dense dans $E$.

*Démonstration*

Supposons que $H$ n'est pas fermé. On dispose de 
$
(h_n)_n in H^NN tends(n -> oo) z in.not H
$
Comme $H$ est un hyperplan, 
$
H plus.o "Vect"(z) = E
$
Ainsi pour tout $x in E$
$
  x = h + alpha z quad quad (h, alpha) in H times KK \
  (h + alpha h_n)_n in H^NN tends(n -> oo) x
$

#card("hypcontfl", "Continuité des formes linéaires", ("Maths.Topologie",))

Condition de continuité d'une forme linéaires, lien avec les hyperplans.

#answer

Soit $E$ un $KK$-evn.

Si $f in cal(L)(E, KK)$ est une forme linéaire alors $f$ est continue ssi $ker f$ est fermé.

*Démonstration*

- Si $f$ est continue, $ker f = f^(-1) {0}$ est fermé comme image reciproque d'un fermé par une application continue.

- Si $f$ n'est pas continue, on dispose de $(x_n)_n in E^NN$ tel que #h(1fr)
  $
    forall n in NN, abs(f(x_n)) = 1 \
    (x_n)_n tends(n->oo) 0
  $
  Quitte à poser $(x'_n)_n$ on peut suppposer $f(x_n) = 1 = f(x_0)$.
  $
    h_n = x_n - x_0 in ker f \
    lim_(n -> oo) h_n = -x_0 in.not ker f
  $
  Donc $ker f$ n'est pas fermé.

#card("normop", "Norme opérateur", ("Maths.Topologie",))

Définition de la norme opérateur.

#answer

Soit $E, F, G$ trois $KK$-evn, on définit
$
  cal(L)_C (E, F) = cal(L)(E, F) inter C^0 (E, F)
$
Qui est une $KK$-algèbre.

Pour $f in cal(L)_C (E, F)$ on définit
$
  norm(f)_"op" = lr(class("opening", bar.triple) f class("closing", bar.triple)) &= sup_(x in E\\{0}) norm(f(x)) / norm(x) \ &= sup_(x in SS(0, 1)) norm(f(x))
$
Qui est une norme d'algèbre sur $cal(L)_C (E, F)$, elle est donc sous-multiplicative :
$
  forall f, g in cal(L)_C (E, F), \
  norm(f compose g)_"op" <= norm(f)_"op" dot norm(g)_"op"
$

*Démonstration*

- Comme $f$ est linéaire et continue on dispose de $k > 0$ tel que #h(1fr)
  $
    forall x in E, norm(f(x)) <= k norm(x)
  $
  Ainsi
  $
  Gamma = {norm(f(x)) / norm(x), x in E\\{0}}
  $
  Est non vide majoré, donc le $sup$ existe.

- De plus
  $
    & space space space space space space lambda in Gamma  \
    &<=> exists x in E \\ {0}, lambda = norm(f(x)) / norm(x) \
    &<=> exists x in E \\ {0}, lambda = norm(f(x / norm(x))) \
    &<=> exists x in SS(0, 1), lambda = norm(f(x))
  $
  Ainsi $Gamma = {norm(f(x)), x in SS(0,1)}$.

- C'est bien une norme :

  + Soit $lambda in KK, f in cal(L)_C (E, F)$ #h(1fr)
    $
      norm(lambda f)_"op" &= sup_(x in SS(0, 1)) norm(lambda f(x)) \
      &= abs(lambda) norm(f)_"op"
    $

  + Soit $f in cal(L)_C (E, F)$ tel que $norm(f)_"op" = 0$, soit $x in E \\ {0}$
    $
      norm(f(x)) <= norm(f)_"op" dot norm(x) = 0 \
      f(x) = 0 " donc " f = 0
    $

  + Soit $f, g in cal(L)_C (E, F)$
    $
      & quad norm(f + g)_"op" \ &= sup_(x in SS(0, 1)) norm(f(x) + g(x)) / norm(x) \ 
      &<= sup_(x in SS(0,1)) [norm(f(x)) / norm(x) + norm(g(x)) / norm(x)] \
      &<= norm(f)_"op" + norm(g)_"op"
    $

- Soit $f in cal(L)_C (E, F), g in cal(L)_C (F, G)$ et $x in E$ :
  $
    norm(g(f(x))) &<= norm(g)_"op" norm(f(x)) \
    &<= norm(g)_"op" norm(f)_"op" norm(x)
  $
  D'où $norm(g compose f)_"op" <= norm(g)_"op" dot norm(f)_"op"$.

#card("exjaugeconvex", "Exercice : jauge d'un convexe", ("Maths.Exercice.Topologie",))

Soit $(E, norm(dot))$ un $RR$-evn et $K subset.eq E$ convexe, symétrique par rapport à l'origine (c'est à dire stable par $-$), d'intérieur non vide et borné.

On pose
$
  N : func(E, RR_+, x, inf space Set(lambda > 0, x / lambda in K))
$

+ Montrer que $N$ est bien définit.
+ Montrer que $N$ est une norme
+ Montrer que $N$ est équivalente à $norm(dot)$.
+ Montrer que $overline(B_N) (0, 1) = overline(K)$

#answer

Montrons d'abord qu'on dispose de $delta > 0$ tel que $B(0, delta) subset.eq K$.

Soit $a in circle(K)$, on dispose donc de $delta > 0$ tel que 
$
B(a, delta) subset.eq K
$
Par symétrie, on a alors 
$
B(-a, delta) subset.eq K
$
Soit $x in B(0, delta)$
$
  x + a in B(a, delta) subset.eq K \
  x - a in B(-a, delta) subset.eq K \
  1/2 (x + a) + 1/2 (x - a) = x in K
$
Par convexité.

+ Soit $x in E$ #h(1fr)
  $
    delta / (2 norm(x)) x < delta \
    (delta x) / (2 norm(x)) in B(0, delta) subset.eq K
  $
  D'où $Set(lambda > 0, x / lambda in K)$ non vide minoré par $0$ : $N(x)$ qui en est l'$inf$ existe et est positif.

+ + Comme $K$ est borné, on dispose de $R > 0$ tel que #h(1fr)
    $
      K subset.eq B(0, R)
    $
    Soit $x in E$ tel que $N(x) = 0$.

    Par caractérisation de la borne inférieur, on dispose de
    $
    (lambda_n)_n in RR_+^NN tends(n->oo) 0 \
    $
    Et pour tout $n in NN$
    $
      x / lambda_n in K subset.eq B(0, R) \
      norm(x) / lambda_n <= R \
      norm(x) / R <= lambda_n tends(n -> oo) 0
    $
    Donc $x = 0$
  + Soit $mu in RR, x in E$.
    - Si $mu = 0, N(mu x) = N(0) = 0$.
    - Si $mu > 0$
      $
        N(mu x) &= inf Set(lambda > 0, (mu x) / lambda in K) \
        &= mu N(x)
      $
    - Si $mu < 0$, par symétrie
      $
        N(mu x) = N(-mu x) = -mu N(x)
      $
  + Soit $x, y in E$, $lambda, mu > 0$ tels que $x / lambda, y / mu in K$ on a alors
    $
      (x + y) / (lambda + mu) &= underbrace(lambda /(lambda + mu), 1 - t) underbrace(x / lambda, in K) + underbrace(mu / (lambda + mu), t) underbrace(y / mu, in K) \
      &in K
    $
    Ainsi
    $
      N(x + y) <= lambda + mu
    $
    Et avec $lambda -> N(x), mu -> N(y)$ \
    $
      N(x + y) <= N(x) + N(y)
    $
+ Soit $x in E$, $lambda > 0$ tel que $x / lambda in K$.
  $
    norm(x) / lambda < R \
    norm(x) <= R dot N(x)
  $
  Et
  $
    (delta x) / (2 norm(x)) in K \
    N(x) <= 2 / delta norm(x)
  $
+ Soit $x in K, x / 1 in K$ donc $X in overline(B_N)(0, 1)$.

  Soit $x in overline(B_N)(0, 1)$.
  - Si $N(x) = 1$, on dispose de
    $
    (lambda_n)_n in RR_+^NN tends(n->oo) 1 \
    forall n in NN, x / lambda_n in K \
    x = lim_(n -> oo) x / lambda_n in overline(K)
    $
  - Si $N(x) < 1$, on dispose par propriété de la borne inférieur de $lambda in Ico(N(x), 1)$ tel que
    $
      x / lambda in K \
      x = (1 - lambda) dot 0 + lambda dot (x / lambda) in K
    $

#card("adhsuiteens", "Points d'adhérance d'une suite", ("Maths.Topologie",))

Définition et propriétés sur les points d'adhérance d'une suite.

#answer

Soit $(E, d)$ un espace métrique, $u = (u_n)_n in E^NN$ une suite.

On dit que $l in E$ est un point d'adhérance de $u$ s'il existe $phi$ extractrice tel que
$
  (u_phi(n))_n -> l
$

Notons $cal(V)(u)$ l'ensemble de ces points. On a

$
  cal(V)(u) = inter.big_(p in NN) overline({u_n, n >= p})
$

Qui est donc fermé.

De plus si $(u_n)$ converge vers $l in E$.
$
  K = {u_n, n in NN} union {l}
$
Est compact.

*Démonstration*

- Soit $l = lim_(n -> oo) u_phi(n)$, $p in NN$ #h(1fr)
  $
    (u_phi(n))_(n >= p) -> l in overline({u_n, n >= p}) \
  $
  Donc
  $
    l in inter.big_(p in NN) overline({u_n, n >= p})
  $

- Soit $l in inter.big_(p in NN) overline({u_n, n>=p})$, on pose $delta_n = 1 / (n+1)$.

  Comme $l in overline({u_n, n in NN})$, on dispose de $phi(0)$ tel que $d(u_phi(0), l) <= delta_0$.

  Supposons construits $phi(0), dots, phi(k)$, comme $l in overline({u_n, n >= phi(k) + 1})$, on dispose de $phi(k + 1)$ tel que
  $
    d(u_phi(k+1), l) < delta_(k+1)
  $
  Ainsi $phi$ extractrice et $(u_phi(n))_n -> l$.

- Soit $(x_n)_n in K^NN$, on pose
  $
    Gamma = {n in NN, exists k in NN, x_k = u_n} 
  $
  Si $Gamma$ est fini, alors $x_n$ prend une valeur une infinité de fois qui est valeur d'adhérance de $(x_n)$.

  Sinon on construit : on prend $psi(0) in Gamma$ et $phi(0)$ tel que $u_psi(0) = x_phi(0)$.

  Supposons construits $psi(0), dots, psi(k)$ et $phi(0), dots, phi(k)$, on considère
  $
    Gamma_(k+1) = Set(n > psi(k), exists q > phi(k)\, x_q = u_n)
  $
  Qui est infini, donc on prend $psi(k+1) in Gamma_(k+1)$ et $phi(k+1)$ tel que
  $
    u_psi(k+1) = x_phi(k+1)
  $
  D'où $l$ est valeur d'adhérance de $(x_n)$.

#card("compact", "Compacité", ("Maths.Topologie",))

Définition de compacité.

#answer

Soit $(E, d)$ un espace métrique, $K subset.eq E$ est dit compacte si de toute suite
$
  (u_n)_n in K^NN
$
On peut extraire une sous suite convergente
$
  (u_phi(n))_n -> l in K
$
La compacité ne dépend pas de l'espace ($E$), mais dépend de $d$.

Si $K$ est compacte :

- $K$ est bornée dans $E$.

- Si $K subset.eq X$, $K$ est fermé dans $X$.

- Si $F subset.eq K$ est fermé, alors $F$ est compact.

- Si $(u_n)$ est une suite à valeur dans $K$, alors elle converge ssi elle n'a qu'une seul valeur d'adhérance.

- Si $f in C^0 (K, F)$ avec $F$ un espace métrique, alors $f(K)$ est compacte.

- Un produit fini de compacts est compact.

- Toute intersection décroissante de compacts non vide est non vide.

*Démonstration*

- Supposons $K$ non bornée, soit $a in K$, posons $(x_n)_n in K^NN$ tel que pour tout $n in NN$ #h(1fr)
  $
    d(a, x_n) >= n
  $
  Donc $(x_n)$ ne peut converger, et $K$ n'est pas compacte.

- Soit $(x_n)_n in K^NN -> l in overline(X)$, par compacité on peut éxtraire
  $
    (u_phi(n))_n -> z in K
  $
  Et $z = l$ par unicité de la limite, donc $K$ est fermé.

- Soit $(x_n)_n in F^NN$, par compacité de $K supset.eq F$, on a #h(1fr)
  $
    (u_phi(n))_n -> l in K
  $
  Or comme $F$ est fermé et $(u_phi(n))_n in F^NN$, $l in F$ d'où $F$ compact.

- Par contraposée, soit $(x_n)_n in K^NN$ qui diverge, par compacité, elle admet une valeur d'adhérance $l$, mais $(x_n) arrow.r.not l_1$ c'est à dire #h(1fr)
  $
    exists epsilon>0, forall N in NN, exists n >= N, d(x_n, l_1) >= epsilon
  $
  On fixe $epsilon$, on dispose d'une suite $(x_phi(n))$ tel que
  $
    forall n in NN, d(x_phi(n), l) >= epsilon
  $
  Or cette suite admet une valeur d'adhérance $l_2 != l_1$.

- Soit $(y_n)_n in f(K)^NN$, on dispose de $(x_n)_n in K^NN$ tel que #h(1fr)
  $
    forall n in NN, f(x_n) = y_n
  $
  Et par compacité on peut éxtraire
  $
    (x_phi(n))_n -> l in K \
    (f(x_phi(n)))_n = (y_phi(n))_n -> f(l) in f(K)
  $

- Soit $(K_n)_n$ une suite décroissante de compacts non vides. 

  On construits une suite $(u_n)$ tel que $forall n in NN, u_n in K_n subset.eq K_0$, on peut donc en extraire une sous-suite convergente $(x_phi(n))_n -> z$.

  Ainsi pour tout $n in NN$ :
  $
    forall k >= n, x_phi(k) in K_phi(k) subset.eq K_n \
    z = lim_(k -> oo) x_phi(k) in K_n
  $
  Car $K_n$ est fermé, donc $z in inter.big_(n in NN) K_n$.
#card("thbatttop", "Théorème des bornes atteintes", ("Maths.Topologie",))

Théorème des bornes atteintes en sur un espace métrique.

#answer

Soit $K$ compact et $f in C^0(K, RR)$.

Comme $f(K)$ est compact, $f$ est bornée et atteint ses bornes.

Ainsi pour tout $x in E supset.eq K$
$
  d(x, K) = inf_(y in K) d(x, y)
$
Admet un $min$ : la distance est atteinte.

*Démonstration*

$f(K)$ est bornée et fermé car compact, ainsi il existe un $inf$ et un $sup$, et ce sont un $min$ et un $max$.

#card("ptsfixes", "Théorèmes du point fixe", ("Maths.Topologie",))

Énoncés et démonstrations des différents théorèmes du points fixe.

#answer

+ Soit $K$ compact, $f : K -> K$, si pour tout $x != y in K$
  $
    d(f(x), f(y)) < d(x, y)
  $
  Alors $f$ admet un unique point fixe.

*Démonstration*

+ On pose #h(1fr)
  $
    phi : func(K, RR_+, x, d(f(x), x))
  $
  Par compacité de $K$, $phi$ admet un $min$ atteint en $x_0 in K$ 
  Supposons par l'absurde que $f(x_0) != x_0$ :
  $
    phi(f(x_0)) &= d(f(f(x_0)), f(x_0))  \
    &< d(f(x_0), x_0) \ &< min phi
  $
  Absurde.

  Soit $x != x_0$
  $
    d(f(x), x_0) < d(x, x_0)
  $
  Donc $f(x) != x$.

#card("cpctdf", "Compacité en dimension finie", ("Maths.Topologie",))

Propriétés de compacité en dimension finie.

#answer

Soit $E$ un $KK$-ev de dimension finie muni de $norm(dot)_(oo,e)$ pour la base $e$.
$
  norm(dot)_(oo,e) : func(E, RR_+, display(x = sum_(k = 1)^d x_k e_k), display(max_(k in [|1,d|]) abs(x_k)))
$

- Pour tout $R > 0$, $overline(B_norm(dot)_(oo,e) (0, R))$ est compact.

- $K subset.eq E$ est compact ssi $K$ est fermé borné.

*Démonstration*

- On considère #h(1fr)
  $
    theta : func((RR^d, norm(dot)_oo), (E, norm(dot)_(oo,e)), vec(x_1, dots.v, x_d), sum_(k = 1)^d x_k e_d)
  $
  Qui est $1$-lipschitzienne et
  $
    overline(B_norm(dot)_(oo,e) (0, R)) = theta ([-R, R]^d)
  $
  Or $[-R, R]$ est compact (Bolzano-Weierstrass), d'où le résultat.

- Soit $K subset.eq E$ fermé borné, on dispose donc de $R > 0$ tel que #h(1fr)
  $
    K subset.eq underbrace(overline(B_norm(dot)_(oo,e) (0, R)), "compacte")
  $
  Donc $K$ est fermé dans un compact d'où le résultat.

#card("thheinetop", "Théorème de Heine", ("Maths.Topologie",))

Théorème de Heine sur un espace métrique.

#answer

Soit $K$ compact et $F$ un espace métrique.

Si $f in C^0(K, F)$ alors $f$ est uniformement continue.

*Démonstration*

Supposons par l'absurde que $f$ ne le soit pas.
$
  exists epsilon > 0, forall delta > 0, exists x, y in K, \
  cases(space d(x, y) < delta,space d(f(x), f(y)) >= epsilon)
$

On fixe un tel $epsilon$, on pose $delta_n = 1 / (n+1)$, et on construit $(x_n)_n, (y_n)_n in K^NN$ tels que
$
  forall n in NN, cases(space d(x_n, y_n) < delta_n, space d(f(x_n), f(y_n)) >= epsilon)
$
Par compacité, on peut éxtraire
$
  (x_phi(n))_n -> l in K \
  "Or " d(x_n, y_n) -> 0 " donc" \
  (y_phi(n))_n -> l
$
Or comme $f$ continue
$
  d(f(x_n), f(y_n)) -> d(f(l), f(l)) = 0 >= epsilon
$
Absurde.

#card("eqnormdf", "Équivalence des normes en dimension finie", ("Maths.Topologie",))

Démonstration de l'équivalence des normes en dimension finie.

#answer

Soit $(E, norm(dot))$ un $KK$-evn de dimension finie.

On prend $e = (e_1, dots, e_d)$ base de $E$. On montre que toute norme $N$ sur $E$ est équivalente à $norm(dot)_(e,oo)$.

Comme $N$ est une application linéaire, $N$ est continue donc lipschitzienne sur $E$ :
$
  forall x = sum_(k = 1)^d x_k e_k in E, \
  N(x) <= sum_(k = 1)^d abs(x_k) N(e_k) <= beta norm(x)_(e,oo) \
  "Où " beta = sum_(k = 1)^d N(e_k)
$

De plus comme $SS_(e,oo) (0,1)$ est fermée et bornée, elle est donc compacte comme $E$ est de dimension finie. Ainsi
$
  alpha = min_(x in SS_(e,oo) (0,1)) N(x) = N(x_0) > 0  \
  "avec " x_0 in SS_(e,oo) (0,1)
$
Ainsi pour tout $x in E \\ {0}$
$
  alpha <= N(x / norm(x)_(e,oo)) \
  alpha norm(x)_(e,oo) <= N(x) <= beta norm(x)_e(oo)
$

*Conséquences*

En dimension finie, pour toute norme :

- Toute application linéaire est continue.

- Les compacts sont les fermés bornés.

- Toute suite bornée admet au moins une valeur d'adhérance, et converge ssi elle n'en a qu'une.

- Tout espace de dimension finie est fermé (caractère séquentielle).

- La distance à un fermé est atteinte.

#card("proptopgln", "Propriétés topologiques du groupe linéaire", ("Maths.Topologie.Réduction",))

Propriétés topologiques du groupe linéaire.

#answer

$"GL"_n (KK)$ est un ouvert dense de $M_n (KK)$

Et plus généralement pour tout $p in [|0, n|]$, $Set(M in M_n (KK), "rg" M >= p)$ est un ouvert.

*Démonstration*

- $"GL"_n$ est ouvert comme image reciproque de $KK\\{0}$ par $det$ (qui est continue).

- Soit $P in "GL"_n (KK), delta > 0$, Soit $lambda = min "Sp" (P)$, afin que $lambda / 2$ ne soit pas valeur propre, c'est à dire $P - lambda / 2 I_n in "GL"_n (KK)$.

- Soit $p in [|0, n|]$, pour $norm(dot) : M |-> "tr" (M^TT M)$. Soit $M in M_n (KK)$ tel que $"rg" M >= p$, on dispose d'une sous matrice inversible extraite de taille $p$, or $"GL"_p (KK)$ est un ouvert, donc on dispose d'une boule bien choisie qui marche.

#card("proptopdiag", "Nature topologique des matrices diagonales", ("Maths.Topologie.Réduction",))

Nature topologique des matrices diagonales.

#answer

Notons $"DZ"_n (KK) = Set(A in M_n (KK), A "diagonalisable")$ et $"TZ"_n (KK) = Set(A in M_n (KK), A "trigonalisable")$.

On a

 - $"DZ"_n (CC)$ est dense dans $M_n (CC)$.

 - $"DZ"_n (RR)$ est dense dans $"TZ"_n (RR)$.

*Démonstration*

Montrons que $Set(A in M_n (KK), chi_A "SARS")$ est dense dans $M_n (CC)$.

Soit $A in M_n (CC)$
$
  A &= P underbrace(mat(t_11,, (*);,dots.down;,,t_(n n) ), T) P^(-1) \

  A_k &= P mat(t_11 + 1 / k,, (*);,dots.down;,,t_(n n) + n / k)
$

À partir d'un rang assez grand on a $chi_A_k$ SARS.

Même démonstration pour $"DZ"_n (RR)$ dans $"TZ"_n (RR)$.

#card("nattopcycl", "Nature topologique de l'ensemble des matrices cycycliques", ("Maths.Topologie.Réduction",))

Nature topologique de l'ensemble des matrices cycycliques.

#answer

$Omega = Set(A in M_n (CC), A "cyclique")$ est un ouvert dense de $M_n (CC)$.

Et de plus
$
  Pi : func(M_n (CC), CC_n [X], A, Pi_A)
$
N'est continue que sur $Omega$.

*Démonstration*

- $Omega$ est un ouvert : #h(1fr)
  $
    A in Omega \ <=> exists x_0 in CC^n, "Vect"(x_0, dots, A^(n - 1) x_0)  = CC^n \
    <=> exists x_0 in CC^n, det (x_0, dots, A^(n-1) x_0) != 0
  $

  Ainsi 
  $
    phi_x_0 : func(M_n (CC), CC, A, det(x_0, dots, A^(n-1) x_0)) \
    Omega = union.big_(x_0 in CC^n) phi_(x_0)^(-1) (CC^*)
  $

- De plus $cal(S) = Set(A in M_n (CC), chi_A "SARS") subset.eq Omega$  est dense dans $M_n (CC)$, donc $Omega$ aussi.

- Soit $A in Omega$, on dispose donc de $V = B(A, delta) subset.eq Omega$, or $Pi|_V = chi|_V$ (par cyclicité : $Pi_M = chi_M$), et $chi$ est continue, donc $Pi$ aussi (en $A$).

- Soit $A in.not Omega$, alors $deg Pi_A < n$, or on dispose de $(A_k)_k in Omega^NN -> A$, mais pour tout $k in NN$, $Pi_A_k = chi_A_k$ (unitaire de degré $n$), d'où $Pi_A_k arrow.r.not Pi_A$.

#card("etclassimtopred", "Étude de la classe de similitude d'une matrice", ("Maths.Topologie.Réduction",))

Étude de la classe de similitude d'une matrice.

#answer

Pour $A in M_n (CC)$, notons $cal(C)(A) = { P A P^(-1), P in "GL"_n(CC) }$. On a alors

- $A$ est diagonalisable ssi $cal(C)$ est fermé.

- $A$ est nilpotente ssi $0 in overline(cal(C)(A))$.

*Démonstration*

- On utilise le résultat suivant, si $M in T_n^+ (CC)$ on peut poser #h(1fr)
  $
    underbrace(dmat(1, k, dots.down, k^(n-1)), Q_k) quad quad underbrace(dmat(1, epsilon, dots.down, epsilon^(n-1)), P_epsilon) \
    underbrace(mat(t_11,,,(*);,t_22;,,dots.down;,,,t_(n n)), M) quad quad underbrace(dmat(t_11, t_22, dots.down, t_(n n)), D) \
  $
  On a alors
  $
    Q_k M Q_k^(-1) = mat(t_11,,A_(i j) k^(i - j);,dots.down;,,t_(n n)) tends(k -> oo) D \
    P_epsilon^(-1) M P_epsilon = mat(t_11,,A_(i j) epsilon^(j - i);,dots.down;,,t_(n n)) tends(epsilon -> 0) D
  $

- Supposons $cal(C)(A)$ fermé. Comme $A in cal(M)_n (CC)$, on dispose de $T in cal(C)(A) inter T_n^+ (CC)$, et on peut donc poser
  $
    A_k = Q_k T Q_k^(-1) in cal(C) \
    lim_(k -> oo) A_k = D in cal(C) \
  $
  D'où $A$ est diagonalisable.

- Soit $A in M_n (CC)$ diagonalisable. Soit $(R_k)_k in "GL"_n (CC)^NN$ tel que $A_k = R_k A R_k^(-1) -> B in M_n (CC)$.

  Comme $chi$ est un invarient de similitude et une application continue, on a $chi_A = chi_B$.

  De plus $Pi_A (A_k) = R_k Pi_A (A) R_k^(-1) = 0$ et $M |-> Pi_A (M)$ est continue, d'où $Pi_A (B) = 0$ (qui est SARS), ainsi $B$ est diagonalisable.

  Donc $B in cal(C)(A)$.

- Supposons que $0 in overline(cal(C)(A))$, on dispose de $(A_k)_k in C(A)^NN -> 0$, or $chi_A_k = chi_A$ et par continuité de $chi$, $chi_A = X^n$, d'où $A$ nilpotente.

- Supposons $A$ nilpotente, donc on dispose de $T in cal(C)(A) inter T_n^(++) (CC)$
  $
    Q_k T Q_k^(-1) tends(k -> oo) 0
  $
  D'où $0 in overline(cal(C)(A))$.

#card("ex42top", "Exercice : liens entre spectre norme subordonnée", ("Maths.Exercice.Topologie",))

Soit $n in NN^*$, $norm(dot)$ une norme sur $CC^*$. On note 
$
norm(dot)_"op" : func(M_n (CC), RR_+, A, sup_(X in CC^n \\ {0}) norm(A X) / norm(X))
$ 

Pour $A in M_n (CC)$, on note $rho (A) = max_(lambda in "Sp" (A)) abs(lambda)$.

+ Montrer que pour toute matrice $A$, $rho(A) <= norm(A)_"op"$.

+ Montrer que $rho(A^k) = rho(A)^k$ pour $k in NN^*$. Montrer que $rho(A) <= norm(A^k)^(1 / k)_"op"$ pour $k in NN^*$.

+ Montrer que $norm(dot)_"op"$ est sous-multiplicative.

+ Donner un exemple de norme sur $M_n (CC)$ qui ne soit pas une norme d'opérateur.

+ Soit $norm(dot)_(oo,"op")$ la norme d'opérateur associé à la norme $norm(dot)_oo$ sur $CC^n$. Montrer que $norm(A)_(oo,"op") = max_(1 <= i <= n) sum_(j = 1)^n abs(a_(i,j))$.

+ Soit $T in T_n^+(CC))$. Pour $mu > 0$ on pose $Q_mu = dmat(1, dots.down, mu^(n - 1))$, calculer $lim_(mu -> +oo) norm(Q_mu T Q_mu^(-1))_(oo,"op")$.

+ Soient $A in M_n (CC)$ et $epsilon > 0$. Montrer qu'il existe une norme d'opérateur $N$ sur $M_n (CC)$ telle que $N(A) <= rho(A) + epsilon$.

+ Montrer que $rho(A) = lim_(k -> oo) norm(A^k)^(1/k)_"op"$.

+ En déduire l'équivalence entre

  - $lim_(k -> oo) A^k = 0$.
  - $forall X in M_(n,l) (CC), lim_(k -> oo) A^k X = 0$.
  - $rho(A) < 1$
  - Il existe sur $C^n$ une norme $norm(dot)$ tel que $norm(A)_"op" < 1$.
  - Il existe $M$ semblable à $A$ telle que $norm(M)_(oo,"op") < 1$.

#answer

// TODO: vraiment la grosse flemme là je vais pas te mentir. (M196)

#card("precomp", "Précompacité", ("Maths.Topologie",))

Définition de précompacité.

#answer

On dit que $A subset.eq E$ est précompacte si
$
  forall epsilon > 0, exists N in NN, exists (x_1, dots, x_n) in E^n, \ A subset.eq union.big_(k = 1)^n B(x_k, epsilon)
$

Toute partie compacte est précompacte.

*Démonstration*

- Par contraposée. Soit $A$ non précompacte :
  $
    exists epsilon > 0, forall N in NN, forall (x_1, dots, x_n) in E^n \
    A subset.eq.not union.big_(k = 1)^n B(x_k, epsilon)
  $
  Fixons un tel $epsilon$, et construisons une suite par récurrence : $u_0 in A$ quelconque, et
  $
   forall n in NN^*, u_n in A \\ union.big_(k = 0)^(n-1) B(u_k, epsilon)
  $
  Ainsi $(u_n)_n$ ne peut admettre de valeur d'adhérance, donc $A$ n'est pas compacte.

// TODO: Peut être procéssus diagonal d'extraction ? (M198)

#card("borellebesgueseg", "Borel Lebesgue sur un segment", ("Maths.Topologie",))

Énoncé et démonstration de Borel-Lebesgue sur un segment.

#answer

Pour $K = [a, b] subset.eq RR$ tel que $K subset.eq union.big_(i in I) Omega_i$, où $(Omega_i)_(i in I)$ est une famille quelconque d'ouverts de $RR$. 

On dispose de $J subset.eq I$ fini tel que $K subset.eq union.big_(j in J) Omega_j$.

*Démonstration*

Posons

$
  Gamma = Set(c in [a, b], exists J subset.eq I\, cases( space J "fini", space [a, c] subset.eq union.big_(j in J) Omega_j))
$

Qui est non vide ($a in Gamma$) et majoré, posons $beta = sup Gamma$.

Or $beta in [a, b]$, donc on dispose de $i_0 in I$ tel que $beta in Omega_i_0$, donc il existe $delta_0$ tel que
$
  [beta - delta_0, beta + delta_0] subset.eq Omega_i_0
$
Par propriété de la borne sup, on dispose aussi de $c in Gamma inter Ioc(beta - delta_0, beta)$.

Ainsi on a $J subset.eq I$ fini tel que $[a, c] subset.eq union.big_(j in J) Omega_j$.

Supposons par l'absurde que $beta < b$. 

Posons $beta' = min(b, beta + delta_0)$ et $J' = J union {i_0}$. Ainsi $[a, beta'] subset.eq union.big_(j in J') Omega_j$, or $beta' in Ioc(beta, b)$, qui est absurde.

Donc $beta = b$.

#card("borellebesgue", "Borel-Lebesgue", ("Maths.Topologie",))

Énoncé et démonstration de Borel-Lebesgue.

#answer

On définit un compact au sens de Borel-Lebesgue comme une partie $K$ tel que si $(Omega_i)_(i in I)$ est une famille quelconque d'ouverts de $E$ tel que $K subset.eq union.big_(i in I) Omega_i$, alors
$
  exists J subset.eq I, J "finie et" K subset.eq union.big_(j in J) Omega_j
$

De manière équivalente (Borel-Lebesgue version fermé) : si $(G_i)_(i in I)$ est une famille quelconque de fermés de $K$ tels que $inter.big_(i in I) G_i = emptyset$ alors
$
  exists J subset.eq I, J "finie et" inter.big_(j in J) G_j = emptyset
$

*Équivalence*

Soit $(E, d)$ un espace métrique. Toute partie compacte au sens de Bolzano-Weierstrass, est compacte au sens de Borel-Lebesgue (et vis-versa).

*Démonstration*

Soit $K subset.eq union.big_(i in I) Omega_i$ compacte (au sens de Bolzano-Weierstrass).

- Montrons que
  $
    (exists epsilon > 0, forall x in K, exists i in I, B(x, epsilon) subset.eq Omega_i) \
    eq.triple not (forall epsilon > 0, exists x in K, forall i in I, B(x, epsilon) subset.eq.not Omega_i)
  $

  Par l'absurde, posons $epsilon_n = 1/(n+1)$, on dispose donc de $(x_n) in K^NN$ tel que
  $
    forall i in I, B(x_k, 1 / (k+1)) subset.eq.not Omega_i
  $
  Qu'on peut extraire $(x_phi(n))_n -> z in K$.

  Soit $j in I, delta > 0$ tels que $B(z, delta) subset.eq Omega_j$. Pour $N$ assez grand on a pour tout $n >= N$ :
  $ 
    d(x_phi(n), z) < delta / 2 quad quad 1 / (N + 1) <= delta / 2 \
    B(x_phi(n), 1 / (phi(n) + 1)) subset.eq B(z, delta) subset.eq Omega_j
  $
  Qui est absurde.

- Donc on dispose bien d'un tel $epsilon$. Par précompacité de $K$ on dispose de $x_1, dots, x_n in K$ tels que $K subset.eq union.big_(k = 1)^n B(x_k, epsilon)$.

  Or pour tout $k in [|1, n|]$ on dispose de $i_k in I$ tel que $B(x_k, epsilon) subset.eq Omega_i_k$ d'où
  $
    K subset.eq union.big_(k = 1)^n Omega_i_k
  $

- La version fermé s'obtient en prenant $G_i = K\\Omega_i$.

- La reciproque découle de la version fermée :

  Soit $K$ compact au sens de Borel-Lebesgue, $(x_n)_n in K^NN$ une suite.

  On a montrer que $S = {"valeurs d'adhérance de" (x_n)} = inter.big_(n in NN) overline({x_k, k >= n})$.

  On note $F_n = overline({x_k, k >= n})$ fermé dans $KK$.
  
  Pour tout $n_1 < dots.c < n_d in NN$
  $
    x_n_d in inter.big_(k = 1)^d F_n_k
  $
  Donc comme $K$ compacte $inter.big_(n in NN) F_n != emptyset$, donc $(x_n)$ admet au moins une valeur d'adhérance dans $K$.
