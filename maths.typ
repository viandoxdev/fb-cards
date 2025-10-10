#import "cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#import "utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/lilaq:0.4.0" as lq

#card("anatl", "Taylor-Langrange", ("Maths.Analyse.Dérivation", "Maths.Analyse.Taylor"))

Théorème de Taylor-Lagrange, et conditions d'application.

#answer

Soit $f : Icc(a, b) -> RR$, $C^n$ sur $Icc(a, b)$ et $D^(n+1)$ sur $Ioo(a,b)$

Il existe $c in Ioo(a, b)$ tel que
$
  f(b) = &sum_(k = 0)^(n) f^((k))(a) (b - a)^k / (k!) \ 
         &+ f^((n+1)) (c) (b - a)^(n+1) / ((n+1)!)
$

#card("anatlri", "Taylor reste intégrale", ("Maths.Analyse.Intégration", "Maths.Analyse.Taylor"))

Théorème de Taylor reste intégrale, et conditions d'application.

#answer

Soit $f : Icc(a, b) -> RR$, $C^(n+1)$

#scale(90%, $
  f(b) = &sum_(k = 0)^(n) f^((k))(a) (b - a)^k / (k!)  \ &+ integral_a^b f^((n + 1)) (t) (b - t)^n / (n!) dif t
$)

#card("inegtri", "Inégalitée Triangulaire", ("Maths.Analyse.Réels", "Maths.Analyse.Complexes"))

Inégalitée triangulaire première et deuxième forme.

#answer

Soit a, b in $CC$
$
  |a + b| <= |a| + |b| \
  ||a| - |b|| <= |a - b| <= |a| + |b|
$

#card("moivre", "Formule de Moivre", ("Maths.Analyse.Complexes",))

Formule de Moivre.

#answer

Soit $theta in RR$

$
  (cos theta + i sin theta)^n = cos (n theta) + i sin (n theta)
$

#card("trigsomme", "Formules d'addition trigonometrique", ("Maths.Analyse.Complexes", "Maths.Trigonométrie.Euclidienne"))

Formules d'additions trigonométriques.

#answer

Soient $theta, phi in RR$
$
  cos(theta + phi) &= cos theta cos phi - sin theta sin phi \
  sin(theta + phi) &= cos theta sin phi + sin theta cos phi \
  tan(theta + phi) &= (tan theta + tan phi) / (1 - tan theta tan phi) \
$

#card("trigdup", "Formules de duplication trigonométrique", ("Maths.Analyse.Complexes", "Maths.Trigonométrie.Euclidienne"))

Formules de duplication trigonométriques.

#answer

Soit $theta in RR$
$
  cos(2 theta) &= cos^2 theta - sin^2 theta \
  sin(2 theta) &= 2 cos theta sin theta \
  tan(2 theta) &= (2 tan theta) / (1 - tan^2 theta) \
$

#card("triglin", "Formules de linéarisation trigonométrique", ("Maths.Analyse.Complexes", "Maths.Trigonométrie.Euclidienne"))

Formules de linéarisation trigonométriques.

#answer

Soient $a, b in RR$
$
  cos a cos b &= 1/2 [ cos(a + b) + cos(a - b) ] \
  sin a sin b &= 1/2 [ cos(a - b) - cos(a + b) ] \
  cos a sin b &= 1/2 [ sin(a + b) - sin(a - b) ] \
$

#card("trigfac", "Formules de factorisation trigonométrique", ("Maths.Analyse.Complexes", "Maths.Trigonométrie.Euclidienne"))

Formules de factorisation trigonométriques.

#answer

Soient $p, q in RR$
$inline(
  cos p + cos q &= 2 cos((p + q) / 2) cos ((p - q) / 2) \
  cos p - cos q &= -2 sin ((p + q) / 2) sin ((p - q) / 2) \
  sin p + sin q &= 2 sin ((p + q) / 2) cos ((p - q) / 2) \
)$

#card("trigts2", "Formules en tangente de theta sur deux", ("Maths.Analyse.Complexes", "Maths.Trigonométrie.Euclidienne"))

Formules en $tan theta / 2$.

#answer

Soit $theta in RR$
$
  cos theta &= (1 - tan^2 theta / 2) / (1 + tan^2 theta / 2) \
  sin theta &= (2 tan theta / 2) / (1 + tan^2 theta / 2) \
  tan theta &= (2 tan theta / 2) / (1 - tan^2 theta / 2) \
$

#card("trigparper", "Formules de parité et périodicité trigonométriques", ("Maths.Analyse.Complexes", "Maths.Trigonométrie.Euclidienne"))

Formules de parité et périodicité trigonométriques.

#answer

Soit $theta in RR$
$
  sin(pi / 2 - theta) &= cos theta \
  cos(pi / 2 - theta) &= sin theta \
  cos(pi + theta) &= -cos theta \
  sin(pi + theta) &= -sin theta \
$

#card("sommecons", "Formules de somme d'entiers consécutifs", ("Maths.Calculs",))

Forme explicites des sommes suivantes :
$
  sum_(k=1)^n k = thin ? \
  sum_(k=1)^n k^2 = thin ? \
  sum_(k=1)^n k^3 = thin ? \
$

#answer

$
  sum_(k=1)^n k = (n (n+1)) / 2 \
  sum_(k=1)^n k^2 = (n (n+1)(2n + 1)) / 6 \
  sum_(k=1)^n k^3 = ((n(n+1)) / 2)^2 = (n^2(n+1)^2) / 4 \
$

#card("sommenewton", "Formule de newton", ("Maths.Calculs",))

Soit $n in NN$, $x, a, b in CC$
$
  x^n - 1 = thin ? \
  a^n - b^n = thin ? \
$

#answer

$
  x^n - 1 = (x - 1) sum_(k = 0)^(n - 1) x^k \
  a^n - b^n = (a - b) sum_(k = 0)^(n - 1) a^k b^(n - k - 1) \
$

#card("coefbi", "Formules sur les coéfficients binomiaux", ("Maths.Calculs",))

Soit $k, n, p in NN$

#pad(x: 20%, grid(columns: (1fr, 6em, 1fr),
$
  vec(n, 0) &= thin ? \
  sum_(k=0)^n vec(n, k) &= thin ? \
  vec(n, n - k) &= thin ? \
$, [],
$
  vec(n, n) &= thin ? \
  k vec(n, k) &= thin ? \
  vec(k, p) vec(n, k) &= thin ?
$
))
$
vec(n, k) + vec(n, k+1) = thin ?
$

#answer

Soit $k, n, p in NN$

$
  vec(n, 0) = vec(n, n) = 1 \
  sum_(k=0)^n vec(n, k) = 2^n \
  vec(n, n - k) = vec(n, k) \
  k vec(n, k) = n vec(n - 1, k - 1) \
  vec(k, p) vec(n, k) = vec(n, p) vec(n - p, k - p) \
  vec(n, k) + vec(n, k+1) = vec(n + 1, k + 1)
$

#card("cribleens", "Formule du crible", ("Maths.Algèbre.Ensembles",))

Formule du crible : soit $A_1, dots, A_n subset.eq E$

$
  abs(union.big_(k = 1)^n A_k) = thin ?
$

#answer

Soit $A_1, dots, A_n subset.eq E$
$
  abs(union.big_(k = 1)^n A_k) thick & script(= thick abs(A_1) + abs(A_2) + dots.c + abs(A_n)) \
  & script(- thick abs(A_1 inter A_2) - dots.c - abs(A_(n - 1) inter A_n)) \
  & script(+ thick abs(A_1 inter A_2 inter A_3) + dots.c + abs(A_(n - 2) inter A_(n - 1) inter A_n)) \
  & script(thick dots.v) \
  & script(+ thick (-1)^n abs(A_1 inter A_2 inter dots.c inter A_n)) \
$

$
    = sum_(k = 1)^n (-1)^(k+1) sum_script(1 <= i_1 < dots.c < i_k <= n) abs(inter.big_(j = 1)^k A_(i_j))
$

#card("majmaxbs", "Majorant, borne supérieure, élément maximale", ("Maths.Algèbre.Relations",))

Soit $(E, <=)$ un ensemble ordonné et $A subset.eq E$, définitions de

- Majorant
- Maximum
- Borne supérieure
- Élément maximale

#answer

Soit $(E, <=)$ un ensemble ordonné et $A subset.eq E$.

/ Majorant: $M in E$ est un majorant de $A$ si $forall x in A, x <= M$
/ Maximum: $M$ est le maximum de $A$ si $M$ est un majorant de $A$ et $M in A$. S'il existe il est unique.
/ Borne supérieure: $B$ est la borne supérieure de $A$ si $B$ est le plus petit majorant de $A$ : $forall M in E, (forall x in A, x <= M) => B <= M$. Si elle existe elle est unique.
/ Élément maximale: $M$ est un élément maximale de $A$ si $M$ n'est plus petit que personne : $exists.not x in A, M <= x$. Dans le cas d'un ensemble totalement ordonné, seul un maximum est élément maximale, dans le cas d'un ensemble non totalement ordonné, il peut en exister plusieurs.

#card("edlo1", "EDL d'ordre 1", ("Maths.Analyse.EDL",))

Soit $a, b in CC, c(x)$ et $C(x)$ tel que $C'(x) = c(x)$.

$
  (E_1) : quad y' = a y + b \
  (E_2) : quad y' = a(x) y
$

#answer

Les solutions $S_1$ et $S_2$ de $(E_1)$ et $(E_2)$ sont
$
  S_1 = {x |-> lambda e^(a x) - b / a, lambda in RR} \
  S_2 = {x |-> lambda e^(A(x)), lambda in RR}
$

#card("edlsepvar", "Méthode de séparation des variables", ("Maths.Analyse.EDL",))

Soit $a(x) in D^1$
$
  (dif y) / (dif x) = a(x) y \
  y(x) = thin ?
$

#answer

Soient $a(x) in D^1$ et $A(x)$ une primitive de $a(x)$.
$
  (dif y) / (dif x) = a(x) y \
  (dif y) / y = a(x) dif x \
  integral_(y_0)^y (dif y) / y = integral_(x_0)^x a(x) dif x \
  ln y - ln y_0 = A(x) - A(x_0) \
  y = underbrace(y_0 e^(-A(x_0)), lambda) e^(A(x))
$

#card("edlvarcst", "Méthode de variation de la constante", ("Maths.Analyse.EDL",))

Soient $a(x), b(x) : RR -> RR$ et $A(x)$ une primitive de $a(x)$.
$
  y' = a(x) y + b(x) \
  f_h : quad y(x) = lambda e^(A(x))
$

Trouver $f_p$ solution particulière par la variation de la constante.

#answer

Soient $a(x), b(x) : RR -> RR$ et $A(x)$ une primitive de $a(x)$.
$
  y' = a(x) y + b(x) \
  f_h : quad y(x) = lambda e^(A(x))
$
On fait varier la constante : $lambda -> lambda(x)$ :
$
  f_p (x) &= lambda(x) e^(A(x)) \
  f_p' (x) &= a(x) f_p(x) + b(x) \
  &= lambda'(x) e^(A(x)) + lambda(x) a(x) e^(A(x))  \
  &= lambda(x) a(x) e^(A(x)) + b(x) \
  lambda'(x) &= b(x) e^(-A(x)) \
  lambda (x) &= integral b(x) e^(-A(x)) dif x
$

#card("edlo2", "EDL d'ordre 2", ("Maths.Analyse.EDL",))

Soient $a, b, c in CC$, résolution de l'équation homogène :
$
  a y'' + b y' + c y = 0
$

#answer

Soient $a, b, c in CC$
$
  a y'' + b y' + c y = 0
$
On appèlle équation caractèristique
$
  (E C) : quad a z^2 + b z + c = 0
$
- Si $Delta > 0$, soit $r_1, r_2$ les racines (réelles) de $(E C)$
  $
    f_h(x) = lambda e^(r_1 x) + mu e^(r_2 x), quad lambda, mu in RR
  $
- Si $Delta = 0$, soit $r$ la racine double de $(E C)$
  $
  f_h(x) = (lambda + mu x) e^(r x), quad lambda, mu in RR
  $
- Si $Delta < 0$, soit $alpha + i beta$ et $alpha - i beta$ les racines complexes de $(E C)$ #h(1fr)
  $
  f_h(x) = e^(alpha x)(lambda cos (beta x) + mu sin (beta x))
  $

#card("axgroupe", "Axiomes d'un groupe", ("Maths.Algèbre.Groupes",))

Soit $G$ un ensemble muni d'une opération interne $*$, quels axiomes pour que $(G, *)$ ait une structure de groupe ?

#answer

Soit $G$ un ensemble et $*$ une opération interne, $(G, *)$ forme un groupe si
#[
  #set enum(numbering: "i)")
  + Associativité : #h(1fr)
    $
      forall x, y, z in G, x * (y * z) = (x * y) * z
    $
  + Existence d'un neutre :
    $
      exists e in G, forall x in G, x * e = e * x = x
    $
  + Existence d'inverse :
    $
      forall x in G, exists y in G, x * y = y * x = e
    $
]

#card("vocensstruct", "Vocabulaire d'ensemble structuré", ("Maths.Algèbre",))

Définitions du vocabulaire suivant 
- Magma
- Semi-groupe
- Monoïde
- Groupe

#answer

#[
  #set text(size: 0.6em)
  #align(center, table(columns: (auto,) * 6,
    table.header([Ensemble], [Loi interne], [Associative], [Neutre], [Inverse], [Nom]),
    $times$, $times$, [], [], [], [Magma],
    $times$, $times$, $times$, [], [], [Semi-groupe],
    $times$, $times$, $times$, $times$, [], [Monoïde],
    $times$, $times$, $times$, $times$, $times$, [Groupe]
  ))
]

#card("axsousgroupe", "Axiomes d'un sous-groupe", ("Maths.Algèbre.Groupes",))

Soit $(G, *)$ un groupe, quels axiome pour que $H subset.eq G$ soit un sous-groupe ?

#answer

Soit $(G, *)$ un groupe et $H subset.eq G$, $H$ est un sous-groupe de $G$ si
#[
  #set enum(numbering: "i)")
  + Présence du neutre : #h(1fr)
    $
      e in H
    $
  + Stable par $*$ :
    $
      forall x, y in H, x * y in H
    $
  + Stable par inverse :
    $
      forall x in H, x^(-1) in H
    $
]

#card("thlagrange", "Théorème de Lagrange", ("Maths.Algèbre.Groupes",))

Énoncer le théorème de Lagrange sur les groupes.

#answer

Soit $(G, dot)$ un groupe fini et $H$ un sous-groupe de $G$

$
  |H| | |G|
$

#card("thlagrangedemo", "Démonstration du Théorème de Lagrange", ("Maths.Algèbre.Groupes",))

Démonstration du théorème de Lagrange

#answer

Soit $(G, dot)$ un groupe fini et $H$ un sous-groupe.

#let re = math.class("relation", $cal(R)$)
- Relation quotienté par $H$ : $x re y$ si $y x^(-1) in H$ (relation d'équivalence). On note $G \/ H$ l'ensemble des classes d'équivalences.
- Soit $x in G$, $accent(x, macron)$ sa classe d'équivalence pour $re$. $accent(x, macron) = H x = {h x, h in H}$.

  Par double inclusion :
  - $H x subset.eq accent(x, macron)$ : Soit $y in H x$, $y = h x$ avec $h in H$, donc $y x^(-1) = h in H$ d'où $y re x$ et $y in accent(x, macron)$.
  - $accent(x, macron) subset.eq H x$ : Soit $y in accent(x, macron)$, $y x^(-1) = h in H$, donc $y = h x in H x$.
- Donc $forall x in G, accent(x, macron) = H x tilde.eq H$ d'où $abs(accent(x, macron)) = abs(H)$.
- Enfin par le lemme du berger : $abs(G \/ H) = abs(G) / abs(H)$ et donc $abs(H) | abs(G)$.

#card("propmorphgrouplag", "Relation de cardinal pour un morphisme de groupe", ("Maths.Algèbre.Groupes",))

Soient $(G_1, +), (G_2, dot)$ des groupes et $phi : G_1 -> G_2$ un morphisme, avec $G_1$ fini. Que peut on dire de $abs(G_1)$ ?

#answer

Soient $(G_1, +), (G_2, dot)$ des groupes et $phi : G_1 -> G_2$ un morphisme, avec $G_1$ fini.

$
  abs(G_1) = abs(ker phi) dot abs(im phi)
$

#card("axanneaux", "Axiomes d'un anneau", ("Maths.Algèbre.Anneaux et corps",))

Soit $A$ muni de deux opérations internes $+$ et $dot$, quels axiomes pour que $(A, +, dot)$ soit un anneau ?

#answer

$(A, +, dot)$ est un anneau si :
#v(0.5em)
#[
  #set enum(numbering: "ia)")
  + $(A, +)$ est un groupe abélien
    + Associativité de $+$ #h(1fr)
    + Existence d'un neutre additif $(0_A)$
    + Existence d'opposés $(-x)$
    + Commutativité de $+$
  + Associativité de $dot$
  + Existence d'un neutre multiplicatif $(1_A)$
  + Distributivité de $dot$ sur $+$
    $
    x (y + z) &= x y + x z \
    (x + y) z &= x z + y z
    $
]

#card("dibzero", "Diviseur de zéro", ("Maths.Algèbre.Anneaux et corps",))

Définition de diviseur de $0$ dans un anneau.

#answer

Soit $(A, +, dot)$ un anneau, $x in A$ est dit diviseur de $0$ (à gauche) si $x != 0$ et $ exists y != 0, quad x y = 0$

#card("integrité", "Intégrité d'un anneau", ("Maths.Algèbre.Anneaux et corps",))

Définition d'un anneau intègre.

#answer

Un anneau $(A, +, dot)$ est dit intègre si
- $A$ est commutatif
- $A$ n'admet aucun diviseur de $0$

#card("grpinv", "Groupe des inversibles", ("Maths.Algèbre.Anneaux et corps",))

Définition de groupe des inversibles d'un anneau.

#answer

Le groupe des inversibles d'un anneau $(A, +, dot)$, est le groupe $(A^times, dot)$.

#card("ideal", "Idéal d'un anneau", ("Maths.Algèbre.Anneaux et corps",))

Définition d'un idéal d'un anneau, propriétés élémentaires.

#answer

Soit $(A, +, dot)$ un anneau et $I subset.eq A$, $I$ est un idéal de $A$ si

- $I$ est un sous-groupe additif de $A$
- $I$ est stable par produit externe : $forall x in I, forall a in A, a x in I$

Propriétés :

- Si $1 in I$ idéal de $A$, alors $I = A$.
- Plus généralement s'il existe $x in I$ inversible, $I = A$.
- Une intersection quelconque d'idéaux est un idéal.
- Une somme finie d'idéaux est un idéal.
- Si $phi: A_1 -> A_2$ un morphisme d'anneau avec $A_1$ commutatif, $ker phi$ est un idéal de $A_1$.
- Pour tout $b in A, b A$ est un idéal de $A$.
- Un idéal engendré par un ensemble est le plus petit idéal le contenant, dans le cas d'un singleton ${a} subset A$, il s'agit de $a A$.

#card("axcorps", "Axiomes d'un corps", ("Maths.Algèbre.Anneaux et corps",))

Soit $K$ muni de deux opérations internes $+$ et $dot$, quels axiomes pour que $(K, +, dot)$ soit un corps ?

#answer

$(K, +, dot)$ est un corps si :
#v(0.5em)
#[
  #set enum(numbering: "ia)")
  + $(K, +)$ est un groupe abélien
    + Associativité de $+$ #h(1fr)
    + Existence d'un neutre additif $(0)$
    + Existence d'opposés $(-x)$
    + Commutativité de $+$
  + Associativité de $dot$
  + Commutativité de $dot$
  + Existence d'un neutre multiplicatif $(1)$
  + Distributivité de $dot$ sur $+$
  + Existence d'inverses (sauf pour $0$)
  $
    forall x in K\\{0}, exists x^(-1) in K \
    x x^(-1) = x^(-1) x = 1
  $
]

#card("corpsgauche", "Corps gauche, anneau à division", ("Maths.Algèbre.Anneaux et corps",))

Qu'est-ce qu'un "corps gauche" ou "anneau à division" ?

#answer

Un corps gauche ou anneau a division et un anneau non commutatif dont tous les éléments sont inversible sauf $0$. C'est un corps dont le produit n'est pas commutatif.

#card("axsouscorps", "Axiomes d'un sous-corps", ("Maths.Algèbre.Anneaux et corps",))

Soit $(K, +, times)$ un corps, axiomes pour que $L subset.eq K$ soit un sous-corps ?

#answer

$(K, +, times)$ un corps, $L subset.eq K$ est un sous-corps si :
#v(0.5em)
#[
  #set enum(numbering: "ia)")
  + $0 in L$
  + $1 in L$
  + Stable par $+$
  + Stable par $-$ ou stable par opposé
  + Stable par $times$
  + Stable par $div$ ou stable par inverse
]

#card("carprem", "Primalité de la caracèristique d'un corps", ("Maths.Algèbre.Anneaux et corps",))

Si $(K, +, dot)$ est un corps de caractèristique non nulle, que peut-on dire sur celle ci ?

#answer

$(K, +, dot)$ un corps, notons $p$ sa caractèristique, si $p != 0$ alors $p$ est premier

Démonstration:

Notons $p = a b$ avec $a, b in NN$

$
  (sum_(k = 1)^a 1) (sum_(k = 1)^b 1) &= sum_(k = 1)^a sum_(k = 1)^b 1 \
  &= sum_(k = 1)^(a b = p) 1 \
  &= 0
$

Or un corps n'admet pas de diviseurs de $0$, donc $sum_(k = 1)^a 1 = 0$ ou $sum_(k = 1)^b 1 = 0$, d'où 
$
"ou" space vec(delim: #none, a = p\, b = 1, p = b\, a = 1)
$
Donc $p$ est premier.

#card("corpsfrac", "Corps des fractions", ("Maths.Algèbre.Anneaux et corps",))

Définition du corps des fractions d'un anneau intègre.

#answer

#[
  #let re = math.class("relation", $cal(R)$)
  $(A, +', dot)$ un anneau intègre.

  - Soit $(a, b),(c, d) in A times A\\{0}$, on définit la relation d'équivalence suivante :
    $
    (a, b) re (d, c) "si" a d = b c
    $
  - On note $a / b$ la classe d'équivalence de $(a, b)$.
  - On définit les opérations $+, times$ sur les fractions
    $
    a / b plus c / d = (a d +' c b) / (b d) \
    a / b times c / d = (a c) / (b d)
    $
  Le corps des fractions de $A$ est le corps 
  $
  (A times A\\{0}, plus, times)
  $
]

#card("thgauss", "Théorème de Gauss", ("Maths.Algèbre.Arithmétique",))

Théorème de Gauss.

#answer

Soit $a, b, c in NN$, si $a | b c$ et $a and b = 1$ alors $a | c$

#card("eqdioph", "Équations diophantiennes", ("Maths.Algèbre.Arithmétique",))

Résolutions d'une équation de la forme $a x + b y = c$ dans $ZZ$.

#answer


Soit $a, b, c in ZZ$
$
  (E) : quad a x + b y = c
$
- Solution homogène : On cherche un couple $(u, v) in ZZ^2$ (Bézout) tel que 
  $
  a u + b v = c
  $
- Solution particulière : il en existe si 
  $
  a and b | c
  $
- Les solutions sont 
  $
  S = cases(x = x_p - k b', y = y_p + k a') \
  "avec" (x_p, y_p) "solution particulière" \
  "et" a' = a / (a and b), quad b' = b / (a and b)
  $

#card("nbfermat", "Nombres de Fermat", ("Maths.Algèbre.Arithmétique",))

Que sont les nombres de Fermat, et quelques propriétés.

#answer

Le $n$-ème nombre de Fermat est 
$
F_n = 2^(2^n) + 1
$
Ils sont impaires et premier entre eux :

Soit $n < m in NN$,

$
  inline(
    &(2^(2^n) - 1)& dot &F_n& dot &F_(n+1) dots.c F_(m - 1) \
    &(2^(2^n) - 1)& dot &(2^(2^n) + 1)& dot &F_(n+1) dots.c F_(m - 1) \
    &&& (2^(2^(n+1)) - 1)& dot &F_(n+1) dots.c F_(m-1) \
  )
$
$
  dots.v \
  2^(2^(m)) - 1 = F_m - 2
$
Donc $F_n | F_m - 2$, d'où $F_m and F_n | F_m - 2$, donc $F_m and F_n | 2$, mais ils sont impaire donc premier entre eux.

#card("euclid", "Lemme d'Euclide", ("Maths.Algèbre.Arithmétique",))

Théorème du lemme d'Euclide.

#answer

Soit $p in PP, a,b in ZZ$,
$
p | a b => p | a "ou" p | b
$

Plus algébriquement :

$
  ZZ \/ p ZZ "est un anneaux intègre :" \
  a b equiv 0 space [p] => a equiv 0 space [p] "ou" b equiv 0 space [p]
$

#card("nbdiv", "Formule du nombre de diviseurs", ("Maths.Algèbre.Arithmétique",))

Formule du nombre de diviseurs d'un entier.

#answer

$
  n = p_1^alpha_1 p_2^alpha_2 dots.c p_k^alpha_k \
  "nombre de diviseurs" = product_(i = 1)^k (alpha_k + 1)
$

#card("crt", "Théorème des restes chinois", ("Maths.Algèbre.Arithmétique",))

Théorème des restes chinois.

#answer

Soit $n, m in NN^star$ premiers entre eux

- Formulation arithmétique : #h(1fr)
  $
  forall a in [|0, m-1|], forall b in [|0, n-1|], \
  exists! x in [|0, n m - 1|], \
  x equiv a space [m] "et" x equiv b space [n]
  $
- Formulation algébrique :
  $
  phi space : space func(delim: #none,
    ZZ \/ m n ZZ, ZZ \/ m ZZ times ZZ \/ n ZZ,
    x, vec(x &space [m], x &space [n])
  )
  $
  est un isomorphisme d'anneaux.
- Structure de preuve : injectivité par $ker phi$ + argument de cardinal.

#card("ptitfermat", "Petit théorème de Fermat", ("Maths.Algèbre.Arithmétique",))

Petit théorème de Fermat.

#answer

- Première formulation : #h(1fr)
  $
    forall p in PP, forall a in ZZ, \
    a and p = 1 => a^(p - 1) equiv 1 space [p]
  $
- Deuxième formulation (moins forte) :
  $
    forall p in PP, forall a in ZZ, \
    a^p equiv a space [p]
  $
- Démo :
  On étudie $(ZZ \/p ZZ)^times$ :
  $
    forall a in (ZZ \/p ZZ)^times \
    "ord"(a) | p - 1 "(Lagrange)" \
    "donc" a^(p - 1) equiv 1 space [p]
  $

#card("indeuler", "Indicatrice d'Euler", ("Maths.Algèbre.Arithmétique",))

Définition de l'indicatrice d'Euler, et propriétés.

#answer

La fonction indicatrice d'Euler est
$
  phi space : space func(delim: #none, NN^star, NN, n, abs((ZZ \/n ZZ)^times)) \
$
Quelques propriétés :

$
phi(p) = p - 1 \
phi(p^alpha) = p^alpha - p^(alpha - 1) \
m and n = 1 => phi(m n) = phi(m) phi(n) \
phi(n = p_1^alpha_1 p_2^alpha_2 dots.c p_k^alpha_k) = product_(i = 1)^k (p_i^alpha - p_i^(alpha - 1)) \
phi(n) / n = product_(i = 1)^(k) (1 - 1 / p_i) \
sum_(d in "Div"(n)) phi(d) = n
$
Pour se convaincre de la dernière :
$
1 / n + 2 / n + dots.c + n / n \
$
Sous formes irréductibles ($p_i and q_i = 1$)
$
p_1 / q_1 + p_2 / q_2 + dots.c + p_n / q_n
$
Il y a $n$ fractions, les $q_i in "Div"(n)$, et pour chaque $q_i$, on a tous les $p_i <= q_i$, qui sont premiers avec eux :

$
  underbrace(sum_(d in "Div"(n)), "somme sur" \ "tous les" \ "dénominateur") underbrace(phi(d), "nombre de" \ "fractions pour le" \ "dénominateur" d) = underbrace(n, "nombre de" \ "fractions")
$

Enfin, une généralisation du petit théorème de Fermat :

$
  a and n = 1 => a^(phi(n)) equiv 1 space [n]
$

#card("bezout", "Théorème de Bézout", ("Maths.Algèbre.Arithmétique",))

Énoncé et preuve du théorème de Bézout.

#answer

- Soient $a, b in NN$ et $d = a and b$ alors il existe $u, v in ZZ$ tel que $a u + b v = d$.
- Preuve : Soit $I = {a u + b v, (u, v) in ZZ }$

  $I$ est un idéal de $ZZ$, donc $exists d in ZZ, I = d ZZ$ (principalité de $ZZ$). Donc $d | a$ et $d | b$.

  Soit $diff$ tel que $diff | a$ et $diff | b$. $forall x in I, diff | x$, en particulier $diff | d$ d'où $diff <= d$.

  $a and b = d in I$ d'où $exists u,v in ZZ, d = a u + b v$

#card("propidcd", "Propriétés diviseurs communs", ("Maths.Algèbre.Arithmétique",))

Soit $a, b in ZZ$
$
  x | a "et" x | b "ssi" space ? \
  a | y "et" b | y "ssi" space ? \
  a ZZ + b ZZ = space ? \
  a ZZ inter b ZZ = space ? \
$

#answer

Soit $a, b in ZZ$
$
  x | a "et" x | b "ssi" space x | (a and b) \
  a | y "et" b | y "ssi" space m | (a or b) \
  a ZZ + b ZZ =  (a and b) ZZ\
  a ZZ inter b ZZ = (a or b) ZZ \
$

#card("corptotord", "Corps totalement ordonné", ("Maths.Analyse.Réels",))

Définition d'un corps totalement ordonné.

#answer

Soit $(K, +, dot)$ un corps et un ordre $<=$.

+ $forall x, y, z in K, x <= y => x + z <= y + z$
+ $forall x, y in K, x >= 0 "et" y >= 0 => x y >= 0$

$RR$ et $QQ$ sont ordonnés, $CC$ ne l'est pas. Mais il existe un seul corps totalement ordonné (à isomorphisme près) : $RR$.

#card("porpreel", "Propriété fondamentale des réels", ("Maths.Analyse.Réels",))

Propriété fondamentale des réels.

#answer

Toute partie non vide majoré de $RR$ admet une borne sup. De même pour minoré.

On en déduit (car $RR$ est totalement ordonné) que
- $x >= 0 => -x <= 0$
- Loi du signe de produit
- $x^2 >= 0$
- $1 > 0$
- $x > 0 => 1/x > 0$
- $0 < x <= y => 1/x >= 1/y$

#card("propsup", "Propriété de la borne supérieure", ("Maths.Analyse.Réels",))

Propriété de la borne supérieure.

#answer

Soit $A subset.eq RR$ non vide majoré, $S = sup A$ ssi
+ $forall x in A, x <= S$
+ $forall epsilon > 0, exists y in A, s - epsilon < y$

#card("partconv", "Partie convexe de R", ("Maths.Analyse.Réels",))

Définition de partie convexe.

#answer

Une partie convexe de $RR$ est un ensemble $C subset.eq RR$ tel que
$
  forall x <= y in C, Icc(x, y) subset.eq C
$
Les parties convexes de $RR$ sont des intervalles.

#card("densite", "Densité", ("Maths.Analyse.Réels",))

Définition de densité.

#answer

Soit $D subset.eq RR$, $D$ est dense dans $RR$ si
$
  forall a < b in RR, Ioo(a, b) inter D != emptyset
$
$QQ$ est dense dans $RR$, preuve : saut de grenouille.

#card("vois", "Voisinage", ("Maths.Analyse.Réels",))

Définition de voisinage.

#answer

Soit $x in overline(RR)$, $V subset.eq RR$ est un voisinage de $x$ si 
$
exists epsilon > 0, Ioo(x-epsilon, x+epsilon) subset.eq V
$
On note $cal(V) (x)$ l'ensemble des voisinages de $x$.

#card("adh", "Adhérence", ("Maths.Analyse.Réels",))

Définition et propriétés de l'adhérence d'un ensemble.

#answer

Soit $A subset.eq RR$, $x in overline(RR)$, $x in RR$ est adhérent à $A$ si
$
  forall V in cal(V)(x), V inter A != emptyset
$
L'adhérence de $A$ est alors
$
  "adh"(A) &= {x in RR | x "adhérent à" A} \
  &= {x in RR | script(forall epsilon > 0\, #Ioo($x-epsilon$, $x+epsilon$) inter A != emptyset)}
$
Propriétés :
- $A subset.eq "adh"(A)$
- Si $A$ non vide borné : ${inf A, sup A} subset.eq A$
- $"adh"(Ioo(a,b)) = Icc(a,b)$
- $D$ est dense dans $RR$ ssi $"adh"(D) = RR$
- $"adh"("adh"(A)) = "adh"(A)$

#card("aritgeomsuit", "Suites arithmético-géometriques", ("Maths.Analyse.Suites Réelles",))

Formule explicite d'une suite arithmético-géometrique.

#answer

Soit $a, b in RR$ et $(u_n)$ une suite tel que
$
  forall n in NN, u_(n+1) = a u_n + b
$
On note $f(x) = a x + b$, on trouve le point fixe $w = b / (1 - a)$. Soit $v_n= u_n - w$.
$
  v_(n+1) &= a u_n + b - underbrace((a w + b), -w) \
  &= a(u_n - w) = a v_n \
  v_n &= a^n v_0 \
  u_n &= a^n (v_0 - w) + w
$

#card("record2", "Suites récurentes d'ordre 2", ("Maths.Analyse.Suites Réelles",))

Formule explicite d'une suite récurrente d'ordre 2.

#answer

Soit $a, b in RR$, $(u_n)$ une suite tel que
$
  u_(n+2) = a u_(n+1) + b u_n
$
On résout l'équation caractèristique 
$
x^2 = a x + b
$
- Deux racines $r_1, r_2$ #h(1fr)
  $
    u_n = lambda r_1^n + mu r_2^n
  $
- Racine double $r$
  $
    u_n = (lambda + mu n)r^n
  $
Avec $lambda, mu in RR$ déterminés par $u_0$ et $u_1$.

#card("carseq", "Caractèrisation séquentielle de l'adhérence", ("Maths.Analyse.Suites Réelles",))

Caractèrisation séquentielle de l'adhérence et la borne supérieure.

#answer

Soit $A subset.eq RR$.
- Si $(u_n)$ une suite à valeure dans $A$ et $u_n -> l$, alors $l in "adh"_overline(RR)(A)$.
- Si $x in "adh"_overline(RR)$, alors il existe $(u_n) in A^NN$ tel que $u_n -> x$.
Ainsi
$
  "adh"(A) \ = {x in RR | exists (u_n) in A^NN, u_n -> x}
$
Et $S = sup A$ existe si $A$ non vide majoré par $S$ et il existe $(u_n) in A^NN$ tel que $u_n -> S$.

#card("suitadj", "Suites adjacentes, emboitées", ("Maths.Analyse.Suites Réelles",))

Définition et théorème des suites adjacentes et emboitées.

#answer

- Adjacentes :

  Deux suites $(a_n)$ et $(b_n)$ sont adjacentes si
  $
  (a_n) arrow.tr, quad (b_n) arrow.br \ "et" lim_(n -> oo) (b_n - a_n) = 0
  $

  Théorème : $(a_n)$ et $(b_n)$ et $lim a_n = lim b_n$.

  Preuve : Théorème de la limite croissante pour la convergence.
- Emboitées :

  La même chose avec des segments.

  Théorème : 
  $
    inter.big_(n=0)^oo Icc(a_n, b_n) = {x} \ "avec" x = lim a_n = lim b_n
  $

#card("bolzweie", "Théorème de Bolzano-Weiestrass", ("Maths.Analyse.Suites Réelles",))

Théorème de Bolzano-Weiestrass et démonstration.

#answer

Toute suite réelle bornée admet une sous-suite convergente. Dans $RR^n$ (et $CC$), il suffit d'ếtre borné en norme ou module.

Preuve :

Soit $(u_n)$ une suite bornée par $a_0$ et $b_0$, notons $A = {u_n, n in NN}$. Par récurrence :
- Ini : $abs(Icc(a_0, b_0) inter A) = oo$
- Héré : On suppose $abs(Icc(a_n, b_n) inter A) = oo$, et on coupe en $m = (a_n + b_n) / 2$ :
  - Si $abs(Icc(a_n, m) inter A) = oo$, $cases(a_(n+1) = a_n, b_(n+1) = m)$ #v(8pt)
  - Si $abs(Icc(m, b_n) inter A) = oo$, $cases(a_(n+1) = m, b_(n+1) = b_n)$

Par le théorème des suites emboitées : 
$
exists l in Icc(a_0, b_0), space inter.big_(n = 0)^oo Icc(a_n, b_n) = {l}
$

Soit $phi$ une extractrice, par récurrence :
- Ini : $phi(0) = 0$
- Héré : $Icc(a_(n+1), b_(n+1))$ est infini, donc il existe $m > phi(n)$ tel que $u_m in Icc(a_(n+1), b_(n+1))$. On prend $phi(n+1) = m$.

Donc $a_n <= u_(phi(n)) <= b_n$ d'où $lim u_(phi(n)) = l$.

#card("cesaro", "Moyennes de Cesàro", ("Maths.Analyse.Suites Réelles",))

Définition, propriétés des moyennes de Cesàro.

#answer

Soit $(u_n)$ une suite. La suite des moyennes de Cesàro de $u_n$ est
$
  sigma_n = (a_1 + a_2 + dots.c + a_n) / n
$
Si $u_n -> l in overline(RR)$, alors $sigma_n -> l$.

Preuve : 
- $l$ fini : Découpage pour $n < N$ et $n >= N$ et inégalité triangulaire.
- $l$ infini : majoration.

#card("asympt", "Manipulations asymptotiques", ("Maths.Analyse.Suites Réelles",))

Manipulations asymptotiques élémentaires.

#answer

- $~$ : relation d'équivalence
  - produit, quotient, exposant
  - *pas* de somme, de composition, ...
- $o(1) <=> "tend vers" 0, O(1) <=> "borné"$
- $O$ et $o$ transitifs
- $O$ et $o$ mangent les constantes
- $u_n ~ v_n "ssi" u_n = v_n + o(v_n)$
- Si $u_n ~ v_n$ (ou $O, o$), alors $u_(phi(n)) ~ v_(phi(n))$ (ou $O, o$)
- $o$ et $~$ sont des cas particuliers de $O$.

#card("asyusu", "Comparaison asymptotiques usuelles", ("Maths.Analyse.Suites Réelles",))

Comparaison asymptotiques usuelles, stirling

#answer

Soit $k in RR_+^star, q > 1$, au voisinage de l'infini :
$
  n^k &= o(q^n) \
  q^n &= o(n!) \
  n! &~ sqrt(2 pi n) n^n / e^n \
  ln (n!) &~ n ln n \
  sum_(k = 1)^n 1/n &= ln n + gamma + o(1)
$

#card("lipschitz", "Fonctions K-Lipschitziennes", ("Maths.Analyse.Continuité",))

Qu'est qu'une fonction $K$-lipschitzienne

#answer

Une fonction $f: A -> RR$ est $K$-lipschitzienne si
$
  forall x,y in A, abs(f(x) - f(y)) <= K abs(x - y)
$
Lipschitz sur un segment implique uniformement continue.

#card("bornes", "Théorème des bornes atteintes", ("Maths.Analyse.Continuité",))

Théorème des bornes atteintes et démonstration.

#answer

Si $f$ est $C^0 (Icc(a, b))$, alors $f$ est bornée et atteint ses bornes.

Preuve :

Notons $M = sup f$, quitte à avoir $M in overline(RR)$. $M in "adh"_overline(RR)(f(Icc(a, b)))$, donc il existe une suite $(x_n)$ à valeur dans $Icc(a, b)$ tel que $f(x_n) -> M$.

Par Bolzano-Weiestrass, il existe $phi$ tel que $x_(phi(n)) -> l$ avec $l in Icc(a, b)$ et donc nécéssairement $M in RR$.

#card("heine", "Théorème de Heine", ("Maths.Analyse.Continuité",))

Énoncé et démonstration du théorème de Heine.

#answer

Toute fonction continue sur un segment est uniformement continue.

Preuve :

Soit $f in C^0(Icc(a,b))$. Supposons par l'absurde que $f$ n'est pas uniformement continue.

$
  exists epsilon > 0, forall delta > 0, exists x, y in Icc(a,b) \
  |x - y| < delta "et" |f(x) - f(y)| >= epsilon
$
 
On prend $(x_n), (y_n) in Icc(a,b)^NN$ tel que 
$
forall n in NN, |x_n - y_n| < 1/n \
|f(x_n) - f(y_n)| >= epsilon
$
Ces suites sont bornées donc par Bolzano-Weiestrass, il existe une extractrice $phi$ tel que $x_(phi(n)) -> l in Icc(a, b)$.

Or $|x_(phi(n)) - y_(phi(n))| -> 0$ donc $y_(phi(n)) -> l$. 

Mais par continuité de $f$, 
$
lim_(n->oo) f(x_(phi(n))) &= lim_(n->oo) f(y_(phi(n))) \ &= f(l)
$

Donc il existe $N in NN$ tel que 
$
|f(x_phi(n)) - f(y_(phi(n)))| < epsilon
$
Qui est absurde.

#card("trigorec", "Fonctions trigonometriques réciproques", ("Maths.Analyse.Dérivation",))

Domaine de définition et dérivées des fonctions trigonometrique réciproques.

#answer

$
  mat(delim: #none,
    arccos,:,Icc(-1, 1),->,Icc(0, pi);
    arccos',:,Ioo(-1, 1),->,Ico(-1,-oo);
    ,,x,|->,-1/sqrt(1 - x^2);;
    arcsin,:,Icc(-1,1),->,Icc(-pi/2,pi/2);
    arcsin',:,Ioo(-1,1),->,Ico(1,+oo);
    ,,x,|->,1/sqrt(1 - x^2);;
    arctan,:,RR,->,Ioo(-pi/2, pi/2);
    arctan',:,RR,->,Ioc(0,1);
    ,,x,|->, 1 / (1+x^2)
  )
$

#card("extrloc", "Propriété des extrémum locaux", ("Maths.Analyse.Dérivation",))

Que peut on dire si $f : I -> RR$ et dérivable et admet un extrémum local en $a in I\\{inf I, sup I}$.

#answer

Soit $f : I -> RR$ dérivable qui admet un extrémum local en $a$, un point intérieur à $I$, alors $f'(a) = 0$.

Preuve : par hypothèse, pour un maximum (un minimum se traite de même)
$
exists V in cal(V)(a), forall x in V, f(x) <= f(a)
$
Étudions
$
lim_(x -> a) (f(x) - f(a)) / (x - a)
$
#pad(x: 0.5em, grid(columns: (1fr, 1fr),
[
Si $x < a$ : #h(1fr)
  $
    overbrace(f(x) - f(a), <= 0) / underbrace(x - a, < 0) >= 0
  $
],[
Si $x > a$ :
  $
    overbrace(f(x) - f(a), <= 0) / underbrace(x - a, > 0) <= 0
  $
]))
Donc $f'(a) = 0$ (les deux limites sont égales par la dérivabilité de $f$ en $a$).

#card("rolletaf", "Théorème de Rolle, théorème des acroissements finis", ("Maths.Analyse.Dérivation",))

Énoncé et preuve des théorèmes de Rolle et des acroissements finis.

#answer
Soit $f in C^0(Icc(a,b))$ dérivable sur $Ioo(a,b)$ 

/ Rolle: Si $f(a) = f(b)$, alors 
  $
  exists c in Ioo(a,b), space f'(c) = 0
  $
/ TAF:
  $
  exists c in Ioo(a,b), space f'(c) = (f(b) - f(a)) / (b - a)
  $

Preuve :
- Rolle : théorème des bornes atteintes, propriétés des extrémum locaux avec une disjonction de cas si les extrémums sont aux bornes.
- TAF : Rolle en pente, on corrige par la pente pour se ramener à Rolle.

#card("inegacrlag", "Inégalité des acroissements finis et de Taylor-Lagrange", ("Maths.Analyse.Dérivation",))

Inégalité des acroissements finis et de Taylor-Lagrange.

#answer

/ Inégalité des acroissements finis: #linebreak()
  Soit $f : I -> RR$ dérivable et $a in I$, pour tout $x in I$
$
  abs(f(x) - f(a)) <= sup_Icc(a,x) abs(f') dot abs(x - a)
$
/ Inégalité de Taylor-Lagrange: #linebreak()
  Soit $f : I -> RR$ qui est $D^(n+1)$ et $a in I$, pour tout $x in I$
$
abs(f(x) - sum_(k = 0)^n f^((k))(a) (x - a)^k / k!)\ <= sup_Icc(a,x) abs(f^((n+1))) dot abs(x - a)^(n+1) / (n+1)!
$

Preuve :

On prend les théorème et on majore le paramètre.

#card("intrecpol", "Intégration de l'inverse d'un trinôme", ("Maths.Analyse.Intégration",))

Méthode d'intégration pour l'inverse d'un trinôme du second degré.

#answer

On prend $a x^2 + b x + c$ un trinôme du second degré, on vas intégrer $1 / (a x^2 + b x + c)$.

- $Delta > 0$ : décomposition en éléments simples
- $Delta = 0$ : 
  $
    integral (dif x) / (a x^2 + b x + c) &= integral (dif x) / (a(x - r)^2) \
    &= - 1 /(a(x - r))
  $
- $Delta < 0$ : on passe à la forme cannonique
  $
    a x^2 + b x + c \ = a [(x + b/(2 a))^2 + abs(Delta) / (4 a^2)]
  $
  Et on se ramène à $integral (dif u) / (u^2 + 1) = arctan u$.
  $
    integral 1 / (a x^2 + b x + c) \ = 2 / sqrt(abs(Delta)) arctan( (2 a x + b) / sqrt(abs(Delta)))
  $

#card("dls", "Développements limités", ("Maths.Analyse.Développements Limités",))

#grid(columns: (1fr,)*2,
$
  1/(1 - x) = space ? \
  1/(1 + x) = space ? \
  ln(1 + x) = space ? \
  e^x = space ? \
  e^(-x) = space ? \
  cos(x) = space ? \
  sin(x) = space ? \
$,
$
  "ch"(x) = space ? \
  "sh"(x) = space ? \
  (1 + x)^alpha = space ? \
  1 / (sqrt(1 - x^2)) = space ? \
  arcsin(x) = space ? \
  arccos(x) = space ? \
  arctan(x) = space ? \
$
)
#v(-0.5em)
$
  tan(x) = space ?
$

#answer
$

  1/(1 - x) &= 1 + x + x^2 + o(x^2) \
  &= sum_(k = 0)^n x^k + o(x^n) \
  1/(1 + x) &= 1 - x + x^2 + o(x^2) \
  &= sum_(k = 0)^n (-x)^k + o(x^n) \
  ln(1 + x) &= x - x^2 / 2 + x^3 / 3 + o(x^3) \
  &= sum_(k = 0)^n (-x)^(k+1) / (k+1) + o(x^n) \
  e^x &= 1 + x + x^2 / 2 + x^3/6 + o(x^3) \
  &= sum_(k = 0)^n x^k / k! + o(x^n) \
  e^(-x) &= 1 - x + x^2 / 2 - x^3/6 + o(x^3) \
  &= sum_(k = 0)^n (-x)^k / k! + o(x^n) \
  cos(x) &= 1 - x^2 / 2 + x^4 / 24 + o(x^5) \
  &= sum_(k=0)^n (-1)^k x^(2k) / (2k)! + o(x^(2k)) \
  sin(x) &= x - x^3 / 6 + x^5 / 120 + o(x^6) \
  &= sum_(k=0)^n inline(((-1)^k x^(2k+1)) / (2k+1)!) + o(x^(2k+1)) \
  "ch"(x) &= 1 + x^2 / 2 + x^4 / 24 + o(x^5) \
  &= sum_(k=0)^n x^(2k) / (2k)! + o(x^(2k)) \
  "sh"(x) &= x + x^3 / 6 + x^5 / 120 + o(x^6) \
  &= sum_(k=0)^n (x^(2k+1)) / (2k+1)! + o(x^(2k+1)) \
  (1 + x)^alpha &= inline(1 + alpha x + alpha(alpha - 1) / 2 x^2 + o(x^2)) \
  &= sum_(k=1)^n x^k/k! display(product_(p = 0)^(k - 1) (alpha - p)) + o(x^n) \
  1 / (sqrt(1 - x^2)) &= 1 + 1/2 x^2 + 3/8 x^4 + o(x^4)  \
  &= sum_(k=1)^n 1/(2^(2k)) vec(2k, k) x^(2k) + o(x^(2k)) \
  script(arcsin(x)) &= x + 1/2 x^3 / 3 + 3/8 x^5/5 + o(x^5) \
  &= sum_(k=1)^n inline((vec(2k, k) x^(2k+1))/(2^(2k)(2k+1))) + o(x^(2n+1)) \
  script(arccos(x)) &= -x - 1/2 x^3 / 3 - 3/8 x^5/5 + o(x^5) \
  &= sum_(k=1)^n inline(- (vec(2k, k) x^(2k+1))/(2^(2k)(2k+1)) + o(x^(2n+1))) \
  script(arctan(x)) &= x - x^3 / 3 + x^5/5 + o(x^5) \
  &= sum_(k=1)^n inline(((-1)^k x^(2k+1)) / (2k+1)) + o(x^(2n+1)) \
  script(tan(x)) &= script(x + 1/3 x^3 + 2/15 x^5 + 17/315 x^7 + o(x^8)) \
$

#card("etudl", "Étude local et asymptotique de fonctions", ("Maths.Analyse.Développements Limités",))

Méthode pour étudié le comportement local et asymptotique d'une fonction.

#answer

/ Local: au voisinage de $a in RR$
  - Équivalent en $a$ : premier terme
  - Tangente en $a$ : $"DL"_1(a)$
  - Signe de $f$ en $a$ : premier terme non nul.
  - Position relative par rapport à la tangente : signe du premier terme non nul après l'ordre $1$.
/ Asymptotique: au voisinage de $plus.minus oo$
  - Asymptote oblique : $"DL"_1(plus.minus oo)$
  - Position relative : signe du terme suivant.

Rappelle :

$f$ admet une asymptote oblique d'équation $a x + b$ si 
$
lim_(x -> plus.minus oo) f(x) - a x - b = 0
$

#card("suitrec", "Suites récurrentes", ("Maths.Analyse.Suites Réelles",))

Méthode pour les suites récurrentes de la forme $u_(n+1) = f(u_n)$.

#answer

Soit $f$ une fonction et $(u_n) in RR^NN$ tel que $u_(n+1) = f(u_n)$.

+ Intervalle stable : on cherche $I$ tel que $f(I) subset.eq I$.
+ Variations de $(u_n)$
  - Signe de $f(x) - x$ sur $I$
    - $+$ : $(u_n)$ est croissante
    - $-$ : $(u_n)$ est décroissante
    - Sinon affiner $I$
  - Monotonie de $f$
    - Si $f$ est croissante sur $I$, $(u_n)$ est monotone
    - Si $f$ est décroissante sur $I$, $(u_(2n))$ et $(u_(2n+1))$ sont monotone.
+ On montre l'éxistence de la limite (limite croissante)
+ On la détermine : il s'agit de l'un des points fixes de $I$ (idéalement il n'y en a qu'un).
  
  Dans le cas des fonctions décroissantes, on cherche les limites des deux sous-suites, points fixes de $f compose f$.

#card("conv", "Propriétés de convexité", ("Maths.Analyse.Convexité",))

Définition et propriétés de convexité.

#answer

Soit $f : I -> RR$, $f$ est dite convexe si 
$
forall x, y in I, forall lambda in Icc(0, 1) \ f(lambda x + (1 - lambda) y) \ <= lambda f(x) + (1-lambda) f(y)
$

Propriétés :
- Soit $f : I -> RR$ convexe, $forall x_1, dots, x_n in I$
  $
  forall lambda_1, dots, lambda_n in Icc(0, 1), lambda_1 + dots.c + lambda_n = 1 =>\
  f(sum_(i = 1)^n lambda_i x_i) <= sum_(i = 1)^n lambda_i f(x_i)
  $
- Soit $Phi$ convexe, $forall f in C^0(Icc(a,b))$
  $
    Phi(1/(b-a) integral_a^b f(x) dif x) \ <= 1/(b-a) integral_a^b Phi (f(x)) dif x
  $
- Soit $f : I -> RR$, $a in I$, on note
  $
    mat(delim: #none, tau_a,:, I\\{a},->,RR;,,x,|->,(f(x) - f(a)) / (x - a))
  $
  les taux d'acroissements en $a$ de $f$.

  $f$ est convexe ssi $forall a in I, tau_a$ est croissante.
- Soit $f : I -> RR$, on appelle droite d'appuis en $x_0$ de $f$ une droite $y = a x + b$ tel que
  - $forall x in I, a x + b <= f(x)$ \
  - $f(x_0) = a x_0 + b$
  Si $f$ convexe, $f$ admet des droites d'appuis en tout points.

#card("invmat", "Théorème de caractérisation des matrices inversibles", ("Maths.Algèbre.Matrices",))

Énoncé du théorème de caractérisation des matrices inversibles.

#answer

Soit $A in M_n (RR)$, les assertions suivantes sont équivalentes :
- $A$ est inversible.
- $A attach(t: L, ~) I_n$.
- $"rg" A = n$.
- Le système homogène $A X = 0$ admet une seule solution.
- $forall Y in RR^n$ le système homogène $A X = Y$ admet au plus une solution.
- $forall Y in RR^n$ le système homogène $A X = Y$ admet au moins une solution.

#card("assoc", "Polynômes associés", ("Maths.Algèbre.Polynômes",))

Définition et propriétés des polynômes associés.

#answer

Soit $P, Q in KK[X]$, $P$ et $Q$ sont dit associé si $P | Q$ et $Q | P$.

$P, Q$ sont associés ssi $exists lambda in KK^star, A = lambda B$. Toute class de polynômes associés contient un unique polynôme unitaire (à l'exception de ${0}$).

#card("porpracines", "Propriétés des racines d'un polynôme", ("Maths.Algèbre.Polynômes",))

Propriétés des racines d'un polynôme.

#answer

Soit $P in KK[X]$, $n = deg P$

*En général*
+ Si $P != 0$, $P$ à au plus $n$ racines (comptées avec multiplicités).
+ L'unique polynôme qui à une infinité de racines est $P = 0$.
+ Si $Q in KK_n [X]$ et $exists alpha_1, dots, alpha_(n+1) in KK$ tels que $forall k in [|1, n+1|], P(alpha_k) = Q(alpha_k)$, alors $P = Q$.

*En caractèristique nulle*
4. $a in KK$ est racine de $P$ avec multiplicité $m$ ssi 
  $
  forall k in [|0, m - 1|], P^((k))(a) = 0 \
  "et" P^((m)) (a) != 0
  $

*Démonstration*

+ Si $alpha_1, dots, alpha_N in KK$ sont des  racines distinctes de $P$, et $m_1, dots, m_N in NN^*$ leurs multiplicités. #h(1fr)

  Pour tout $k in [|1, N|], (X - alpha_k)^(m_k) | P$

  Or pour $i < j in [|1, n|]$
  $
    (X - alpha_i) - (X - alpha_j) = alpha_j - alpha_i
  $
  Relation de Bézout ($alpha_j - alpha_i$ associé à $1$) donc premiers entre eux deux à deux.

  D'où $product_(k in 1)^N (X - alpha_k)^(m_k) | P$ et $n >= sum_(k = 1)^N m_k$.

+ Par la propriétés précedente, si $P$ à une infinité de racine distincte il ne peut être de degré positif (ou il serait infini) donc il est nul.

4. Par Taylor-Langrange formel, pour tout $j in [|1, m-1|]$

  $
    P &= underbrace(sum_(k = 0)^(j - 1) P^((k)) (a) (X - a)^k / k!, R_j (X) space (deg < j)) \ &+ underbrace(sum_(k = j)^(n) P^((k)) (a) (X - a)^k / k!, (X - a)^j Q(X))  \
  $

  D'où $R_j$ le reste de la division euclidienne de $P$ par $(X - a)^j$. Or $a$ est une racine de multiplicité $m$ ssi

  $
    cases(R_m = 0, R_(m+1) != 0)  \
  <=> cases(forall k in [|0\, m - 1|]\, (P^((k)) (a)) / k! = 0, exists k in [|0\, m|]\, (P^((k)) (a)) / k! != 0 ) \
  <=> cases(forall k in [|0\, m - 1|]\, (P^((k)) (a)) = 0, P^((m)) (a) != 0 ) \
  $

#card("multrac", "Multiplicité d'une racine", ("Maths.Algèbre.Polynômes",))

Définition de multiplicité d'une racine.

#answer

Soit $P in KK[X], alpha in KK$ une racine et $n in NN^star$. On dit que $alpha$ est de multiplicité $n$ si (l'un ou l'autre) :
- $(X - alpha)^n | P$ mais $(X - alpha)^(n+1) divides.not P$.
- $forall k in [|0, n-1|], P^((k)) (alpha) = 0$

#card("scinde", "Polynômes scindés", ("Maths.Algèbre.Polynômes",))

Définition et propriétés des polynôme scindés.

#answer

Soit $P in KK[X]$, $alpha_1, dots, alpha_k$ ses racines et $m_1, dots, m_k$ leur multiplicités. 
- $P$ est scindé si $deg P = sum_(i = 1)^k m_k$.
- $P$ est scindé racines simples si $P$ scindé et $forall i in [|1, k|], m_i = 1$.

Propriétés :
- Si $P$ est scindé racines simples sur $RR$, $P'$ aussi.
- Si $P$ est scindé sur $RR$, $P'$ aussi.
- Tout polynôme $P$ est scindé sur $CC$ : théorème de Gauss-d'Alembert.

#card("irred", "Polynômes irréductibles", ("Maths.Algèbre.Polynômes",))

Définition et propriétés des polynômes irréductibles.

#answer

Soit $P in KK[X]$, $P$ est dit irréductible si ses seuls diviseurs sont $P$, $1$ et leurs associés.

+ Dans $CC$, les polynômes irréductibles sont les monômes (théorème de Gauss-d'Alembert).
+ Dans $RR$, les polynômes irréductibles sont les monômes et les polŷnomes de degré $2$ avec $Delta < 0$.
+ En général, un polynôme de degré $1$ est toujours irréductible.
+ Dans $KK[X]$, un polynôme de degré $2$ ou $3$ est irréductible ssi il n'admet pas de racine dans $KK$.
+ Dans $KK[X]$, un polynôme de degré $>= 2$ ne peut être irréductible s'il admet une racine dans $KK$.
+ ($"car"(KK) = 0$) Un polynôme $P in KK[X] subset LL[X]$ irréductible ($LL$ extension de corps de $KK$) n'admet que des racines simples dans $LL$ (et à fortiori dans $KK$).

*Démonstration*

2. Par les propriétés 3 et 4, on sait que ces polynômes sont irréductibles, montrons que ce sont les seuls.

  Soit $P in RR[X]$ irréductible de degré $>= 2$.

  $P in CC[X]$ donc on dispose de $lambda in CC\\RR$ racine de $P$.

  $
    P(overline(lambda))   = overline(P)(overline(lambda)) = overline(P(lambda)) = 0
  $

  D'où (car $(X - lambda) and (X - overline(lambda)) = 1$)
  $
    Q = underbrace(X^2 - 2 Re(lambda) X + |lambda|^2, in RR[X]) | P
  $

  Comme $P$ est irréductible, $P$ et $Q$ sont associés et $deg P = 2$.

4. Soit $P in KK_3 [X] \\ KK_1 [X]$
  - S'il est irréductible il n'admet pas de racine.
  - S'il n'est pas irréductible, #h(1fr)
    $
    P = Q R
    $ 
    - Soit $deg Q = 1, Q = X - alpha$ et $alpha$ racine de $P$.
    - Soit $deg R = 1, R = X - beta$ et $beta$ racine de $P$.

6. $0 <= deg P' <= deg P - 1$ et par irréductibilité de $P$ dans $KK[X]$

  $
    P and P' = 1
  $

  Or le PGCD se conserve sur les extensions de corps, ils n'ont donc pas de racine communes (dans $KK$ et $LL$).

#card("fnsymrac", "Fonctions symétriques des racines", ("Maths.Algèbre.Polynômes",))

Définition des fonctions symétriques des racines et formules de Viete.

#answer

Soit $alpha_1, dots, alpha_k in CC$ et $k in [|0, n|]$, la $k$-ème fonction symétrique des élémentaire de $alpha_1, dots, alpha_n$ est
$
  sigma_k = sum_(1 <= i_1 < dots.c < i_k <= n) product_(j = 1)^k alpha_(i_j)
$
On remarque que $sigma_0 = 1$.

Soit $P = a_0 + a_1 X + dots.c + a_n X^n$ scindé, on note $alpha_1, dots, alpha_n$ ses racines (non distinctes).

Formule de Viete :
$
  forall k in [|0, n|], sigma_k = (-1)^k a_(n-k) / a_n
$

#card("tcheb", "Polynômes de Tchebycheff", ("Maths.Algèbre.Polynômes",))

Définition et propriétés des polynômes de Tchebycheff.

#answer

Le $n$-ème polynôme de Tchebycheff est le polynôme tel que 
$
  forall theta in RR, T_n (cos theta) = cos(n theta)
$

Propriétés :
+ Formule de récurrence : #h(1fr)
  $
    T_(n+1) + T_(n-1) = 2 X T_n
  $
+ $deg T_n = n$, coéfficient dominant : $2^(n-1)$, sauf pour $n = 0$, $T_0 = 1$.
+ $T_n$ est scindé racines simples sur $RR$ :
  $
    T_n (X) \ = 2^(n-1) product_(k = 0)^(n-1) (X - cos ((2k+1) pi) / (2n))
  $
+ Orthogonalité : si $n != p$
  $
    integral_(-1)^1 T_n (x) T_p (x) (dif x) / sqrt(1 - x^2) = 0
  $
+ Minimalité en norme :
  $
    norm(P) = max_(t in Icc(-1, 1)) abs(P (t))
  $
  Si $P$ unitaire de degré $n$, alors $norm(P) >= 1 / (2^(n-1))$.

  Avec cas d'égalité si $P(X) = (T_n (X)) / (2^(n-1))$

Preuves :
+ Formules de trigonométrie : #h(1fr)
  $
  script(cos((n+1)theta) + cos((n-1)theta) = 2 cos theta cos(n theta)) \
  script(T_(n+1) (cos theta) + T_(n-1) (cos theta) = 2 (cos theta) T_(n) (cos theta))
  $
  Donc ils coincident en une infinité de valeurs $Icc(-1, 1)$, et sont donc égaux.
+ Par récurrence avec la relation de récurrence.
+ On résout $cos(n theta) = 0$, on fait attention à distingué les racines.
+ Changement de variable $x = cos theta$, puis formules de trigonométrie.
+ Par contraposé : On prend $P$ unitare de degré $n$ tel que $norm(P) <= 1 / (2^(n-1))$.
  - $P = 1/(2^(n-1)) T_n + Q, quad deg Q <= n - 1$.
  - On regarde les $y_k$ quand $T_n (y_k) = plus.minus 1$.
  - On en déduis le signe de $Q$
  - Par le TVI $Q$ à $n$ racines donc $Q = 0$.
  - Donc $P(X) = (T_n (X)) / (2^(n-1))$.

#card("fracrat", "Propriétés des fractions rationelles", ("Maths.Algèbre.Polynômes",))

Propriétés des fractions rationelles

#answer

- Si on dit que $P / Q$ est scindé, c'est que $Q$ est scindé.
- Si $F$ admet une infinité de racines alors $F = 0$.
- Si $F$ et $G$ coincident en une infinité de points alors $F = G$.

#card("decompels", "Décomposition en éléments simples", ("Maths.Algèbre.Polynômes",))

Formules, propriétés de la décomposition en éléments simples.

#answer

Soit $F in KK(X)$, $F$ se décompose de façon uniqe sous la forme
$
  F = E + G "avec" E in KK[X] "et" deg G < 0
$
On appelle $E$ la partie entière de $F$ et $G$ la partie pôlaire.

- Si $F = P / Q$ sindé racines simples : soit $alpha_1, dots, alpha_n$ les pôles et $Q(X) = (X - alpha_k) R_k (X)$ pour tout $k in [|1, n|]$ : #h(1fr)
  $
    F = E + lambda_1 / (X - alpha_1) + dots.c + lambda_n / (X - alpha_n)
  $
  Avec
  $
    lambda_k = P(alpha) / (R_k (alpha)) = P(alpha) / (Q'(alpha))
  $
- Si $F$ est scindé pôles multiples, on fait la même chose en retranchant les décompositions à chaques fois.

Décomposition en éléments simples de $P' / P$ :

$
  P(X) = lambda (X - alpha_1)^(m_1) dots dots.c dot (X - alpha_k)^(m_k) \
  (P'(X)) / (P(X)) =  m_1 / (X - alpha_1) + dots.c + m_k / (X - alpha_k)
$

#card("axesp", "Axiomes d'un espace vectoriel", ("Maths.Algèbre.Espaces Vectoriels",))

Axiomes d'un espace vectoriel.

#answer

Sois $KK$ un corps, $E$ muni de la somme interne $+$ et du produit externe $dot$ est un $KK$-ev si
+ $(E, +)$ est un groupe abélien.
+ $forall x in E, 1 dot x = x$.
+ $forall lambda in KK, forall x, y in E, lambda (x + y) = lambda x + lambda y$.
+ $forall lambda, mu in KK, forall x in E, (lambda + mu) x = lambda x + mu x$.
+ $forall lambda, mu in KK, forall x in E, lambda (mu x) = (lambda mu) x$

#card("ran", "Théorème de caractérisation du rang", ("Maths.Algèbre.Espaces Vectoriels",))

Énoncé du théorème de caractérisation du rang.

#answer

Soit $A in M_(n p)(KK), r in NN$, les assertions suivantes sont équivalentes
- $A$ équivalente par ligne à une matrice échelonné avec $r$ lignes non nulles.
- $"rg" phi_A = r$ \
- $"rg" (C_1, dots, C_p) = r$ (avec $C_i$ la $i$-ème colonne de $A$)
- $"rg" (L_1, dots, L_n) = r$ (avec $L_i$ la $i$-ème ligne de $A$)
- $A attach(t: sscript(L\,C), ~) J_r$
On dit alors que $"rg" A = r$.

On a aussi
- $A attach(t: sscript(L\,C), ~) B$ ssi $"rg" A = "rg" B$ #h(1fr)
- $"rg"(phi compose psi) <= min("rg" phi, "rg" psi)$

#card("forml", "Formes lineaires et hyperplans", ("Maths.Algèbre.Espaces Vectoriels",))

Formes lineaires et hyperplans.

#answer

Soit $E$ un $KK$-ev de dimension finie.
- Si $alpha in E^star\\{0}$, alors $ker alpha$ est un hyperplan.
- Si $H$ est un hyperplan de $E$, il existe une forme linéaire $alpha$ unique à constante multiplicative prés tel que $H = ker alpha$.

#card("semb", "Matrices sembables", ("Maths.Algèbre.Matrices",))

Définition de matrices sembables.

#answer

Soit $A, B in M_n(KK)$, $A$ est dite sembable à $B$ si
$
  exists P in "GL"_n (KK), space B = P^(-1) A P
$
Invariants :
- $"rg" A = "rg" B$
- $tr A = tr B$
- $det A = det B$
- $chi_A = chi_B$
- $mu_A = mu_B$

#card("propbaseseries", "Propriétés élémentaires sur les séries", ("Maths.Analyse.Séries",))

Propriétés élémentaires sur les séries.

#answer

- Soit $(u_n) in KK^NN$ et $S_n = sum_(k=0)^n u_n$, on dit que $sum u_n$ converge si $(S_n)$ converge.
- Si $sum u_n$ converge alors 
  $
  (u_n) tends(n -> +oo) 0
  $
- La suite $(u_n)$ converge ssi la série $sum (u_(n+1) - u_n)$ converge.
- L'ensemble $cal(S)$ des séries convergentes est un sev de l'espace des suites, et l'application
  $
    mat(delim: #none, phi : , cal(S), ->, KK;, (u_n), |->, sum_(n = 0)^(+oo) u_n)
  $
  est linéaire.
- Si $(u_n) in RR_+^NN$ alors $sum u_n$ converge ssi $(S_n)$ est majoré (théorème de la limite monotone).

#card("thcmpserpos", "Théorème de comparaison des séries positives", ("Maths.Analyse.Séries",))

Énoncé et démonstration du théorème de comparaison des séries positives.

#answer

Soient $(u_n), (v_n) in RR_+^NN$ alors

+ Si $forall n >= n_0, u_n <= v_n$ et $sum v_n$ converge alors $sum u_n$ converge.
+ Si $u_n = O_(n -> +oo) (v_n)$ et $sum v_n$ converge alors $sum u_n$ converge.
+ Si $u_n eqv(n -> +oo) v_n$ alors $sum u_n$ converge ssi $sum v_n$ converge.

Démonstration :

+ $(S_n)$ est majoré par $(accent(S, ~)_n)$ qui est fini.
+ $(S_n)$ est majoré par $M dot accent(S, ~)_n$ qui est fini.
+ $u_n ~ v_n$ implique $u_n = O(v_n)$ et $v_n = O(u_n)$.

#card("cmpserint", "Comparaison série intégrale", ("Maths.Analyse.Séries", "Maths.Analyse.Intégration"))

Propriétés et methode de comparaison série intégrale.

#answer

Pour $f in C_("pm")^0 (Ico(a, +oo), RR_+)$, décroissante, $forall n >= ceil(a) + 1 = N_0$

$
  f(n) &>= integral_n^(n+1) f(t) dif t \
&<= integral_(n-1)^n f(t) dif t
$

D'où

$
  sum_(n = N_0)^N f(n) &>= integral_(N_0)^(N+1) f(t) dif t \
&<= integral_(N_0-1)^N f(t) dif t
$

Ainsi $sum f(n)$ converge ssi $integral_(N_0)^(+oo) f$ converge.

Et de plus (à redémontrer) :
$
  sum (integral_(n-1)^n f(t) dif t - f(n)) \
  sum (f(n) - integral_n^(n+1) f(t) dif t) \
$
sont à terme général positif et convergent car

$
  f(n) <= integral_(n-1)^n f <= f(n +1) \

  0 <= integral_(n-1)^n f - f(n) <= f(n +1) - f(n) \
$

Et $sum f(n+1) - f(n) $ est positive et converge (série téléscopique) car $f$ converge (positive et décroissante).

*Dans le cas $f$ non monotone* :

Si $f in C^1$ et $integral_n^(+oo) |f'|$ converge

$
  integral_k^(k+1) f &= underbrace([(t - k -1) f(t)]_k^(k+1), f(k)) \
&- integral_k^(k+1) (t-k-1) f'(t) dif t \
  integral_1^(N+1) f &= sum_(k=1)^N f(k) \ &+ sum_(k=1)^N integral_k^(k+1) (k+1-t)f'(t) dif t
$

Or pour tout $k >= 1$

$
  abs(integral_k^(k+1) (k + 1 - t)f'(t) dif t) <= integral_k^(k+1) |f'|
$

Qui est le terme général d'une série convergente d'où

$
 & sum f(n) & "converge" \ "ssi" & (integral_1^N f)_N & "converge" \ "ssi" & integral_1^(+oo) f & "converge"
$

#card("serbertrand", "Séries de Bertrand", ("Maths.Analyse.Séries",))

Définitions et propriétés des séries de Bertrand.

#answer

Soit $alpha, beta in RR$, la série $sum 1 / (n^alpha (ln n)^beta)$ est appelée série de Bertrand.

Cette série converge ssi $alpha > 1$ ou $alpha = 1$ et $beta > 1$.

Démonstration :
- Cas $alpha > 1$ comparaison avec les series de Riemann, en prenant $gamma in Ioo(1, alpha)$.
- Cas $alpha < 1$ même chose avec $gamma in Ioc(alpha, 1)$.
- Cas $alpha = 1$, comparaison série intégrale avec $t |-> 1 / (t (ln t)^beta)$.

#card("recheqsuit", "Recherche d'équivalent d'une suite", ("Maths.Analyse",))

Méthodes de recherche d'équivalents.

#answer

Si on cherche un équivalent d'une suite $(u_n)$

- Étudier la série $sum (u_(n+1) - u_n)$ ou $sum (u_n - u_(n + 1))$, sommes partielles ou restes (voir théorème de sommation des relations de comparaison).
- Chercher $alpha in RR^*$ tel que $u_(n+1)^alpha - u_n^alpha tends(n -> +oo) l in RR^*$, pour avoir
  $
    u_n^alpha - u_0^alpha &= sum_(k=0)^(n-1) u_(k+1)^alpha - u_k^alpha eqv(n->+oo) n l \
  $

#card("abscv", "Absolue convergence", ("Maths.Analyse.Séries",))

Définitions et démonstration du théorème de l'absolue convergence d'une série.

#answer

Une série $sum u_n$ (dans $RR$ ou $CC$) est dite absoluement convergente si $sum |u_n|$ converge. Si $sum u_n$ est absoluement convergente, alors elle est convergente.

Démonstration : on étudie $((u_n)_+)$ et $((u_n)_-)$ pour le cas réel, puis $("Re"(u_n))$ et $("Im"(u_n))$ pour le cas imaginaire, à chaque fois on majore par le module et on applique les thorème de comparaison des séries positives.

#card("thseralt", "Théorème des séries alternées", ("Maths.Analyse.Séries",))

Énoncer et démonstration du théorème des séries alternées.

#answer

Si $(u_n) in RR_+^NN$ décroissante tel que $u_n tends(n -> +oo) 0$, alors $sum u_n$ converge et $R_n = sum_(k = n+1)^(+oo) = S - S_n$ est du signe du premier terme et $abs(R_n) <= abs(u_(n+1))$.

Démonstration : on montre que les suites $S_(2n)$ et $S_(2n +1)$ sont adjacentes et on étudie $R_(2n)$ et $R_(2n+1)$.

#card("abel", "Transformation d'Abel", ("Maths.Analyse.Séries",))

Définition et applications de la transformation d'Abel.

#answer

Il s'agit d'une sorte d'IPP sur les séries. Soit $(a_n)$ et $(b_n)$ deux suites, la transformation d'Abel est utile si on a des hypothèses sur $S_n = sum_(k = 0)^n a_k$. On pose $S_(-1) = 0$.

$
  sum_(k = 0)^n a_k b_k &= sum_(k=0)^n (S_k - S_(k-1)) b_k \
&= sum_(k = 0)^n S_k b_k - sum_(k=0)^n S_(k-1) b_k \
&= S_n b_n - sum_(k = 0)^(n-1) S_k (b_(k+1) - b_k)
$

Applications :

$
  sum sin(n theta) / n^alpha \
sum cos(n theta) / n^alpha \
sum e^(i n theta) / n^alpha \
$

Remarque : on peut aussi écrire $a_k = R_(k-1) - R_k$, qui peut être intérressant si $sum a_n$ converge.

#card("raabduchamel", "Règle de Raabe-Duhamel", ("Maths.Analyse.Séries",))

Énoncé et démonstration de la règle de Raab-Duchamel.

#answer

Soit $(a_n) in (RR_+^*)^NN, a_(n+1)/a_n tends(n -> +oo) 1$ et
$
  a_(n+1) / a_n = 1 - alpha / n + O_(n->+oo)(1/n^(1+h)), quad h > 0
$

On considère $n^alpha a_n = u_n$, on veut montrer que $u_n tends(n -> +oo) l in RR_+^*$, c'est dire que $(ln(u_n))$ a une limite réelle. On étudie $sum ln(u_(n+1)) - ln(u_n)$.

$
  ln(u_(n+1)) - ln(u_n) = ln(a_(n+1) / a_n) + alpha ln((n + 1) / n) \
= ln(1 - alpha / n + O(1/n^(1+h))) + alpha ln (1 + 1/n) \
= alpha / n - alpha / n + O(1 / n^(1 + h)) + O(1 / n^2) \
= O(1/n^min(2, 1 + h))
$

Donc par le théorème de comparaison des séries à terme positifs (en valeur absolue) $sum ln(u_(n+1)) - ln(u_n)$ converge,  d'où $(u_n)$ converge.

Ainsi $n^alpha a_n tends(n -> +oo) e^l$, donc $a_n ~ e^l / n^alpha$, $sum a_n$ converge ssi $alpha > 1$.

#card("thsomrelser", "Théorème de sommation des relations de comparaison pour les séries", ("Maths.Analyse.Séries",))

Énoncés des théorèmes de sommation des relations de comparaison pour les séries.

#answer

*Pour les restes de séries convergentes :*

Si $(u_n) in KK^NN, (a_n) in RR_+^NN$ et $sum a_n$ converge.

+ Si $u_n = O(a_n)$, alors $sum u_n$ converge absoluement et
  $
  sum_(k = n+1)^(+oo) u_k = O(sum_(k = n+1)^(+oo) a_n)
  $
+ Si $u_n = o(a_n)$, alors $sum u_n$ converge absoluement et
  $
  sum_(k = n+1)^(+oo) u_k = o(sum_(k = n+1)^(+oo) a_n)
  $
+ Si $u_n ~ a_n$, alors
  $
  sum_(k = n+1)^(+oo) u_k ~ sum_(k = n+1)^(+oo) a_n
  $

Démonstration : on repasse par les définitions de $o$ et $O$ : $exists N in NN, forall n >= NN, |u_n| <= K a_n$, avec $K > 0$ fixé pour $O$ et $K = epsilon > 0$ pour $o$. Pour $~$, on a $u_n - a_n = o(a_n)$.

#linebreak()
*Pour les sommes partielles de séries divergentes :*

Si $(u_n) in KK^NN, (a_n) in RR_+^NN$ et $sum a_n$ diverge.

+ Si $u_n = O(a_n)$, alors $sum u_n$ converge absoluement et
  $
  sum_(k = 0)^n u_k = O(sum_(k = 0)^n a_n)
  $
+ Si $u_n = o(a_n)$, alors $sum u_n$ converge absoluement et
  $
  sum_(k = 0)^n u_k = o(sum_(k = 0)^n a_n)
  $
+ Si $u_n ~ a_n$, alors
  $
  sum_(k = 0)^n u_k ~ sum_(k = 0)^n a_n
  $

Démonstration : même que pour l'autre, on à juste a découper la somme entre avant et après un certain rang (pour $o$ et $O$).

#card("eqvrefrim", "Équivalents de référence : séries de Riemann", ("Maths.Analyse.Séries",))

Équivalent des restes ou sommes partielles des séries de Riemann (à redemontrer).

#answer

Par comparaison série intégrale :

- Pour $1 >= alpha > 0$ #h(1fr)
  $
    integral_1^(n+1) (dif t)/t^alpha <= 1 + sum_(k = 1)^n 1/k^alpha <= integral_2^(n) (dif t) / t^alpha \
  S_n (alpha) = sum_(k = 1)^n 1 / k^alpha eqv(n -> +oo) n^(1 - alpha) / (1 - alpha)
  $
- Pour $alpha > 0$
  $
    integral_(n+1)^(+oo) (dif t) / t^alpha <= sum_(k = n + 1)^(+oo) 1/k^alpha <= integral_n^(+oo) (dif t) / t^alpha \
  R_n (alpha) = sum_(k = n + 1)^(+oo) 1/k^alpha eqv(n -> +oo) 1/(alpha - 1) dot 1 / n^(alpha - 1)
  $

#card("convsertgsp", "Exercice : Nature de la série terme général sur somme partielle", ("Maths.Analyse.Séries","Maths.Exercice.Séries"))

Démonstration de la CNS sur $alpha$ de la convergence de la série $sum u_n / S_n^alpha$ (avec $sum u_n$ divergente).

#answer

Soit $(u_n) in (RR_+^*)^NN$, $sum u_n$ diverge, et $alpha in RR$. On note $S_n = sum_(k = 1)^n u_n$.

- Si $alpha > 1$ :

#{
  set align(center)
  let base = 0.2
  let xs = lq.linspace(1, 8)
  let color = (blue,) * 6
  color.at(4) = teal
  lq.diagram(
    width: _sizes.text * 15,
    height: _sizes.text * 10,
    xlim: (1, 7),
    ylim: (0, 1),
    grid: none,
    xaxis: (
      stroke: _colors.text + 2pt,
      position: base,
      ticks: ((3, $S_(n-1)$), (4, $S_n$), (5, $S_(n+1)$)),
      subticks: none,
      tip: tiptoe.stealth,
    ),
    yaxis: (
      stroke: _colors.text + 2pt,
      position: base + 1,
      ticks: none, 
      subticks: none,
      tip: tiptoe.stealth,
    ),
    legend: lq.legend(
      line(stroke: orange, length: 1em), $script(1/t^alpha)$,
      box(fill: blue, width: 1em, height: 1em), $script(u_n / S_n^alpha)$,
      box(fill: teal, width: 1em, height: 1em), $script(u_(n+1) / S_(n+1)^alpha)$,
      fill: none,
    ),
    lq.bar(
      range(6),
      (base, base, base, 1 / 4 + base, 1 / 5 + base, base ),
      fill: color,
      align: left,
      width: 1.0,
      base: base,
    ),
    lq.plot(
      xs,
      xs.map(x => 1 / x + base),
      mark: none,
    ),
  ) 
}

Donc pour $t in Icc(S_(n-1), S_n)$
$
  1/t^alpha >= 1 / S_n^alpha \
  sum_(k = 1)^n u_k / S_k^alpha <= integral_(S_0)^S_n (dif t) / t^alpha = 1/script(alpha - 1) (1/S_0^(alpha - 1) - 1 / S_n^(alpha - 1))
$
Or $S_n tends(n -> +oo) 0$ donc

$
  sum_(n = 1)^(+oo) u_n / S_n^alpha <= 1/(alpha - 1) dot 1 / (S_0^alpha)
$

- Si $alpha = 1$ :

Si $u_n / S_n tendsnot(n->+oo) 0$, la série diverge grossièrement, et sinon

$
  u_n / S_n &~ -ln(1 - u_n / S_n) \
&~ ln(S_n) - ln(S_(n-1))
$

Qui est le terme général d'une série téléscopique divergergente.

- Si $alpha <= 1$, on compare avec $alpha = 1$, car à partir d'un certain rang $S_n >= 1$.

#card("famsom", "Familles sommables", ("Maths.Analyse.Séries",))

Définition et propriétés élémentaires des familles sommables.

#answer

Soit $I$ un ensemble non vide.

Pour $(u_i) in RR_+^I$, on définit
$
  sum_(i in I) u_i &= sup { sum_(j in J) u_j, J subset.eq I "fini"} \ &in RR_+ union {+oo}
$

Pour une famille $(u_i) in KK^I$, on dit qu'elle est sommable si 
$
sum_(i in I) |u_i| < +oo
$

Si $(u_i)_(i in I)$ est sommable, alors elle contient un nombre au plus dénombrable d'éléments non nuls (Démonstration : on étudie $J_n = {i in I | u_i >= 1 / n}$)

#card("sompaq", "Théorème de sommation par paquets", ("Maths.Analyse.Séries",))

Énoncer et éléments de démonstration du théorème de sommation par paquets.

#answer

Soit $(u_i)_(i in I) in RR^I$, et $I = union.big.plus_(n in NN) I_n$ une partition. La famille $(u_i)$ est sommable ssi

$
  (*) : cases(
    space forall n in NN\, (u_i)_(i in I_n) "sommable",
    space sum (sum_(i in I_n) abs(u_i)) "converge vers" S
  )
$

Dans ce cas

$
  sum_(i in I) u_i = sum_(n = 0)^(+oo) (sum_(i in I_n) u_i)
$

Démonstration :

- Cas positif :
  - On suppose $(*)$, on prend une sous famille fini $J$ de $I$, on a donc une famille $(J_n = I_n inter J)_n$, on note $N = max(n in NN | J_n != emptyset)$ qui existe car $J$ fini.
    $
      sum_(j in J) u_j &= sum_(n = 0)^N (sum_(j in J_n) u_j) \
&<= sum_(n=0)^(+oo) (sum_(i in I_n) u_i) = S
    $
  - Caractèrisation de la borne supérieure, majoration et sous ensembles finis.
- Cas général :
  D'abord en valeurs absolues, puis parties positives, négatives, réelles et imaginaires. 

#card("intclas", "Critère de convergence d'intégrales usuelles", ("Maths.Analyse.Intégration",))

Critère de convergence d'intégrales usuelles : 
$
  integral_1^(+oo) (dif t) / t^alpha \
  integral_0^1 (dif t) / t^alpha \
  integral_2^(+oo) (dif t) / (t^alpha (ln t)^beta) \
  integral_0^(1/2) (dif t) / (t^alpha (ln t)^beta) \
$

#answer

- $integral_1^(+oo) (dif t) / t^alpha$ converge vers $1 / (alpha - 1)$ ssi $alpha > 1$.

- $integral_0^1 (dif t) / t^alpha$ converge vers $1 / (1 - alpha)$ ssi $alpha < 1$.

- $integral_2^(+oo) (dif t) / (t^alpha (ln t)^beta)$ converge ssi $alpha > 1$ ou $alpha = 1$ et $beta > 1$

- $integral_0^(1/2) (dif t) / (t^alpha (ln t)^beta)$ converge ssi $alpha < 1$ ou $alpha  = 1$ et $beta > 1$

#card("fungamma", "Fonction gamma", ("Maths.Analyse.Intégration",))

Définition, convergence et démonstration de la fonction $Gamma$.

#answer

On définit

$
  Gamma(x) = integral_0^(+oo) e^(-t) t^(x - 1) dif t
$

- Qui converge pour $x > 0$. #h(1fr)
- Pour $x > 0$
  $
    Gamma(x+1) = x Gamma(x)
  $
- $Gamma(1) = 1$

$t |-> e^(-t) t^(x-1)$ est $C^0_"pm"$ sur $Ioo(0, +oo)$.

- Sur $Ico(1, +oo)$ #h(1fr)
  $
    e^(-t) t^(x^-1) &= o_(t->+oo) (e^(-t/2)) \
&= o_(t->+oo) (1/t^2)
  $

  Or $integral_1^(+oo) e^(-t/2) dif t$ converge, donc par le théorème de comparaison d'intégrales de fonctions positives, $integral_1^(+oo) e^(-t) t^(x - 1) dif t$ converge.
- Sur $Ioc(0, 1)$
  $
    e^(-t) t^(x - 1) eqv(t->0_+) 1 / t^(1 - x)
  $
  Or $integral_0^1 (dif t) / t^(1 - x)$ converge ssi $1 - x < 1$ d'où $x > 0$, et on conclut par le même théorème.

$
  Gamma(x + 1) &= integral_0^(+oo) e^(-t) t^x dif t \
&= [-e^(-t) t^x]_0^(+oo) + x integral_0 e^(-t) t^(x - 1) dif t \
&= x Gamma(x)
$

#card("mobiusphi", "Fonctions arithmétiques : Möbius et indicatrice d'Euler", ("Maths.Algèbre.Arithmétique",))

Définition, contexte et démonstration de la fonction de Möbius et la formule d'inversion.

#answer

Pour $A = cal(F)(NN^*, CC)$ on définit $(*)$, pour $f, g in A$

$
  f * g = cases(space display(mat(delim: #none, NN^*, ->, CC; n, |->, display(sum_(d | n) f(d) g(n / d)))))
$

Qui est une loi de composition interne sur $A$. On montre que
- $bb(1)_({1})$ est l'élément neutre.
- $(*)$ est commutatif
- $(*)$ est associatif

On définit la fonction de Möbius, on note $pi(n) = |{p in PP, p | n}|$

$
  mu : mat(delim: #none, 1, |->, 1; n | exists.not p in PP\, p^2 | n, |->, (-1)^pi(n ); n | exists p in PP\, p^2 | n, |->, 0)
$

On montre de plus

$
  mu * bb(1)_NN = bb(1)_{1}
$

Pour $n >= 2$ on écrit $n = product_(j = 1)^k p_j^(alpha_j)$. Un diviseur $d$ s'écrit $product_(j = 1)^k p_j^(beta_j)$ avec $beta_j <= alpha_j$. Donc

$
  mu(d) != 0 <=> forall j in [|1, k|], beta_j in {0, 1}
$

Ainsi

$
  sum_(d | n)  mu(d) &= sum_(beta_1, dots, beta_k in {0, 0}) mu(product_(j=1)^k p_j^(beta_j)) \
&=sum_(q = 0)^k sum_(I subset [|1, q|]) (-1)^(|I|) \
&= sum_(q = 0)^k (-1)^q vec(k, q) \
&= 0
$

On en déduit la formule d'inversion de Möbius : soit $f : NN^* -> CC$, on pose $g : n |-> sum_(n | d) f(d)$ ($g = f * bb(1)_NN$), on a alors pour tout $n in NN$

$
  f(n) = sum_(d | n) mu(d) g(n / d)
$

C'est à dire $f = g * mu = f * underbrace(bb(1)_NN * mu, bb(1)_{1})$.

De plus $mu$ est multiplicative.

#card("wallis", "Intégrales de Wallis", ("Maths.Analyse.Intégration",))

Définition, propriétés et démonstration des intégrales de Wallis.

#answer

On pose pour $n in NN$

$
  W_n &= integral_0^(pi/2) (cos t)^n dif t \ 
  &= integral_0^(pi / 2) (sin theta)^n dif theta quad  script((theta = pi/2 - t))
$

*Relation de récurrence*

$
  W_(n+2) &= integral_0^(pi/2) (sin t)^(n + 2) dif t \
&= underbrace([-cos(t) sin(t)^(n+1)]_0^(pi/2), 0) \
&+ (n+1) integral_0^(pi/2) (sin t)^n underbrace((cos t)^2, 1 - (sin t)^2) dif t \
&= (n+1) W_n - (n+1) W_(n+2) \
&= (n+1) / (n+2) W_n
$

*Formules explicites*

$
  W_0 &= pi / 2 \
  W_1 &= 1 \
  W_(2n) &= (2n)! / (2^(2n) (n!)^2) pi / 2 \
  W_(2n + 1) &= (2^(2n) (n!)^2) / (2n + 1)!
$

*Équivalents*

Pour $t in Icc(0, pi / 2)$
$
  0 <= (sin t)^(n+2) <= (sin t)^(n+1) <= (sin t)^n \
  0 <= W_(n+2) <= W_(n+1) <= W_n \
  (n+1) / (n+2) <= W_(n+1) / W_n <= 1
$

D'où 
$
  W_(n+1) &eqv(n -> +oo) W_n \
  W_(2n)^2 &eqv(n -> +oo) W_(2n + 1)^2  \
  &eqv(n -> +oo) W_(2n) W_(2n + 1) = pi / (4 n+ 2) \
$

Ainsi

$
  W_(2n + 1) eqv(n -> +oo) sqrt(pi / (4n + 2)) \
  W_(2n) eqv(n -> +oo) sqrt(pi / (4n)) \
$

#card("rimannlebesg", "Lemme de Riemann-Lebesgue", ("Maths.Analyse.Intégration",))

Énoncé et démonstration du lemme de Riemann-Lebesgue.

#answer

Si $I$ est un Intervalle de $RR$, et $f in C^0_"pm" (I, KK)$ intégrable sur $I$, alors

$
  integral_I f(t) e^(i lambda t) dif t tends(lambda -> oo) 0 \
  integral_I f(t) cos(lambda t) dif t tends(lambda -> oo) 0 \
  integral_I f(t) sin(lambda t) dif t tends(lambda -> oo) 0 \
$

*Démonstration*

- Si $f$ est $C^1$ sur un ségment : par IPP, on dérive $f$, $f'$ étant continue sur un ségment elle est uniformement continue sur ce ségment (théorème de Heine), et est donc bornée (théorème des bornes atteintes).

- On montre d'abord pour $I$ ségment.
  - On traite le cas $f$ constante.
  - On généralise à $f$ en éscalier.
  - Par densité des fonctions en éscalier on étend aux fonctions continues.
- On étend finalement aux intervalles quelconques.

#card("exunsgcycl", "Éxistence et unicité des sous groupes de groupe cyclique", ("Maths.Algèbre.Groupes",))

Soit $G$ un groupe cyclique d'ordre $n$, et $d | n$, montrer l'éxistence et l'unicité d'un sous groupe d'ordre $d$.

#answer

Soit $G$ cyclique d'ordre $n$.

Par isomorphisme à $(ZZ \/n ZZ, +)$, on se ramène à l'étude de $(UU_n, dot)$.

Soit $H$ sous groupe de $UU_n$, $|H| = d$.

Pour tout $x in H$, $x^d = 1$ donc $H subset UU_d$, par égalité des cardinaux, $H = UU_d$.

#card("polcyc", "Polynômes cyclotomiques", ("Maths.Algèbre.Polynômes",))

Définitions et propriétés des polynômes cyclotomiques.

#answer

Pour $n in NN^*$ on note 
$
VV_n &= {z in UU_n | "ord"(z) = n} \
&= { e^((2k i pi) / n) , k in (ZZ \/n ZZ)^times}
$

On définit de $n$-ème polynôme cyclotomique
$
  Phi_n (X) = product_(xi in VV_n) (X - xi) \
  deg(Phi_n) = phi(n)
$

On montre
$
  X^n - 1 = product_(d | n) Phi_d \
  Phi_n in ZZ[X] \
  Phi_p "irréductible"
$

*Démonstration*

- Pour $d | n$, on a #h(1fr)
  $
  VV_d = {z in UU_n | "ord"(n) = d}
  $
  Car si $z in UU_n$ d'ordre $d$, $z in gen(z)$ sous groupe de $UU_n$ de cardinal $d$, qui est unique car $UU_n$ est cyclique. D'où $z in UU_d$ et à fortiori $z in VV_d$.

- On a donc
  $
    UU_n = union.big.plus_(d | n) VV_d \
  $
  $
    X^n - 1 &= product_(xi in UU_n) (X - xi) \
&= product_(d | n) (product_(xi in VV_n) (X - xi)) \
&= product_(d | n) Phi_d
  $
- On montre que la division euclidienne dans $ZZ[X]$ par un polynôme unitaire donnent un polynôme dans $ZZ[X]$. On refait la démonstration de la division euclidienne (récurrence).
- Récurrence forte sur $n$ pour montrer que $Phi_n in ZZ[X]$
  $
    X^n - 1 = Phi_n dot (product_(d | n \ d != n) Phi_d) 
  $

- Soit $p in PP$

  $
    Phi_p &= product_(omega in UU_p \ "ord"(omega) = p) (X - omega) \
&= (X^p - 1) / (X - 1) = sum_(k = 0)^(p - 1) X^k
  $
  Remarquons que
  $
    tau : func(QQ[X], QQ[X], P(X), P(X+1))
  $
  est un automorphisme d'anneau.
  
  D'où $Phi_p (X)$ irréductible ssi $Phi_p (X+1)$ irréductible.

  $
    Phi_p (X+1) &= ((X+1)^p - 1) / X \
&= X^(p-1) + sum_(k=1)^(p - 1) underbrace(vec(k, p), "divisible par" p) X^(k - 1)
  $

  et le coéfficient constant est $vec(p, 1)$ qui n'est pas divisible par $p^2$, d'où par le critère d'Eisenstein, $Phi_p$ irréductible dans $QQ[X]$.


Démonstration de $n = sum_(d | n) phi(d)$ :

$
    n &= |UU_n| \ &= sum_(d | n) |VV_d| \
&= sum_(d | n) phi(d)
$

#card("quotgr", "Groupes quotientés", ("Maths.Algèbre.Groupes",))

Définitions et propriétés des groupes quotientés.

#answer

Soit $G$ un groupe, $H$ sous-groupe.

On définit la relation d'équivalence 

$
  forall (x, y) in G^2, space x ~ y "ssi" y in x H
$

On obtient ainsi les classes à gauche $g H$ pour tout $g in G$, dont l'ensemble est noté $G \/ H$.

$H$ est dit distingué si 

$
forall g in G, space g H g^(-1) = H
$

Et dans ce cas $G \/ H$   à une structure de groupe muni de la multiplication sur les classes
$
  overline(x) dot overline(y) = overline(x dot y)
$

Et on pose

$
  f : mat(delim: #none, G, ->, G \/ H; g, |->, g H)
$

qui est un morphisme de groupe surjectif appelé projection cannonique de $G$ sur $G \/ H$ dont le noyau est $H$.

*Cas particuliers*

- Tous noyau de morphisme est un sous groupe distingué.
- Tous sous-groupe d'indice 2 ($(|G|)/(|H|) = 2$) est distingué.

#card("idmax", "Idéaux maximaux, anneaux quotientés", ("Maths.Algèbre.Anneaux et corps",))

Définitions d'idéal maximale, anneau quotienté, propriétés.

#answer

Soit $(A, +, dot)$ un anneau et $I$ idéal de $A$.

*Idéal maximale*

Un idéal $I$ de $A$ est dit maximale si pour tout $J$ idéal de $A$
  $
    I subset.neq J => J = A
  $

*Anneau quotienté*

On définit sur $A$ la relation d'équivalence

$
  forall (x, y) in A^2, space x ~ y "ssi" x - y in I
$

On note $A \/ I$ l'ensemble des classes d'équivalences par cette relation qu'on muni d'une structure de groupe en définissant les loi suivantes
$
  overline(x) + overline(y) = overline(x + y) \
  overline(x) dot overline(y) = overline(x dot y) \
$

Qui ne dépend pas du représentant choisis.

*Propriétés*

- $I$ est maximale ssi tous les éléments non nuls de $A \/ I$ sont inversibles.
- Si $A$ commutatif, $I$ maximale, alors $I$ est premier ($A \/ I$ est intègre).

Démonstration :

- On suppose $I$ maximale. Soit $x in A\\I$ c'est à dire $x in.not overline(0_A)$, montrons que $overline(x)$ est inversible. 

  $I subset.eq x A + I = J$ est un idéal, or $I$ maximale d'où $1_A in A = J$, d'où l'éxistence de $y in A$ et $z in I$ tel que

  $
    x y + z = 1_A \
    overline(x y) = overline(1_A)
  $
- On suppose les éléments non nuls de $I \/ A$ inversibles.

  Soit $J supset.neq I$ idéal de $A$, donc il existe $x in J$ tel que $x in.not I$.

  $overline(x) != overline(0)$ donc $overline(x)^(-1) = overline(y)$ existe.
  $
  overline(x) overline(y) = overline(x y) = overline(1_A) \
  exists z in I, space underbrace(x y + z, in J) = 1_A
  $

  $1_A in J$ donc $J = A$, $I$ est maximale.
- Soit $x, y in A$ tels que $x y in I$, supposons que $x in.not I$. Donc $overline(x)$ inversible : on dispose de $x' in A$ et $z in I$ tels que

  $
    x x' + z = 1_A \
    overbrace(underbrace(x y, in I) x' + z y, in I) = y in I
  $

#card("sigsn", "Signature d'une permutation", ("Maths.Algèbre.Groupes",))

// TODO: Finish this ? I think this might need more but idk.

Définitions et propriétés de la signature dans $frak(S)_n$.

#answer

Plusieurs définitions alternatives.

- $epsilon : (frak(S)_n, compose) -> (ZZ^times, dot)$ est l'unique morphisme non triviale.

Pour $sigma in frak(S)_n$ :

$
epsilon(sigma) &= product_(1 <= i < j <= n) (sigma(i) - sigma(j)) / (i - j) \
&=  (-1)^(N_sigma) \
&= (-1)^(n - |"Orb"(sigma)|)
$

Où $N_sigma = |{(i, j) | i < j "et" sigma(i) > sigma(j)}|$.

#card("hold", "Hölder", ("Maths.Analyse.Intégration",))

Inégalité de Hölder et démonstration.

#answer

Soit $p, q in RR_+^star$ tels que $1/p + 1/q = 1$.

Pour $x_1, dots, x_n, y_1, dots, y_n in RR_+$ #h(1fr)

$
  sum_(i=1)^n x_i y_i <= (sum_(i = 1)^n x_i^p)^(1/p) (sum_(i = 1)^n y_i^q)^(1/q)
$

*Démonstration*

- Pour tout $x, y in RR_+$ #h(1fr)
  $
  x y <= 1/p x^p + 1/q y^q
  $
  Le cas nul se traite facilement, puis on utilise la concavité de $ln$ sur $RR_+^*$ :
  $
    ln(1/p x^p + 1/q y^q) &>= 1/p ln(x^p) + 1/q ln(y^q) \ &= ln(x y) \
    1/p x^p + 1/q y^q &>= x y 
  $
- On traite d'abord le cas où l'un des vecteurs ($X$ ou $Y$) est nul.
- On traite ensuite le cas où
  $
    sum_(i = 1)^n x_i^p = 1 quad "et" quad sum_(j = 1)^n y_j^q = 1 \
  $
  Pour tout $i in [|1, n|]$
  $
    x_i y_i &<= 1/p x_i^p + 1/q y_i^q \
    sum_(i = 1)^n x_i y_i &<= 1/p underbrace(sum_(i = 1)^n x_i^p, 1) + 1/q underbrace(sum_(i = 1)^n y_i^q, 1) \
  &<= 1 = (sum_(i = 1)^n x_i^p)^(1/p) (sum_(i = 1)^n y_i^q)^(1/q)
  $
- Enfin dans le cas général, on pose pour $i in [|1, n|]$
  $
    accent(x, ~)_i = x_i / (sum_(i = 1)^n x_i) quad quad 
    accent(y, ~)_i = y_i / (sum_(i = 1)^n y_i)
  $
  Et ça marche.

// TODO: Minkowski

#card("actgr", "Actions de groupe", ("Maths.Algèbre.Groupes",))

Définitions et exemples usuels, propriétés des actions de groupes.

#answer

Soit $G$ un groupe, $X$ un ensemble. Une action de groupe est la donnée d'un morphisme de groupe
$
  phi : func(G, frak(S)(X), g, rho_g : func(X, X, x, rho_g (X) = g.x))
$

Ainsi tout groupe fini de cardinal $n in NN$ est isomorphe à un sous groupe de $frak(S)_n$.

*Démonstration*

Grâce à l'action de groupe $phi$
$
  phi : func(G, frak(S)(G) tilde.eq frak(S)_n, a, rho_& : func(G, G, g, a g))
$
Qui est un morphisme de groupe (car $rho_a compose rho_b = rho_(a, b)$), injectif (car $ker phi = e_G$), d'où $phi|_(phi(G))$ isomorphisme de $G -> phi(G)$, avec $phi(G)$ sous groupe de $frak(S)(G) tilde.eq frak(S)_n$.

*Autre action classique*

On peut aussi considérer l'action de conjugaison
$
  theta : func(G, frak(S)(G), g, rho_g : func(G, G, x, g x g^(-1)))
$

On a 
$
ker theta &= { g in G | theta(g) = id } \
&= {g in G | forall x in G, g x g^(-1) = x} \
&= {g in G | forall x in G, g x = x g} \
&= Z(G) \
$

#card("formcl", "Formule des classes", ("Maths.Algèbre.Groupes",))

Énoncé, démonstration et définitions de la formule des classes.

#answer

Soit $G$ un groupe et $phi$ une action de $G$ sur un ensemble $X$. On définit pour tout $x in X$

$
  "Stab"(x) = {g in G | g.x = x}
$

C'est un sous groupe de $G$ :
- $e.x = x$ d'où $e in "Stab"(x)$ \
- $forall g in "Stab"(x), g^(-1).x = g^(-1).g.x = x$
- $forall g, h in "Stab"(x), (g h).x = g.h.x = x$

On définit également

$
  "Orb"(x) = { g.x, g in G }
$

Qui est la classe d'équivalence de $x$ pour la relation d'équivalence

$
  x ~ y "si" exists g in G, y = g.x
$

Donc les orbites forment une partition de $X$.

*Formule des classes*

Pour tout $x in X$ fini et $G$ fini
$
  |"Orb"(x)| dot |"Stab"(x)| = |G|
$

*Démonstration*

Soit $x in X$, pour $y in "Orb"(x)$, on dispose de $g_0 in G$ tel que $g_0.x = y$.

Étudions ${g in G | g.x = y}$ :

$
  g.x = y &<=> g.x = g_0.x \
&<=> (g_0^(-1) g).x = x \
&<=> g_0^(-1) g in "Stab"(x) \
&<=> g in g_0 "Stab" (x)
$

D'où

$
  G &= union.big.plus_(y in "Orb"(x)) { g in G | g.x = y} \
  |G| &= sum_(y in "Orb"(x)) |g_0 "Stab" (x)| \
&= sum_(y in "Orb"(x)) |"Stab" (x)| \
&= |"Orb"(x)| dot |"Stab" (x)| \
$

#card("pgroup", "Exercice : Les p-groupes", ("Maths.Algèbre.Groupes","Maths.Exercice.Algèbre Générale"))

Définitions d'un $p$-groupe, et démonstration de
+ Pour $G$ $p$-groupe, $|Z(G)| = p^alpha$ avec $alpha in NN^*$.
+ Tout groupe $G$ d'ordre $p^2$ est abélien

#answer

Un $p$-groupe est un groupe dont tout les éléments sont d'odre $p^gamma$ avec $p in PP$. A fortiori, il s'agit d'un groupe de cardinal $p^alpha$.

+ On étudie l'action de groupe 
  $
    phi : func(G, frak(S)(G), g, rho_g : func(G, G, x, g x g^(-1)))
  $

  On montre que 
  $
  x in Z(G) "ssi" "Orb"(x) = {e_G}
  $
  Et par la formule des classes on a pour tout $x in G$ :
  $
    p^alpha = |G| = |"Orb"(x)| dot |"Stab"(x)|
  $
  Donc $|"Orb"(x)| | p^alpha$ d'où si $|"Orb"(x)| > 0, p | |"Orb"(x)|$.
  
  Or les $"Orb"(x)$ forment une partition de $G$ donc

  $
      p^alpha &= |G| = sum_(x in G) |"Orb"(x)| \
&= |Z(G)| + underbrace(sum_(x in G \/ ~ \ |"Orb"(x)| > 1) |"Orb"(x)|, "divisible par " p)
  $

  Donc $p | |Z(G)|$ mais $e_G in Z(G)$ donc $|Z(G)| > 0$ d'où $|Z(G)| >= p$.
+ Par l'exercice ci dessus
  $
    Z(G) in {p, p^2}
  $
  Supposons qu'il existe $x in G\\Z(G)$, alors 
  $
    Z(G) subset "Stab"(x) "et" x in "Stab"(x)
  $ 
  Donc $|"Stab"(x)| >= p + 1$ sous-groupe de $G$ donc 
  $
    "Stab"(x) = G
  $
  D'où $x in Z(G)$, absurde.

#card("exeordp", "Exercice : élément d'ordre p dans un groupe d'ordre divisé par p", ("Maths.Algèbre.Groupes", "Maths.Exercice.Algèbre Générale"))

Soit $G$ un groupe d'ordre $p q$ avec $p in PP$ et $q in NN^star$, démonstration de l'éxistence d'un élémént d'ordre $p$.

#answer

Soit $G$ d'odre $n = p q$ avec $(p, q) in PP times NN^*$.

On pose
$
  Gamma = { (x_1, dots, x_p) in G^p | x_1 dots.c x_n = e_G} \
  sigma = (1 space 2 space dots.c space p) in frak(S)_p
$

On considère $H = gen(sigma)$ qui agit sur $Gamma$ via
$
  phi : func(H, frak(S)(Gamma), sigma^k, rho_(sigma^k))

$
Où
$
  rho_(sigma^k) : func(Gamma, Gamma, (x_1, dots, x_p), (x_(sigma^k (1)), dots, x_(sigma^k (p))))
$
(On montre par récurrence sur $k$ que $rho_(sigma^k)$ à bien valeur dans $Gamma$).

On remarque que $|H| = p$ et
$
  forall X = (x_1, dots, x_p) in G^p, \ X in Gamma <=> x_p^(-1) = x_1 dots.c x_(p-1) \
  Gamma tilde.eq G^(p-1) "donc"
  |Gamma| = n^(p-1)
$

Pour tout $x in Gamma$ (par la formule des classes)
$
  p = |H| = |"Orb"(x)| dot |"Stab"(x)| \
  "donc" |"Orb"(x)| in {1, p} \
$
$
  "Orb"(x) = {x} &<=> x_1 = x_2 = dots.c = x_p \
  &<=> x_1^p = e_G
$

Et
$
  n^(p - 1) &= |Gamma| = sum_(x in Gamma \/ ~) |"Orb"(x)| \
&= sum_(x in Gamma \/ ~ \ |"Orb"(x)| = 1) 1 + sum_(x in Gamma \/ ~ \ |"Orb"(x)| > 1) p \
&= |{x in G | x^p = e_G}| + k p
$
Avec $k in NN$. Or $p | n$ donc 
$
p | |{x in G | x^p = e_G}| >= 1
$
Donc il existe au moins $p - 1$ éléménts d'ordre $p$.

*Cas $n = 2$ :*

On regroupe les éléments avec leurs inverse, ce qui montre par la parité du cardinale l'éxistence d'un élémént d'ordre $2$.

#card("burnside", "Théorème de Burnside", ("Maths.Algèbre.Groupes",))

Énoncer et démonstration du théorème de Burnside.

#answer

Soit $G$ un groupe fini qui agit sur un ensemble $X$ fini par $phi$.

On définit pour $g in G$

$
  "Fix"(g) = { x in X, g.x = x}
$

Notons $N$ le nombre d'orbites :

$
  N = 1/(|G|)sum_(g in G) |"Fix"(g)|
$

*Démonstration*

On étudie
$
  Gamma &= { (g, x) in G times X | g.x = x } \
&= union.big.plus_(x in X) { (g, x), g in "Stab"(x) } \
&= union.big.plus_(g in G) { (g, x), x in "Fix"(g) }
$

Or par la formule des classes
$
  |"Stab"(x)| = (|G|) / (|"Orb"(x)|)
$

D'où (en notant $x_i$ représentant du $i$-ème orbite)

$
  |Gamma| &= sum_(x in X) |"Stab"(x)| \
&= sum_(j = 1)^N sum_(x in overline(x_j)) |"Stab"(x)| \
&= sum_(j = 1)^N sum_(x in overline(x_j)) (|G|) / (|"Orb"(x_j)|) \ 
&= N |G|
$

Or

$
  |Gamma| = sum_(g in G) |"Fix"(g)|
$

D'où

$
  N = 1/(|G|) sum_(g in G) |"Fix"(g)|
$

#card("grord2", "Exercice : Groupe d'éléments d'ordre inférieur à deux", ("Maths.Exercice.Algèbre Générale",))

Propriétés du groupe $G$ tel que $forall x in G, x^2 = 1$

#answer

On a immédiatement 
$
forall x in G, x = x^(-1)
$

- $G$ est abélien, soit $x,y in G$ : #h(1fr)
  $
    x y = (x y)^(-1) = y^(-1) x^(-1) = y x
  $
- Si $G$ fini, $G tilde.eq (ZZ\/2ZZ)^n$ et $|G| = 2^n$ pour un $n in NN$.

  Passons en notation additive pour plus de caireté :

  Faison de $G$ un $FF_2$-ev :

  $
    func(delim: #none, FF_2 times G, G, (overline(k), g), k g)
  $

  Qui ne dépend pas du représentant car $2 G = {0}$.

$G$ un $FF_2$-ev de dimension finie, donc isomorphe à $FF_2^n$ en tant qu'éspace vectoriel, et à fortiori en tant que groupe.

#card("irean", "Irréductibles d'un anneau", ("Maths.Algèbre.Anneaux et Corps",))

Définition, propriétés élémentaires sur les irréductibles dans un anneau principal.

#answer

Soit $(A, +, dot)$ un anneau principal.

- Dans un anneau principal on a un PGCD

  Pour tout $a, b in A$, il existe $d in A$ tel que $a A + b A = d A$, unique (à associés près), qu'on appelle PGCD de $a$ et $b$ ($a and b = d$).

  On a aussi Bézout car $d in d A = a A + b A$ d'où $exists (u, v) in A^2, d = a u + b v$.
- Un élément de $A$ est dit irréductible si ses seuls diviseurs sont ses associés et les inversibles.
- Pour tout $a in A$, il existe une unique (à permutation et multiplication par des inversibles près) décomposition de $a$ en irréductibles.

*Démonstration de la décomposition*

- Toute suite croissante d'idéaux est stationnaire.
  
  $(I_i)_(i in NN)$ suite d'idéaux de $A$ croissante au sens de l'inclusion.
  $
    K = union.big_(i in NN) I_i
  $
  Est encore un idéal car union croissante d'idéaux

  Par principalité de $A$, $K = z A$ avec $z in K$ donc on dispose de $k in NN$ tel que $z in I_k$ d'où
  $
    K = z A subset.eq I_k subset.eq K
  $
- Tout élément de $A$ admet au moins un diviseur irréductible dans $A$.

  Soit $x in A$, on construit la suite $(x_n)$ par récurrence : $x_0 = x$ et pour $n in NN$
  - Si $x_n$ irréductible, $x_(n+1) = x_n$
  - Sinon on prend $x_(n+1)$ diviseur de $x_n$ non associés et non inversible.
  
  Par définition de la divisibilité, $(x_n A)_n$ est une suite croissante d'idéaux, et est donc stationnaire. 

  Soit $k$ le rang à partir du quel c'est le cas, $x_k$ est donc un diviseur irréductible de $x$.
- Éxistence de la décomposition : récurrence avec la propriété ci dessus.
- Unicité de la décomposition : on prend deux décomposition on montre que chaque irréductible est présent à la même puissance dans les deux.

#card("carspos", "Polynômes en caractèristique strictement positive", ("Maths.Algèbre.Polynômes",))

Remarques et mises en gardes à propos de $KK[X]$ quand $"car"(KK) > 0$

#answer

Soit $KK$ un corps tel que $"car"(KK) > 0$

- Le morphisme d'évaluation $theta : KK[X] -> cal(F)(KK, KK)$ n'est pas forcément injectif.

  Dans $FF_p$, $theta (X^p - X) = theta(0) = 0_(cal(F)(FF_p, FF_p))$ or $X^p - 1 != 0$.

- Il n'y a pas équivalence entre multiplicité d'une racine et les valeurs des dérivées succéssives.

  Pour $"car"(KK) = p in PP$

  Pour $k in [|1, p - 1|]$

  $
    vec(k, p) = overbrace(p (p-1) dot dots.c dot (p - k + 1), p "divise") / underbrace(k!, p "ne divise pas")
  $

  D'où $vec(k, p)$ nul dans $KK$.

  Ainsi pour tout $a, b in KK$

  $
    (a + b)^p &= a^p + b^p + sum_(k = 1)^(p - 1) vec(k, p) a^k b^(p - k)  \
&= a^p + b^p
  $

  Et on peut définir le morphisme de corps de Frobenius

  $
    sigma : func(KK, KK, x, x^p)
  $

  Donc dans $FF_p [X]$

  $
    Q = (X - 1)^p = X^p - 1
  $

  $1$ est racine de multiplicité $p$ de $Q$ or $Q' = 0$ d'où pour tout $k in NN, Q^((k)) (1) = 0$.

#card("thwilson", "Théorème de Wilson", ("Maths.Algèbre.Arithmétique",))

Énoncer et démonstration du théorème de Wilson.

#answer

Pour tout $p in NN^star$, $p$ est premier ssi $(p - 1)! equiv -1 [p]$.

*Démonstration*

- Soit $n in NN^star$ non premier.
  - Si $3 <= n = m^2$ avec $m in NN^star$. $2 m dot m | (n - 1)!$ d'où $(n - 1)! equiv 0 [n]$
  - Sinon on dispose de $1 <= p, q < n$ tels que $n = p q$ d'où $n = p q | (n - 1)!$ et $(n - 1)! equiv 0 [n]$.
- Soit $p in PP$, étudions $(p - 1)!$ dans $(ZZ \/ p ZZ)^times$

  Soit $x in (ZZ \/ p ZZ)^times$ tel que $x^2 = 1$

  $
    (x + 1)(x - 1) = 0
  $

  Donc $x = {1, -1}$.

  On peut donc regrouper les éléments du produit $(p - 1)!$ avec leurs inverses (qui sont dans le produit), à l'éxception de $1$ et $-1$ d'où

  $
    (p-1)! &= (p-1) (p - 2) dot dots.c  dot 1 \
  &= -1 dot 1 = 1
  $

  Dans $ZZ \/ p ZZ$.

*Autre démonstration horrible pour le deuxième sens*

Soit $p in PP$, on étudie $R = X^p - X$ dans $FF_p [X]$.

  Pour tout $x in FF_p, R(x) = 0$ donc $(X - x) | R$ et premiers entre eux deu x à deux d'où

  $
    product_(x in FF_p) (X - x) | R
  $

  Et par égalité des degrés on a égalité des polynômes.

  Considèrons maintenant le morphisme d'anneau suivant :
  $
    pi : func(ZZ[X], FF_p [X], sum_(k = 0)^n a_k X^k, sum_(k = 0)^n overline(a_k) X^k) \

    Q = product_(k = 0)^(p - 1) (X - k) = X^p + sum_(k = 0)^(p - 1) a_k X^k \
    pi(Q) = product_(k = 0)^(p - 1) (X - overline(k)) = R \
  $
  $
    a_1 &= (-1)^(p - 1) sum_(I subset [|0, p-1|] \ |I| = p - 1) product_(i in I) i \
&= (p - 1)! \
    overline(a)_1 &= overline((p-1)!) = -1
  $

#card("taylorform", "Formule de Taylor-Langrange formelle", ("Maths.Algèbre.Polynômes",))

Formule de Taylor-Langrange formelle sur $KK[X]$, démonstration.

#answer

Soit $KK$ un corps tel que $"car"(KK) = 0$, $P in KK[X], N >= deg P "et" a in KK$.

$
  P = sum_(k = 0)^N P^((k)) (a) (X - a)^k / k!
$

*Démonstration*

Notons $E = KK_N [X]$ qui est un $KK$-ev de dimension $N+1$.

La famille $((X - a)^k)_(k in [|0, N|])$ est libre car échelonné en degré, c'est donc une base de $E$, et comme $P in E$, et comme $P in E$

$
  P = sum_(k = 0)^N lambda_k (X - a)^k
$

Pour $j in [|0, N|]$

$
  P^((j)) (a) &= sum_(k = j)^N (lambda_k k!) / (k - j)! (a - a)^(k - j) \
&= lambda_j j! \
  lambda_j &= (P^((j)) (a)) / j!
$

#card("polentz", "Contenus d'un polynôme à coéfficients entiers", ("Maths.Algèbre.Polynômes",))

Définitions, propriétés, et démonstrations à propos du contenu dans $ZZ[X]$.

#answer

Soit $P = sum_(k = 0)^d a_k X^k in ZZ[X]$, on définit le contenu de $P$ comme

$
  c(P) = and.big_(k = 0)^d a_k
$

Et on dit qu'un polynôme $P$ est primitif si $c(P) = 1$.

- Soient $P, Q in ZZ[X]$ tels que $c(P) = c(Q) = 1$, alors $c(P Q) = 1$.A
- Pour tout $P, Q in ZZ[X], c(P Q) = c(P) c(Q)$.

*Démonstration*

- Soit $p in PP$, posons le morphisme d'anneau #h(1fr)
  $
    pi: func(ZZ[X], FF_p [X], sum_(k=0)^d a_k X^k, sum_(k = 0)^d overline(a_k) X^k)
  $
  
  $c(P) = 1$ donc $P$ admet au moins un coéfficient non divisible par $p$ et de même pour $Q$.

  $
    pi(P) != 0 "et" pi(Q) != 0 \
    pi(P Q) = pi(P) pi(Q) != 0
  $

  Donc $p$ ne divise pas tous les coéfficients de $P Q$ pour tout $p in PP$, d'où $c(P Q) = 1$.
- On remarque que pour $P in ZZ[X]$ et $k in ZZ$, $c(k P) = k c(P)$ et on étudie $accent(P, ~) = P / c(P)$ et $accent(Q, ~) = Q / c(Q)$.

#card("exocont1", "Exercice : Produit de polynômes de rationels unitaire entier", ("Maths.Exercice.Polynômes",))

Soient $P, Q in QQ[X]$ unitaires, montrer que si $P Q in ZZ[X]$ alors $P, Q in ZZ[X]$.

#answer

$P, Q in QQ[X]$ unitaires, $P Q in ZZ[X]$.

Comme $P Q$ unitaire $c(P Q) = 1$. On trouve $a, b in ZZ$ tels que $a P, b Q in ZZ[X]$.

$
  c(a P) c(b Q) = a b c(P Q) = a b
$

Or $P$ et $Q$ étant unitaires

$
  cases(c(a P) | a, c(b Q) | b) "donc" cases(a = k_a c(a P), b = k_b c(b Q)) \
  c(a P) c(b Q) = a b = k_a k_b c(a P) c(b Q) \
  "d'où" k_a = k_b = 1 "et" cases(a = c(a P), b = c(b Q))
$
Ainsi

$
  cases(P = a P / a in ZZ[X], Q = b Q / b in ZZ[X])
$

#card("exocont2", "Exercice : Irréductibilité dans les rationels", ("Maths.Exercice.Polynômes",))

Soit $P in ZZ[X]$ dont les seuls diviseurs dans $ZZ[X]$ sont de degré $0$ ou $deg P$, montrer que $P$ est irréductible dans $QQ[X]$.

#answer

On suppose par contraposé que $P$ n'est pas irréductible dans $QQ$.

$
P = Q R \
1 <= deg Q, deg R <= deg P - 1
$

On introduit $a, b in ZZ$ tels que $a Q, b R in ZZ[X]$.

$
  a b c(P) &= c(a Q b R) \
&= c(a Q) c(b R) \
$
$
P &= (a Q b R) / (a b) \
&= ((a Q)(b R)) / ((c(a Q) c(b R)) / (c(P))) \
&= c(P) dot underbrace((a Q) / (c(a Q)), Q_0) dot underbrace((b R) / (c(b R)), R_0) in ZZ[X]
$

Avec $Q_0$ et $R_0$ diviseurs de $P$ dans $ZZ[X]$ de degrés compris dans $[|1, deg P - 1|]$.

#card("entieralg", "Entiers algébriques", ("Maths.Algèbre.Polynômes",))

Définition d'entier algébrique.

#answer

Soit $alpha in CC$, on dit que $alpha$ est un entier algébrique s'il existe $Q in ZZ[X]$ unitaire tel que $Q(alpha) = 0$.

+ $alpha$ est donc aussi algébrique dans $QQ$, et son polynôme minimal est aussi dans $ZZ[X]$.

*Démonstration*
+ Notons $P_alpha$ ce polynôme, comme $Q(alpha) = 0, P_alpha | Q$ dans $QQ[X]$, d'où 
  $
  ZZ[X] in.rev Q = P_alpha R in QQ[X]
  $

  Et donc $P_alpha, R in ZZ[X]$ car $Q$ unitaire (cf. exercices sur le contenu).

#card("expolent", "Exercice : Polynômes à coéfficients entiers", ("Maths.Exercice.Polynômes",))

+ Soit $P = sum_(k = 0)^d a_k X^k in ZZ[X]$, montrer que si $P$ admet une racine rationelle $p / q$ avec $p and q = 1$, alors $q | a_d$ et $p | a_0$.

#answer

+ #h(1fr)
  $
    0 = P(p / q) &= sum_(k = 0)^d a_k p^k q^(d - k) \
    - underbrace(sum_(k = 0)^(d - 1) a_k p^k q^(d - k), "divisible par" q) &= a_d p^d \
    - underbrace(sum_(k = 1)^d a_k p^k q^(d - k), "divisible par" p) &= a_0 q^d
  $
  D'où $cases(q | a_d p^d, p | a_0 q^d)$ or $q and p = 1$ donc par le théorème de Gauss, $cases(q | a_d, p | a_0)$.

  On en déduis que si $P in ZZ[X]$ est unitaire et admet une racine rationelle, alors elle est entière.

#card("eisenstein", "Critère d'Eisenstein", ("Maths.Algèbre.Polynômes",))

Énoncé et démonstration du critère d'Eisenstein.

#answer

Soit $P = sum_(k=0)^d a_k X^k in ZZ[X]$ tel qu'il existe $p in PP$ et
$
  cases(forall k in [|0, d - 1|]\, p | a_k, p divides.not a_d, p^2 divides.not a_0)
$

Alors $P$ n'a pas de diviseurs dans $ZZ[X]$ de degré compris dans $[|1, d - 1|]$, et est donc irréductible dans $QQ[X]$ (cf. exercices sur le contenu).

*Démonstration*

On considère le morphisme d'anneau suivant
$
  pi: func(ZZ[X], FF_p [X], sum_(k = 0)^d a_k X^k, sum_(k = 0)^d overline(a_k) X^k)
$

Supposons par l'absurde que $P = Q R$ avec $Q, R in ZZ[X]$

$
  overline(0) != overline(a_d) X^d = pi(P) = pi(Q) pi(R)
$

Par unicité de la décomposition en irréductibles dans $FF_p [X]$

$
  pi(Q) = alpha X^k quad pi(R) = beta X^l \
  k + l = d space space deg Q >= k space space deg R >= l
$
Or $deg Q + deg R = d$ d'où
$
  Q = sum_(i = 0)^k b_i X^i "avec" cases(space overline(b_k) = alpha != 0, space overline(b_0) = 0) \
  R = sum_(i = 0)^l c_i X^i "avec" cases(space overline(c_l) = beta != 0, space overline(c_0) = 0) \
$
D'où $a_0 = b_0 c_0$ est divisible par $p^2$, absurde.

#card("exratmul", "Exercice : rationalité d'une racine de haute multiplicité", ("Maths.Exercice.Polynômes",))

Soit $P in QQ[X]$ de degré $n$ et $alpha$ racine de $P$ de multiplicité $m_alpha > n / 2$, montrer que $alpha in QQ$.

#answer

Soit $P in QQ[X]$ de degré $n$ et $alpha$ racine de $P$ de multiplicité $m_alpha > n / 2$.

$
  P = product_(k = 0)^N Q_k^p_k
$

Décomposition en irréductibles de $P$ dans $QQ[X]$. Pour tout $i != j, P_i and P_j = 1$ dans $QQ[X]$ et donc dans $CC[X]$.

Ainsi $alpha$ n'est racine que d'un des $P_i$, notons $P_1(alpha) = 0$.

C'est une racine simple car $P_1$ irréductible, d'où

$
  p_1 >= m_alpha > n / 2 \
2p_1 > n >= p_1 deg(P_1) \
  2 > deg(P_1) = 1
$

Donc $P_1 = lambda (X - alpha) in QQ[X]$ d'où $alpha in QQ$.

#card("algb", "Algèbres", ("Maths.Algèbre.Algèbres",))

Définition d'une $KK$-Algèbre avec $KK$ un corps.

#answer

Une $KK$-Algèbre est un ensemble $A$ muni de deux lois de composition internes $(+)$, $(times)$ et d'une loi de composition externe $(dot)$ tel que
- $(A, +, times)$ est un anneau
- $(A, +, dot)$ est un $KK$-ev
- $forall (alpha, x, y) in KK times A^2$ #h(1fr)
  $
    alpha (x times y) = (alpha x) times y = x times (alpha y)
  $

*Exemples*
- $KK$ est une $KK$-Algèbre
- $(KK[X], +, times, dot)$ est une $KK$-Algèbre
- Pour $E$ un $KK$-ev, $(cal(L)(E), +, compose, dot)$ est une $KK$-Algèbre.

#card("exordppcm", "Exercice : existence d'un élément d'ordre du ppcm de deux autres", ("Maths.Exercice.Algèbre Générale",))

+ Soit $G$ un groupe abélien fini, montrer que pour tout $x, y in G$, il existe un élément $z in G$ tel que $"ord"(z) = "ord"(x) or "ord"(y)$.

+ En déduire que 
$
max_(g in G) "ord"(g) = or.big_(g in G) "ord"(g)
$

#answer

+ Soit $G$ un groupe abélien, $x, y in G$ qui admettent un ordre.

  $
    "ord"(x) = product_(i = 1)^N p_i^alpha_i \
    "ord"(y) = product_(i = 1)^N p_i^beta_i \
  $

  Pour tout $k in [|1, N|]$
  $
    "ord"(x^(product_(i != k) p_i^alpha_i)) = p_k^alpha_k \
    "ord"(y^(product_(i != k) p_i^beta_i)) = p_k^beta_k
  $

  On pose alors 
  $
  z_k = cases(space x^(product_(i != k) p_i^alpha_i) "si" alpha_k >= beta_k, space y^(product_(i != k) p_i^beta_i) "sinon")
  $
  D'où $"ord"(z_k) = p_k^max(alpha_k, beta_k)$

  Ainsi en posant $z = product_(k = 1)^N z_k$ :

  $
  "ord"(z) &= product_(k = 1)^N p_k^max(alpha_k, beta_k) \ &= "ord"(x) or "ord"(y)
  $

  (Car $G$ est abélien).

+ Par récurrence (car $G$ fini) on dispose de $h in G$ tel que
  $
    "ord"(h) = or.big_(g in G) "ord"(g) = m
  $
  Posons $g_0 in G$ d'ordre $max_(g in G) "ord"(g)$.

  On a donc
  $
    m <= "ord"(g_0) | m \
    m = "ord"(g_0)
  $

#card("excyclsginvcor", "Exercice : Cyclicité des sous-groupes finis des inversibles d'un corps", ("Maths.Exercice.Algèbre Générale",))

Soit $KK$ un corps, et $G <= KK^times$ fini. Montrer que $G$ est cyclique.

#answer

*Première méthode*

On utilise la propriété suivante (à redémontrer) : si $G$ abélien fini
$
  max_(g in G) "ord"(g) = or.big_(g in G) "ord"(g)
$

Or pour tout $g in G, g^m = 1$ d'où
$
  G subset {"racines de" X^m - 1 "dans" KK[X]}
$
D'où $|G| <= m$ car $KK$ est un corps et ainsi l'élément d'ordre maximale est d'ordre supérieure ou égal au cardinal de $G$, d'où $G$ cyclique.

*Deuxième méthode*

Pour $d | n = |G|$ on pose
$
  Gamma_d = {g in G | "ord"(g) = d} \
  G = union.plus.big_(d | n) Gamma_d \
  n = sum_(d | n) |Gamma_d| \
$

On pose aussi
$
  A_d &= {g in G | g^d = 1} \
  &= {"racines de" X^d - 1} inter G \
|A_d| &<= d
$

Pour $d | n$ on a
- $Gamma_d = emptyset$ et $|Gamma_d| = 0$
- Ou il existe $x in Gamma_d$, d'où $gen(x) subset A_d$ et $d <= |A_d| <= d$.

  Ainsi 
  $
    Gamma_d = {g in A_d = gen(x) | "ord"(g) = d} \
  |Gamma_d| = phi(d)
  $

Finalement

$
  sum_(d | n) phi(d) = n = sum_(d | n) underbrace(|Gamma_d|, in {0, phi(d)})
$

D'où nécéssairement $|Gamma_d| = phi(d)$ pour tout $d | n$, en particulier pour $|Gamma_n| = phi(n) > 0$ : il existe $phi(n)$ éléments d'ordre $n$.

#card("excarfp", "Exercice : Les carrés de Fp", ("Maths.Exercice.Algèbre Générale",))

Notons $FF_p^2 = {x^2, x in FF_p}$ et $FF^(*^2)_p = {x^2, x in FF_p^*}$.

+ Montrer que $abs(FF_p^2) = (p + 1)/ 2$ et $abs(FF^(*^2)_p) = (p - 1) / 2$.
+ Montrer que pour $x in FF_p^*$, $x in FF^(*^2)_p$ ssi $x^((p - 1)/2) = overline(1)$.
+ En déduire que pour $p >= 3$, $-1$ est un carré ssi $p equiv 1 [4]$.
+ On suppose $p equiv 3 [4]$, pour $x in FF_p^*$ montrer que $x$ est un carré ssi $-x$ n'en est pas un.
+ Soit $p in PP | p equiv -1 [4]$, pour tout $r in FF_p^*$ montrer que $Gamma_r = {(x, y) in (FF_p^*)^2 | x^2 - y^2 = r}$ est de cardinal $p - 3$.

#answer

+ On étudie le morphisme de groupe #h(1fr)

  $
    theta : func(FF_p^*, FF^(*^2)_p, x, x^2) \
  $
  $
    ker theta &= {x in FF_p^*, x^2 = 1} \
    &= {x in FF_p^*, (x - 1)(x + 1) = 0} \ 
    &= {-1, 1} \ 
  $
  $
    underbrace(abs(ker theta), 2) dot underbrace((im theta), abs(FF^(*^2)_p)) = p - 1
  $
  D'où $abs(FF^(*^2)_p) = (p - 1) / 2$. 

  Et $FF_p = FF_p^* union {0}$ d'où
  $
    abs(FF_p^2) = abs(FF^(*^2)_p) + 1 = (p + 1) /2
  $

+ Soit $x in FF_p^(*^2)$, on écrit $x = y^2$ avec $y in FF_p^*$.

  $
    x^((p - 1) / 2) = y^(p - 1) = overline(1)
  $
  D'où

  $
    underbrace(FF_p^(*^2), (p - 1) / 2) subset underbrace({"racines de" X^((p - 1) / 2) - 1}, <= (p - 1) /2)
  $

  D'où l'égalité des ensembles.

+ $
    overline(-1) in FF_p^(*^2) &<=> (-1)^((p - 1)/2) = overline(1) \
&<=> (p - 1) / 2 in 2 ZZ \
&<=> p equiv 1 [4]
  $
+ On suppose $p equiv 3 [4]$
  $
    (-1) in.not FF_p^(*^2) quad "car" (-1)^((p- 1) / 2) = -1 \
  $
  $
    x in FF_p^(*^2) &<=> x^((p-1)/2) = 1 \
&<=> (-x)^((p - 1)/2) = -1 \
&<=> -x in.not FF_p^(*^2)
  $

+ 
  - Si $r$ est un carré, $r = a^2$ avec $a in FF_p^*$
    $
      (x, y) in Gamma_r &<=> x^2 - y^2 = a^2 \
  &<=> (x a^(-1))^2  - (y a^(-1))^2 = 1 \
  &<=> (x a^(-1), y a^(-1)) in Gamma_1
    $

    D'où $abs(Gamma_r) = abs(Gamma_1)$
  - Si $r$ n'est pas un carré, $-r$ en est un.

    $
      (x, y) in Gamma_r &<=> y^2 - x^2 = -r
    $
  
    Et on se ramène au cas précédent.

    $
      abs(Gamma_r) = abs(Gamma_1)
    $

  Dénombrons $Gamma_1$.

  $
    (x, y) in Gamma_1 &<=> x^2 - y^2 = 1 \
&<=> (x - y)(x + y) = 1
  $

  Posons $a = x + y, b = x - y$ ($p$ impair d'où $2 in FF_p^*$)

  $
    x &= a + b / 2 \
    y &= a - b / 2 \
  $

  $
    (x, y) in Gamma_1 <=> b = a^(-1)
  $

  On a $(p - 1)$ choix pour $a$, et $b$ déterminé par $a$, d'où au plus $(p-1)$ couples.

  Il faut exclure les cas où notre choix de $a$ permet $x, y in.not FF_p^star$ :

  $
    x = overline(0) &<=> a = -a^(-1) \
&<=> a^2 = -1 \
    y = overline(0) &<=> a = a^(-1) \
&<=> a^2 = 1 \
  $
  
  Ainsi $abs(Gamma_r) = abs(Gamma_1) = p - 3$.

#card("salg", "Sous algèbres", ("Maths.Algèbre.Algèbres",))

Définition, propriétés des sous-algèbres.

#answer

Soit $(A, +, times, dot)$ une $KK$-algèbre, $B subset A$ est une sous-algèbre de $A$ si c'est un sous-anneau et un sev de $A$.

De plus si $B$ est de dimension finie

$
  B^times = B inter A^times
$

*Démonstration*

On a évidement $B^times subset B inter B^times$.

On suppose $b in B inter A^times$, on dispose de $a in A, a b = b a = 1$.

On pose
$
  phi_b = func(B, B, x, b c) in cal(L)(B)
$

Soit $x in ker phi_b$, on a $b x = 0$ donc $(a b) x = x = 0$.

Donc $phi_b$ bijectif (argument dimensionnel), et $phi_b^(-1)(b) = a$ existe et $a in B$.

#card("csalgcor", "Algèbres commutatives intègres de dimension finie", ("Maths.Algèbre.Algèbres",))

Que peut-on dire d'une algèbre $(A, +, times, dot)$ commutative et intègre de dimension finie ?

#answer

Si $(A, +, times, dot)$ est commutative, intègre et de dimension finie, alors c'est un corps.

*Démonstration*

Soit $a in A \\ {0}$, étudions

$
  phi_a : func(A, A, x, a x) in cal(L) (A)
$

$
  ker phi_a &= {x in A | a x = 0} \
&= {x in A | x = 0} quad "(par integrité)" \
&= {0}
$

Et par argument dimensionnel, $phi_a$ bijectif, d'où $phi_a^(-1)(a) = a^(-1)$ existe.

#card("morpalg", "Morphisme d'algèbre", ("Maths.Algèbre.Algèbres",))

Définition, propriétés des morphismes d'algèbres.

#answer

Pour $A, B$ deux $KK$-algèbre, une application $phi : A -> B$ est un morphisme d'algèbre si c'est un morphisme d'anneau linéaire.

Et dans ce cas $im phi$ est une sous-algèbre de $B$ et $ker phi$ est un idéal et un sev de $A$.

#card("devsg", "Dévissage de groupes", ("Maths.Algèbre.Groupes","Maths.Exercice.Algèbre Générale"))

Propriétés, outils du dévissage de groupes.



#answer

+ Soient $G$ et $H$ deux groupes cycliques de cardinaux $n$ et $p$, $G times H$ est cyclique ssi $n and p = 1$.
+ 

*Démonstration*

+ - Par contraposé, supposons que $n and p = d > 1$, ainsi $m = n or p < n p$.

    Pour tout $(x, y) in G times H$,
    $
      (x, y)^m = (x^m, y^m) = (e_G, e_H)
    $
    donc $"ord"((x, y)) | m < |G times H|$ qui ne peut être cyclique.

  - Soit $x in G$ d'ordre $n$ et $y in H$ d'ordre $p$. Pour $k in NN^*$

    $
      (x, y)^k &<=> (x^k, y^k) = (e_G, e_H) \
&<=> cases(n | k, p | k) <=> n p | k \
&<=> G times H "cyclique"
    $
  
  - Autre méthode :
    $
      G tilde.eq ZZ \/ n ZZ \
      H tilde.eq ZZ \/ p ZZ \ 
    $
    $
      G times H &tilde.eq ZZ \/ n ZZ times ZZ \/ p ZZ \ 
&tilde.eq ZZ \/ (n p) ZZ quad "cyclique"\
    $

+ Soient $H, K$ sous-groupes de $G$ et $phi$ (qui n'est pas forcément un morphisme) tel que

  $
    phi : func(H times K, G, (h, k), h k)
  $

  On note $H K = phi(H times K)$. Soient $(h, k), (h_0, k_0) in H times K$

  $
   & phi(h, k) = phi(h_0, k_0)  \ 
<=> & h k = h_0 k_0 \
<=> & h_0^(-1) h = k_0 k^(-1) = t in H inter K \ 
<=> & exists t in H inter K, space cases(space h = k_0 t, space k = t^(-1) h_0)
  $

  $phi$ est injectif ssi $H inter K = {e_G}$, c'est automatique si $|H| and |K| = 1$ (en étudiant les ordres et les divisibilités de ceux-ci).

  Dans ce cas $abs(H K) = abs(im phi) = abs(H) dot abs(K)$

  Dans le cas général 
  $
    abs(phi^(-1) {phi(h_0, k_0)}) = abs(H inter K)
  $

#card("grodied", "Groupe Diédral", ("Maths.Algèbre.Groupes",))

Construction et propriétés du groupe diédral.

#answer

*Construction*

Soient $n >= 2$ et $A_0, dots, A_(n-1)$ des points de $RR^2$ d'afixes
$
  forall i in [|0, n-1|], A_i : e^((2 i k pi) / n)
$
On considère $Gamma$ l'ensemble des isométries qui préservent le polygone $A_0, dots, A_(n-1)$.

Comme une transformation affine préserve les barycentres, tout élément de $Gamma$ préserve l'isobarycentre (l'origine).

On a alors
$
  Gamma in O(RR^2)
$
Et donc tout $gamma in Gamma$, est soit une rotation ou une réflexion.

- Si $gamma$ est une rotation :
  $gamma(A_0) in {A_0, dots, A_(n-1)}$ d'où $gamma = "rot"((2k pi)/ n)$ pour un $k in [|0, n - 1|]$.

  On note $r$ la rotation d'angle $(2 pi) / n$
  $
    gamma = r^k
  $

- Si $gamma$ est une réflexion

  Soit $s$ la réflexion à l'axe des abscices, $s in Gamma$.

  $s compose gamma in Gamma$ est une rotation car
  $
    det(s compose gamma) = (-1)^2 = 1
  $

  Ainsi $exists k in [|0, n-1|]$ tel que
  $
    s compose gamma = r^k <=> gamma = s compose r^k
  $

Donc
$
  Gamma &= union.big_(k = 0)^(n - 1) {r^k, s r^k}
$

*Groupe*

$Gamma$ est un sous-groupe de $O(RR^2)$.

- $abs(Gamma) = 2 n$
- $Gamma = gen(s\, r)$

#card("algeng", "Algèbre engendrée", ("Maths.Algèbre.Algèbres",))

Pour $(A, +, times, dot)$ une $KK$-algèbre et $alpha in A$, définition et propriétés de $KK[alpha]$.

#answer

Soit $(A, +, times, dot)$ une $KK$-algèbre et $alpha in A$. Si on pose le morphisme d'algèbre
$
  theta_alpha : func(KK[X], A, P = sum_(k = 0)^d a_k X^k, sum_(k = 0)^d a_k alpha^k)
$

On note $KK[alpha] = im theta_alpha$ qui est la plus petite sous-algèbre de $A$ contenant $alpha$.

De plus $ker theta_alpha$ est un idéal de $KK[X]$.
- Si $theta_alpha$ est injectif et $KK[alpha] tilde.eq KK[X]$ qui est donc de dimension infinie.

- Sinon on dispose d'un unique polynôme $pi_alpha$ unitaire tel que $ker theta_alpha = pi_alpha KK[X]$ (par principalité).

  $pi_alpha$ est appelé polynôme minimal de $alpha$, $KK[alpha]$ est de dimension $d = deg pi_alpha$ et $(1, alpha, dots, alpha^(d-1))$ en est une base.

*Démonstration*

- Soit $B in KK[X] \\ {0}$ et $d = deg B$, par l'éxistence et l'unicité de la division euclidienne on a

  $
    KK[X] = B KK[X] plus.circle KK_(d - 1) [X]
  $

- Soit $u in cal(L)(E, F)$ et $G$ un supplémentaire de $ker u$, montrons que $u|_G$ est un isomorphisme de $G -> im u$.

  $ker u|_G = ker u inter G = {0}$ par supplémentarité.

  Soit $y in im u, y = u(x), x = a + b$ avec $(a, b) in ker u times G$.

  $
    u(x) &= underbrace((a), 0) + u(b) \
y &= u|_G (b)
  $

  Soit $y in im u|_G, y = u|_G (x) = u(x)$.

  D'où $im u = im u|_G$.

- Si $theta_alpha$ est injectif, c'est un isomorphisme de $KK[X]$ sur $im theta_alpha = KK[alpha]$.

- Sinon on a $pi_alpha$ de degré $d$ et
  $
    KK[X] = pi_alpha KK[X] plus.circle KK_(d - 1) [X]
  $

  $KK_(d - 1)$ est un supplémentaire de $ker theta_alpha$, ainsi $theta_alpha|_(KK_(d - 1) [X])$ est un isomorphisme de $KK_(d - 1) [X] -> KK[alpha]$, d'où
  $
    dim KK[alpha] = d
  $

  Et l'image de la base cannonique de $KK_(d - 1) [X]$ par $theta|_(KK_(d - 1) [X])$ est

  $
    (1, alpha, dots, alpha^(d - 1))
  $
  Qui est donc une base de $KK[alpha]$.

#card("intkalph", "Condition d'intégrité d'une sous-algèbre engendrée", ("Maths.Algèbre.Algèbres",))

Pour $A$ une $KK$-algèbre et $alpha in A$ tel que $theta_alpha$ n'est pas injectif, sous quelle condition $KK[alpha]$ est elle intègre ?

#answer

Soit $A$ une $KK$-algèbre et $alpha in A$ tel que $theta_alpha$ n'est pas injectif.

$KK[alpha]$ est intègre ssi $pi_alpha$ est irréductible.

*Démonstration*

- Si $pi_alpha$ irréductible, soit $x = P(alpha), y = Q(alpha) in KK[alpha]$ tels que $x y = 0$.

  $
    P Q (alpha) = 0 \
    pi_alpha | P Q
  $

  Donc par le lemme d'Euclide, 
  $
  "ou" space cases(delim: #none, pi_alpha | P <=> x = 0, pi_alpha | Q <=> y = 0)
  $
- Par contraposé, si $pi_alpha$ non irréductible, $pi_alpha = P Q$ avec $P, Q in KK[X]$ non inversible ou associé à $pi_alpha$.

  $
    underbrace(P(alpha), != 0) underbrace(Q(alpha), != 0) = pi_alpha (alpha) = 0
  $

  D'où $KK[alpha]$ non intègre.

#card("inverkkalp", "inversibilité des éléments d'une sous-algèbre engendrée", ("Maths.Algèbre.Algèbres",))

Soit $KK[alpha]$ une sous-algèbre de $A$ de dimension finie pour $alpha in A$, sous quelle condition $x in KK[alpha]$ est il inversible ?

#answer

Soit $KK[alpha]$ une sous-algèbre de $A$ de dimension finie pour $alpha in A$. Soit $x = P(alpha) in KK[alpha]$.

$
  x in KK[alpha]^times "ssi" P and pi_alpha = 1
$

On en déduit que $KK[alpha]$ est un corps ssi $pi_alpha$ est irréductible.

*Démonstration*

Par propriété de sous-algèbre

$
  KK[alpha]^times = A^times inter KK[alpha]
$

Ainsi

$
  x in KK[alpha]^times &<=> exists y in KK[alpha], x y = 1 \
&<=> exists Q in KK[X], P Q (alpha) = 1 \
&<=> exists Q in KK[X], pi_alpha | (P Q - 1) \
&<=> exists Q, V in KK[X], P Q - 1 = pi_alpha V \
&<=> exists Q, V in KK[X], P Q - pi_alpha V = 1 \
&<=> P and pi_alpha = 1
$

Ainsi si $pi_alpha$ irréductible, pour tout $x = P(alpha) in KK[alpha] \\ {0}, P and pi_alpha = 1$ d'où $x$ inversible et $KK[alpha]$ est un corps.

Et si $KK[alpha]$ est un corps, alors il est intègre et $pi_alpha$ irréductible.

#card("algextc", "Algèbres et extensions de corps", ("Maths.Algèbre.Algèbres",))

Propriétés des algèbres en lien avec les extensions de corps.

#answer

Soient $KK subset.eq LL$ deux corps. On remarque que $LL$ est une $KK$-algèbre.

+ Soit $alpha in LL$ qui admet un polynôme annulateur dans $KK[X]$ et $pi_alpha$ son polynôme minimal.

  $pi_alpha$ est irréductible dans $KK[X]$ et $KK[alpha]$ est un corps.

*Démonstration*

+ $P, Q in KK[X]$ tels que $pi_alpha = P Q$.

  Dans $LL$

  $
    P (alpha) Q (alpha) = pi_alpha (alpha) = 0
  $

  Donc $P(alpha) = 0 <=> pi_alpha | P$ ou $Q(alpha) = 0 <=> pi_alpha | Q$ donc $pi_alpha$ irréductible.

  Ainsi $KK[alpha]$ est un corps.

#card("algebriques", "Nombres algébriques", ("Maths.Algèbre.Algèbres",))

Définitions et propriétés des nombres algébriques sur un corps $KK$.

#answer

Soit $alpha in A$ une $KK$-algèbre, on dit que $alpha$ est algébrique sur $KK$ s'il admet un polynôme annulateur dans $KK[X]$.

Par défaut $alpha$ algébrique veut dire algébrique sur $QQ$., quitte à les échangers prenons $P(alpha) = 0, P in ker theta_alpha = pi_alpha KK[X]$.

*Propriété*

+ Soit $alpha in LL$ une extension de corps de $KK$, $alpha$ algébrique sur $KK$.

  Pour tout $P in KK[X]$ unitaire, $P = pi_alpha$ ssi $P(alpha) = 0$ et $P$ irréductible sur $KK[X]$.

*Démonstration*

+ Sens directe connus. Soit $P in KK[X]$ unitaire, irréductible et annulateur de $alpha$.

  On a $pi_alpha | P$, or $P$ irréductible donc $P$ et $pi_alpha$ sont associé, or tout deux unitaires donc $P = pi_alpha$.

#card("bastel", "Théorème de la base téléscopique", ("Maths.Algèbre.Algèbre Linéaire",))

Énoncer et démonstration du théorème de la base téléscopique.

#answer

Soit $KK subset.eq LL$ deux corps tel que $LL$ est de dimension finie sur $KK$.

Soient
- $E$ un $LL$-ev, (et donc un $KK$-ev).
- $e = (e_1, dots, e_n)$ base de $E$ sur $LL$.
- $z = (z_1, dots, z_p)$ base de $LL$ sur $KK$.

Alors $F = (z_i e_j)_(i in [|1, p|] \ j in [|1, n|])$ est une base de $E$ sur $KK$

Ainsi $dim_KK E = dim_LL E dot dim_KK LL$.

*Démonstration*

- Soit $omega in E$, on dispose de $lambda_1, dots, lambda_n in LL$ tels que
  $
    omega = sum_(j = 1)^n lambda_j e_j
  $
  On dispose de $(a_(i j))_(i j) in KK^[|1, p|]^[|1, n|]$ 
  $
    forall j in [|1, n|], lambda_j = sum_(i = 1)^p alpha_(i j) z_i \
  $
  Ainsi
  $
    omega = sum_(j = 1)^n sum_(i = 1)^p alpha_(i j) z_i e_j
  $

- Soit $(a_(i j))_(i j) in KK^[|1, p|]^[|1, n|]$ tel que

  $
    sum_(j = 1)^n underbrace(sum_(i = 1)^p a_(i j) z_i, lambda_j in LL) e_j = 0 \
    sum_(j = 1)^n lambda_j e_j = 0
  $
  Donc pour tout $j in [|1, n|], lambda_j = 0$.
  $
    lambda_j = sum_(i = 1)^p a_(i j) z_i = 0
  $
  Donc par liberté de $z$, $a_(i j) = 0$ pour tout $i, j$.

#card("clotrat", "Clôture algébrique des rationnels", ("Maths.Algèbre.Algèbres",))

Propriétés de la clôture algébrique de $QQ$.

#answer

Notons $KK$ l'ensemble des $alpha in CC$ algébriques sur $QQ$.

$KK$ est un corps algébriquement clos.


*Démonstration : corps*

- Soit $alpha, beta in KK$, montrons que $alpha beta, alpha + beta in KK$.

  On utilise le fait que $z$ algébrique dans $LL$ ssi $LL[z]$ de dimension finie sur $LL$ (car $z$ admet un polynôme annulateur dans $LL[X]$).

  - Donc $QQ[alpha]$ est de dimension finie sur $QQ$, 

  - $beta$ algébrique sur $QQ subset QQ[alpha]$ donc algébrique sur $QQ[alpha]$.
  - Donc $QQ[alpha][beta]$ est de dimension finie sur $QQ[alpha]$, et donc par le théorème de la base téléscopique, sur $QQ$.

  - Or $QQ[alpha + beta], QQ[alpha beta] subset.eq QQ[alpha][beta]$, donc $QQ[alpha + beta]$ et $QQ[alpha beta]$ sont de dimension finie sur $QQ$.

- Soit $alpha in KK\\{0}$, soit $pi_alpha$ son polynôme minimal et $d = deg pi_alpha$.

  $
    underbrace(X^d pi_alpha (1 / X), in QQ[X]) space "annule" space 1/ alpha
  $

  Donc $1 / alpha in KK$

- $1 in KK$ car $QQ subset.eq KK$.

*Démonstration : clôture*

Soit $P = sum_(k = 0)^d a_k X^k in KK[X]$. Soit $alpha in CC$ racine de $KK$, montrons que $alpha in KK$.

Pour tout $k in [|0, d|], a_k in KK$ donc $QQ[a_k]$ de dimension finie sur $QQ$.

Par récurrence on a 
$
LL = QQ[a_0][a_1] dots.c [a_d]
$
De dimension finie sur $QQ$.

Comme $P in LL[X]$ annule $alpha$, $LL[alpha]$ est de dimension finie sur $LL$ et donc sur $QQ$, id est $alpha in KK$.
