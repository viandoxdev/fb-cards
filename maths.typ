#import "cards.typ": *

#show: setup

#card("anatl", "Taylor-Langrange", ("Maths.Analyse.Dérivation", "Maths.Analyse.Taylor"))

Théorème de Taylor-Lagrange, et conditions d'application.

#answer

Soit $f : [a, b] -> RR$, $C^n$ sur $[a, b]$ et $D^(n+1)$ sur $]a,b[$

Il existe $c in ]a, b[$ tel que
$
  f(b) = sum_(k = 0)^(n) f^((k))(a) (x - a)^k / (k!) + f^(n+1) (c) (x - a)^(n+1) / ((n+1)!)
$

#card("anatlri", "Taylor reste intégrale", ("Maths.Analyse.Intégration", "Maths.Analyse.Taylor"))

Théorème de Taylor reste intégrale, et conditions d'application.

#answer

Soit $f : [a, b] -> RR$, $C^(n+1)$

$
  f(b) = sum_(k = 0)^(n) f^((k))(a) (x - a)^k / (k!) + integral_a^b f^((n + 1)) (t) (b - t)^n / (n!) dif t
$

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
$
  cos p + cos q &= &2 cos((p + q) / 2) cos ((p - q) / 2) \
  cos p - cos q &= -&2 sin ((p + q) / 2) sin ((p - q) / 2) \
  sin p + sin q &= &2 sin ((p + q) / 2) cos ((p - q) / 2) \
$

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
  abs(union.big_(k = 1)^n A_k) &= sum_(k = 1)^n (-1)^k sum_script(1 <= i_1 < dots.c < i_k <= n) abs(inter.big_(j = 1)^k A_(i_j))
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
  (E_2) : quad y' = c(x) y
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
- Relation quotienté par $H$ : $x re y$ si $y x^(-1) in H$ (relation d'équivalence). On note $G_(\/ H)$ l'ensemble des classes d'équivalences.
- Soit $x in G$, $accent(x, macron)$ sa classe d'équivalence pour $re$. $accent(x, macron) = H x = {h x, h in H}$.

  Par double inclusion :
  - $H x subset.eq accent(x, macron)$ : Soit $y in H x$, $y = h x$ avec $h in H$, donc $y x^(-1) = h in H$ d'où $y re x$ et $y in accent(x, macron)$.
  - $accent(x, macron) subset.eq H x$ : Soit $y in accent(x, macron)$, $y x^(-1) = h in H$, donc $y = h x in H x$.
- Donc $forall x in G, accent(x, macron) = H x tilde.eq H$ d'où $abs(accent(x, macron)) = abs(H)$.
- Enfin par le lemme du berger : $abs(G_(\/ H)) = abs(G) / abs(H)$ et donc $abs(H) | abs(G)$.

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

Le groupe des inversibles d'un anneau $(A, +, dot)$, est le groupe $(A^"inv", dot)$.

#card("ideal", "Idéal d'un anneau", ("Maths.Algèbre.Anneaux et corps",))

Définition d'un idéal d'un anneau.

#answer

Soit $(A, +, dot)$ un anneau et $I subset.eq A$, $I$ est un idéal de $A$ si

- $I$ est un sous-groupe additif de $A$
- $I$ est stable par produit externe : $forall x in I, forall a in A, a x in I$

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
