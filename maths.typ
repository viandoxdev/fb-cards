#import "cards.typ": *

#show: setup

#card("anatl", "Taylor-Langrange", ("Maths.Analyse.Dérivation", "Maths.Analyse.Taylor"))

Théorème de Taylor-Lagrange, et conditions d'application.

#answer

Soit $f : [a, b] -> RR$, $C^n$ sur $[a, b]$ et $D^(n+1)$ sur $]a,b[$

Il existe $c in ]a, b[$ tel que
$
  f(b) = sum_(k = 0)^(n) f^((k))(a) (x - a)^k / (k!) + f^((n+1)) (c) (x - a)^(n+1) / ((n+1)!)
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

#card("nbfermat", "Nombres de Fermat", ("Maths.Algèbre.Arithmétique",))

Que sont les nombres de Fermat, et quelques propriétées.

#answer

Le $n$-ème nombre de Fermat est 
$
F_n = 2^(2^n) - 1
$
Ils sont impaires et premier entre eux :

Soit $n < m in NN$,

$
  &(2^(2^n) - 1)& dot &F_n& dot &F_(n+1) dot dots.c dot F_(m - 1) \
  &(2^(2^n) - 1)& dot &(2^(2^n) + 1)& dot &F_(n+1) dot dots.c dot F_(m - 1) \
  &&& (2^(2^(n+1)) - 1)& dot &F_(n+1) dot dots.c dot F_(m-1) \
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
  ZZ_(\/ p ZZ) "est un anneaux intègre :" \
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
  phi space : space mat(delim: #none,
    ZZ_(\/ m n ZZ), ->, ZZ_(\/ m ZZ) times ZZ_(\/ n ZZ);
    x,|->,vec(x &space [m], x &space [n])
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
  On étudie $(ZZ_(\/p ZZ))^"inv"$ :
  $
    forall a in (ZZ_(\/p ZZ))^"inv", "ord"(a) | p - 1 "(Lagrange)" \
    a^(p - 1) equiv 1 space [p]
  $

#card("indeuler", "Indicatrice d'Euler", ("Maths.Algèbre.Arithmétique",))

Définition de l'indicatrice d'Euler, et propriétées.

#answer

La fonction indicatrice d'Euler est
$
  phi space : space mat(delim: #none, NN^star, ->, NN; n, |->, abs((ZZ_(\/n ZZ))^"inv")) \
$
Quelques propriétées :

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

  Soit $diff$ tel que $d | a$ et $d | b$. $forall x in I, diff | x$, en particulier $diff | d$ d'où $diff <= d$.

  $a and b = d in I$ d'où $exists u,v in ZZ, d = a u + b v$

#card("propidcd", "Propriétées diviseurs communs", ("Maths.Algèbre.Arithmétique",))

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
  forall x <= y in C, [x, y] subset.eq C
$
Les parties convexes de $RR$ sont des intervalles.

#card("densite", "Densité", ("Maths.Analyse.Réels",))

Définition de densité.

#answer

Soit $D subset.eq RR$, $D$ est dense dans $RR$ si
$
  forall a < b in RR, ]a, b[ inter D != emptyset
$
$QQ$ est dense dans $RR$, preuve : saut de grenouille.

#card("vois", "Voisinage", ("Maths.Analyse.Réels",))

Définition de voisinage.

#answer

Soit $x in overline(RR)$, $V subset.eq RR$ est un voisinage de $x$ si 
$
exists epsilon > 0, ] x-epsilon, x+epsilon [ subset.eq V
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
  &= {x in RR | script(forall epsilon > 0\, \]x-epsilon\, x+epsilon\[ inter A != emptyset)}
$
Propriétés :
- $A subset.eq "adh"(A)$
- Si $A$ non vide borné : ${inf A, sup A} subset.eq A$
- $"adh"(]a,b[) = [a,b]$
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

Formule explicite d'une suite récurrent d'ordre 2.

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
  "adh"(A) = {x in RR | exists (u_n) in A^NN, u_n -> x}
$
Et $S = sup A$ existe si $A$ non vide majoré par $S$ et il existe $(u_n) in A^NN$ tel que $u_n -> S$.

#card("suitadj", "Suites adjacentes, emboitées", ("Maths.Analyse.Suites Réelles",))

Définition et théorème des suites adjacentes et emboitées.

#answer

- Adjacentes :

  Deux suites $(a_n)$ et $(b_n)$ sont adjacentes si
  $
  (a_n) arrow.tr, quad (b_n) arrow.br, quad lim_(n -> oo) (b_n - a_n) = 0
  $

  Théorème : $(a_n)$ et $(b_n)$ et $lim a_n = lim b_n$.

  Preuve : Théorème de la limite croissante pour la convergence.
- Emboitées :

  La même chose avec des segments.

  Théorème : 
  $
    inter.big_(n=0)^oo [a_n, b_n] = {x} "avec" x = lim a_n = lim b_n
  $

#card("bolzweie", "Théorème de Bolzano-Weiestrass", ("Maths.Analyse.Suites Réelles",))

Théorème de Bolzano-Weiestrass et démonstration.

#answer

Toute suite réelle bornée admet une sous-suite convergente. Dans $RR^n$ (et $CC$), il suffit d'ếtre borné en norme ou module.

Preuve :

Soit $(u_n)$ une suite bornée par $a_0$ et $b_0$, notons $A = {u_n, n in NN}$. Par récurrence :
- Ini : $abs([a_0, b_0] inter A) = oo$
- Héré : On suppose $abs([a_n, b_n] inter A) = oo$, et on coupe en $m = (a_n + b_n) / 2$ :
  - Si $abs([a_n, m] inter A) = oo$, $cases(a_(n+1) = a_n, b_(n+1) = m)$ #v(8pt)
  - Si $abs([m, b_n] inter A) = oo$, $cases(a_(n+1) = m, b_(n+1) = b_n)$

Par le théorème des suites emboitées : 
$
exists l in [a_0, b_0], space inter.big_(n = 0)^oo [a_n, b_n] = {l}
$

Soit $phi$ une extractrice, par récurrence :
- Ini : $phi(0) = 0$
- Héré : $[a_(n+1), b_(n+1)]$ est infini, donc il existe $m > phi(n)$ tel que $u_m in [a_(n+1), b_(n+1)]$. On prend $phi(n+1) = m$.

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
- $l$ inifni : majoration.

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

Si $f$ est $C^0 ([a, b])$, alors $f$ est bornée et atteint ses bornes.

Preuve :

Notons $M = sup f$, quitte à avoir $M in overline(RR)$. $M in "adh"_overline(RR)(f([a, b]))$, donc il existe une suite $(x_n)$ à valeur dans $[a, b]$ tel que $f(x_n) -> M$.

Par Bolzano-Weiestrass, il existe $phi$ tel que $x_n -> l$ avec $l in [a, b]$ et donc nécéssairement $M in RR$.
