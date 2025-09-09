#import "cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#card("anatl", "Taylor-Langrange", ("Maths.Analyse.Dérivation", "Maths.Analyse.Taylor"))

Théorème de Taylor-Lagrange, et conditions d'application.

#answer

Soit $f : [a, b] -> RR$, $C^n$ sur $[a, b]$ et $D^(n+1)$ sur $]a,b[$

Il existe $c in ]a, b[$ tel que
$
  f(b) = &sum_(k = 0)^(n) f^((k))(a) (b - a)^k / (k!) \ 
         &+ f^((n+1)) (c) (b - a)^(n+1) / ((n+1)!)
$

#card("anatlri", "Taylor reste intégrale", ("Maths.Analyse.Intégration", "Maths.Analyse.Taylor"))

Théorème de Taylor reste intégrale, et conditions d'application.

#answer

Soit $f : [a, b] -> RR$, $C^(n+1)$

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
    forall a in (ZZ_(\/p ZZ))^"inv" \
    "ord"(a) | p - 1 "(Lagrange)" \
    "donc" a^(p - 1) equiv 1 space [p]
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

  Soit $diff$ tel que $diff | a$ et $diff | b$. $forall x in I, diff | x$, en particulier $diff | d$ d'où $diff <= d$.

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
    inter.big_(n=0)^oo [a_n, b_n] = {x} \ "avec" x = lim a_n = lim b_n
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

Si $f$ est $C^0 ([a, b])$, alors $f$ est bornée et atteint ses bornes.

Preuve :

Notons $M = sup f$, quitte à avoir $M in overline(RR)$. $M in "adh"_overline(RR)(f([a, b]))$, donc il existe une suite $(x_n)$ à valeur dans $[a, b]$ tel que $f(x_n) -> M$.

Par Bolzano-Weiestrass, il existe $phi$ tel que $x_(phi(n)) -> l$ avec $l in [a, b]$ et donc nécéssairement $M in RR$.

#card("heine", "Théorème de Heine", ("Maths.Analyse.Continuité",))

Énoncé et démonstration du théorème de Heine.

#answer

Toute fonction continue sur un segment est uniformement continue.

Preuve :

Soit $f in C^0([a,b])$. Supposons par l'absurde que $f$ n'est pas uniformement continue.

$
  exists epsilon > 0, forall delta > 0, exists x, y in [a,b] \
  |x - y| < delta "et" |f(x) - f(y)| >= epsilon
$
 
On prend $(x_n), (y_n) in [a,b]^NN$ tel que 
$
forall n in NN, |x_n - y_n| < 1/n \
|f(x_n) - f(y_n)| >= epsilon
$
Ces suites sont bornées donc par Bolzano-Weiestrass, il existe une extractrice $phi$ tel que $x_(phi(n)) -> l in [a, b]$.

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

#let ivl(delim: "[]", a, b) = {
  let (l,r) = delim.split("").slice(1, count: 2)
  $
  lr(class("opening", #l) #a, #b class("closing", #r))
  $
}

$
  mat(delim: #none,
    arccos,:,ivl(-1, 1),->,ivl(0, pi);
    arccos',:,ivl(-1, 1, delim: "]["),->,ivl(-1,-oo, delim: "[[");
    ,,x,|->,-1/sqrt(1 - x^2);;
    arcsin,:,ivl(-1,1),->,ivl(-pi/2,pi/2);
    arcsin',:,ivl(-1,1, delim: "]["),->,ivl(1,+oo, delim: "[[");
    ,,x,|->,1/sqrt(1 - x^2);;
    arctan,:,RR,->,ivl(-pi/2, pi/2, delim: "][");
    arctan',:,RR,->,ivl(0,1, delim: "]]");
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
Soit $f in C^0([a,b])$ dérivable sur $class("opening", ]) a,b class("closing", \[)$ 

/ Rolle: Si $f(a) = f(b)$, alors 
  $
  exists c in class("opening", ]) a,b class("closing", \[), space f'(c) = 0
  $
/ TAF:
  $
  exists c in class("opening", ]) a,b class("closing", \[), space f'(c) = (f(b) - f(a)) / (b - a)
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
  abs(f(x) - f(a)) <= sup_[a,x] abs(f') dot abs(x - a)
$
/ Inégalité de Taylor-Lagrange: #linebreak()
  Soit $f : I -> RR$ qui est $D^(n+1)$ et $a in I$, pour tout $x in I$
$
abs(f(x) - sum_(k = 0)^n f^((k))(a) (x - a)^k / k!)\ <= sup_[a,x] abs(f^((n+1))) dot abs(x - a)^(n+1) / (n+1)!
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
  &= sum_(k=1)^n (vec(2k, k) x^(2k+1))/(2^(2k)(2k+1)) + o(x^(2n+1)) \
  script(arccos(x)) &= -x - 1/2 x^3 / 3 - 3/8 x^5/5 + o(x^5) \
  &= sum_(k=1)^n inline(- (vec(2k, k) x^(2k+1))/(2^(2k)(2k+1)) + o(x^(2n+1))) \
  script(arctan(x)) &= x - x^3 / 3 + x^5/5 + o(x^5) \
  &= sum_(k=1)^n (-1)^k x^(2k+1) / (2k+1) + o(x^(2n+1)) \
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
forall x, y in I, forall lambda in [0, 1] \ f(lambda x + (1 - lambda) y) \ <= lambda f(x) + (1-lambda) f(y)
$

Propriétés :
- Soit $f : I -> RR$ convexe, $forall x_1, dots, x_n in I$
  $
  forall lambda_1, dots, lambda_n in [0, 1], lambda_1 + dots.c + lambda_n = 1 =>\
  f(sum_(i = 1)^n lambda_i x_i) <= sum_(i = 1)^n lambda_i f(x_i)
  $
- Soit $Phi$ convexe, $forall f in C^0([a,b])$
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
- L'unique polynôme qui à une infinité de racines est $P = 0$.
- Si $n >= 0$, alors $P$ à au plus $n$ racines.
- Si $Q in KK_n [X]$ et $exists alpha_0, dots, alpha_n in KK$ tels que $forall k in [|0, n|], P(alpha_k) = Q(alpha_k)$, alors $P = Q$.

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

- Dans $CC$, les polynômes irréductibles sont les monômes (théorème de Gauss-d'Alembert).
- Dans $RR$, les polynômes irréductibles sont les monômes et les polŷnomes de degré $2$ avec $Delta < 0$.

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
    norm(P) = max_(t in [-1, 1]) abs(P (t))
  $
  Si $P$ unitaire de degré $n$, alors $norm(P) >= 1 / (2^(n-1))$.

  Avec cas d'égalité si $P(X) = (T_n (X)) / (2^(n-1))$

Preuves :
+ Formules de trigonométrie : #h(1fr)
  $
  script(cos((n+1)theta) + cos((n-1)theta) = 2 cos theta cos(n theta)) \
  script(T_(n+1) (cos theta) + T_(n-1) (cos theta) = 2 (cos theta) T_(n) (cos theta))
  $
  Donc ils coincident en une infinité de valeurs $[-1, 1]$, et sont donc égaux.
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
