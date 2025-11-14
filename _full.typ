#import "../cards.typ": *
#show: setup
#[

#import "/utils.typ": *
#import "@preview/cetz:0.4.2"
#import "@preview/tiptoe:0.3.1"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/physica:0.9.7": *
// Bad solution but works, in french cross products are written ^ instead of ×
#show sym.times: sym.and

// TODO: These are all relatively low quality and thats kinda meh, I should go over this again when I have the time (when will I ever have the time ?)

#card("phali", "Amplificateurs Opérationels", ("Physique.Électricité",))

// TODO: This

#answer

#card("syscoordanvec", "Systèmes de coordonées orthogonales", ("Physique.Analyse Vectorielle",))

Définitions élémentaires de système de coordonées orthogonales en analyse vectorielle.

#answer

On peut décrire l'espace dans un système de coordonées $(q_1, q_2, q_3)$ associé au trièdre local $(va(e_1), va(e_2), va(e_3))$.

Un déplacement élémentaire $va(dif M)$ s'éxprime

$
  va(dif M) &= h_1(q_1, q_2, q_3) dif q_1 va(e_1) \ &+ space h_2(q_1, q_2, q_3) dif q_2 va(e_2) \ &+ space h_3(q_1, q_2, q_3) dif q_3 va(e_3)
$

- En cartésiennes $(x, y, z)$ : #h(1fr)

  $
    h_1 = h_2 = h_3 = 1 \
    va(dif M) = dif x va(u_x) + dif y va(u_y) + dif z va(u_z)
  $

- En cylindriques $(r, theta, z)$ :

  $
    h_1 = h_3 = 1 quad h_2 = r \
    va(dif M) = dif r va(u_r) + r dif theta va(u_theta) + dif z va(u_z)
  $

- En sphériques $(r, theta, phi)$ :

  $
    h_1 = 1 quad h_2 = r quad h_3 = r sin theta \
    va(dif M) = dif r va(u_r) + r dif theta va(u_theta) + r sin theta dif phi va(u_phi)
  $

#card("champ", "Champ scalaire, champ vectoriel", ("Physique.Analyse Vectorielle",))

Définitions d'un champ scalaire, champ vectoriel.

#answer

Un champ est une une grandeur dans un domaine $D$ de l'espace à un instant $t$, noté $va(G) (va(r), t)$.

Un champ peut être vectoriel ou scalaire selon si la grandeur qu'il représente l'est.

Un champ est dit

/ Uniforme: s'il est indépendant de $va(r)$.
/ Stationnaire ou permanant: s'il est indépendant de $t$.
/ Constant: S'il est les deux

- On appelle ligne de champ une courbe de l'espace qui est en tout points tengente au champ.

- Pour un champ $f(va(r), t)$, on appelle surface équi-$f$ une surface où $f$ est uniforme.

#card("grad", "Gradient d'un champ scalaire", ("Physique.Analyse Vectorielle",))

Définition du gradient d'un champ scalaire.

#answer

Pour un champ scalaire $f(va(r), t)$. On définit le gradient de $f$, noté $va("grad") f$ ou $grad f$ afin que

$
  dif f = grad f dprod va(dif M)
$

*En coordonées cartésiennes*

$
  va("grad") f = grad f = pdv(f, x) va(u_x) + pdv(f, y) va(u_y) + pdv(f, z) va(u_z)
$

Car

$
  va(dif M) = dif x va(u_x) + dif y va(u_y) + dif z va(u_z) \
$
$
  dif f &= pdv(f,x) dif x + pdv(f, y) dif y + pdv(f, z) dif z \
  &= grad f dprod va(dif M)
$

*En général*

$
  grad f = 1/h_1 pdv(f, q_1) va(e_1) + 1/h_2 pdv(f, q_2) va(e_2) + 1/h_3 pdv(f, q_3) va(e_3)
$

*Cas particulier*

- En sphérique : $grad 1/r = - 1 / r^2 va(u_r)$ 

- En sphérique : $grad r^2 = 2 r va(u_r)$

#card("flux", "Flux au travers d'une surface", ("Physique.Analyse Vectorielle",))

Définition du flux au travers d'une surface.

#answer

On considère une fonction vectorielle $va(F)(q_1, q_2, q_3)$

Pour une surface
- Fermée : on l'oriente de l'intérieur vers l'extérieur par convention.

- Ouverte : on oriente le coutour sur lequel elle s'appuis et on applique la règle de la main droite.

Le flux $Phi$ au travers de la surface $S$ est
$
  dif Phi = va(F) dprod va(dif S) \
  Phi = integral.surf_S va(F) dprod va(dif S)
$

#card("div", "Divergence d'un champ vectoriel", ("Physique.Analyse Vectorielle",))

Définition de la divergence d'un champ vectoriel.

#answer

La divergence d'un champ de vecteur représente à quelle point le champ diverge ou converge en ce points. On écrit $"div" va(F)$ ou $div va(F)$.

$
div va(F) > 0 quad quad
mat(delim: #none, #lq.diagram(
  width: _sizes.text * 6,
  height: _sizes.text * 6,
  xaxis: (ticks: none),
  yaxis: (ticks: none),
  lq.quiver(
    lq.arange(-2, 3),
    lq.arange(-2, 3),
    (x, y) => (x, y)
  )
)) \
div va(F) < 0 quad quad
mat(delim: #none, #lq.diagram(
  width: _sizes.text * 6,
  height: _sizes.text * 6,
  xaxis: (ticks: none),
  yaxis: (ticks: none),
  lq.quiver(
    lq.arange(-2, 3),
    lq.arange(-2, 3),
    (x, y) => (-x, -y)
  )
))
$

Son expression est

$
  div va(F) = 1 / (h_1 h_2 h_3) &[ pdv(, q_1)(h_2 h_3 F_q_1) \
  &+ pdv(,q_2) (h_1 h_3 F_q_2) \
  &+ pdv(,q_3) (h_1 h_2 F_q_3) ]
$

En cartésiennes

$
  div va(F) = pdv(F_x, x) + pdv(F_y, y) + pdv(F_z, z)
$

Cas particuliers

- En cylindrique : $div va(u_r) / r = 0$ (sauf en 0)

- En sphérique : $div va(u_r) / r^2 = 0$ (sauf en 0)

- $div va(r) = dim E$

#card("greenost", "Théorème de Green-Ostrogradski", ("Physique.Analyse Vectorielle",))

Énoncé du théorème de Green-Ostrogradski.

#answer

Pour un champ vectoriel $va(F)$ et une surface fermée $S$ qui délimite un volume $V$, on a
$
  Phi = integral.surf_S va(F) dprod va(dif S) = integral.triple_V div F dif tau
$

#card("circ", "Circulation dans un champ de vecteur", ("Physique.Analyse Vectorielle",))

Définition de la circulation dans un champ de vecteurs.

#answer

Pour $C$ un coutour orienté

#align(center, {cetz.canvas(length: 1.5em, {
  import cetz.draw: *

  hobby((0, 0), (0, 2), (2, 2), (4, 2), (2, -2), (0, 0))
  line((3.2, 2.1), (5, 2.4), mark: (end: ">"), stroke: blue + 2pt, fill: blue)
  content((rel: (-1, 0.4)), $text(fill: #blue, va(dif l))$)
})})

On définit la circulation du champ $va(F)$ sur $C$ comme

$
  dif cal(C) = va(F) dprod va(dif l) \
  cal(C) = integral_cal(C) va(F) dprod va(dif l)
$

#card("rot", "Rotationnel d'un champ de vecteur", ("Physique.Analyse Vectorielle",))

Définition du rotationnel d'un champ de vecteur.

#answer

// TODO: More

$
  va("rot") space va(F) &= curl va(F) \
  &= vec(1/(h_2 h_3) [pdv((h_3 F_q_3), q_2) - pdv((h_2 F_q_2), q_3)], 1 / (h_3 h_1) [pdv((h_1 F_q_1), q_3) - pdv((h_3 F_q_3), q_1)], 1 / (h_1 h_2) [pdv((h_2 F_q_2), q_1) - pdv((h_1 F_q_1), q_2)])
$

En cartésienne

$
  curl va(F) &= vec(pdv(F_z, y) - pdv(F_y, z), pdv(F_x, z) - pdv(F_z, x), pdv(F_y, x) - pdv(F_x, y)) \
$

#card("pvec", "Produit vectoriel", ("Physique",))

Expression du produit vectoriel.

#answer

$
  vec(a_x, a_y, a_z) cprod vec(b_x, b_y, b_z) &= vec(&mdet(a_y, b_y; a_z, b_z), -& mdet(a_x, b_y; a_z, b_z), &mdet(a_x, b_y; a_z, b_z)) \
  &= vec(a_y b_z - b_y a_z, a_z b_y - b_z a_y, a_x b_z - b_y a_z)
$

*Propriétés*

$
  va(u) cprod va(v) &= - (va(v) cprod va(u)) \
  (va(u) cprod va(v)) dprod va(w) &= [va(u), va(v), va(w)]  \
  &= [va(w), va(u), va(v)] \
  &= [va(v), va(w), va(v)] \
  va(u) cprod va(u) &= 0
$

#card("nabla", "Notation nabla", ("Physique.Analyse Vectorielle",))

Notation nabla.

#answer

En coordonées cartésiennes, on "définit"
$
  bold(nabla) = vec(pdv(,x), pdv(,y), pdv(,z))
$

Ainsi on retrouve les formules des opérateurs (toujours en cartésiennes)
$
  va("grad") space f = grad f \
  "div" va(F) = div va(F) \
  va("rot") space va(F) = curl va(F)
$

En général
$
  bold(nabla) = vec(1/h_1 pdv(,q_1), 1/h_2 pdv(,q_2), 1/h_3 pdv(,q_3))
$

#card("cc", "Champ à circulation conservative", ("Physique.Analyse Vectorielle",))

Définition de champ à circulation conservative.

#answer

Un champ $va(F)$ est dit à circulation conservative ssi pour toute courbe fermée $cal(C)$ on a
$
  integral.cont_cal(C) va(F) va(dif l) = 0
$
Ainsi la circulation de toute courbe passant par $A$ et $B$ deux points est la même, elle ne dépend pas du chemin choisis.

On peut alors définir le potentiel $V$, un champ scalaire tel que
$
  V(A) = V_A \
  V(B) = V_A + integral_A^B va(F) dprod va(dif l)
$

Entre $va(M)$ et $va(M) + va(dif M)$
$
  V(M) - V(M + dif M) = dif V(M) = va(F) dprod va(dif M)
$
Ainsi
$
  va(F) = grad V
$
De plus
$
  integral.cont_cal(C) va(F) dprod va(dif l) = integral.double_S (curl va(F)) dprod va(dif S) = 0 \
  => curl va(F) = 0 quad (curl (grad V) = 0)
$

#card("fc", "Champ à flux conservatif", ("Physique.Analyse Vectorielle",))

Définition d'un champ à flux conservatif.

#answer

Un champ $va(F)$ est dit à flux conservatif si pour toute surface $S$ fermée qui délimite un volume $V$.

$
  integral.surf_S va(F) dprod va(dif S) = 0
$

Ainsi

$
  integral.surf_S va(F) dprod va(dif S) = integral.triple_V div va(F) dif tau = 0 \
  => div va(F) = 0 quad (div (curl va(F)) = 0)
$

De plus on dispose de $va(A)$ (champ potentiel vecteur, H.P.) tel que
$
  va(F) = curl va(A)
$

#card("laplacien", "Laplacien", ("Physique.Analyse Vectorielle",))

Définition du laplacien d'un champ.

#answer

*Scalaire*

On appelle laplacien scalaire d'un champ scalaire $V$ le champ scalaire
$
  laplace V = div (grad V)
$
En cartésiennes :
$
  laplace V = pdv(V,x,2) + pdv(V,y,2) + pdv(V,z,2)
$
En général :
$
  laplace V = 1/(h_1 h_2 h_3) &[ pdv(,q_1) ((h_2 h_3) / h_1 pdv(V, q_1)) \
  &+ pdv(,q_2)((h_1 h_3) / h_2 pdv(V, q_2)) \
  &+ pdv(,q_3)((h_1 h_2) / h_3 pdv(V, q_3))]
$

*Vectoriel*

On appelle laplacien vectoriel d'un champ vectoriel $va(F)$ le champ vectoriel
$
  laplace va(F) = grad (div va(F)) - curl (curl va(F))
$
En cartésiennes :
$
  laplace va(F) &= vec(pdv(F_x,x,2) + pdv(F_x,y,2) + pdv(F_x,z,2), pdv(F_y,x,2) + pdv(F_y,y,2) + pdv(F_y,z,2), pdv(F_z,x,2) + pdv(F_z,y,2) + pdv(F_z,z,2)) \
  &= vec(laplace F_x, laplace F_y, laplace F_z)
$
]
#[

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

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

]
#[

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

#card("vpep", "Valeurs propres, espaces propres", ("Maths.Algèbre.Réduction",))

Définitions, caractérisation, démonstration autour des valeurs propres et des espaces propres.

#answer

Soit $u in cal(L)(E), lambda in KK$, il y a équivalence entre

+ $exists x_0 in E\\{0}, space u(x_0) = lambda x_0$

+ $ker (u - lambda id) != {0}$

+ $u - lambda id in.not "GL"(E)$

On dit alors que $lambda$ est une valeur propre de $u$, on appelle sous-espace propre de $u$ pour la valeur propre $lambda$
$
  E_lambda (u) = {x in E | u(x) = lambda x}
$

*Démonstration*

$
  exists x_0 in E \\ {0}, space u(x_0) = lambda x_0 \
  <=> exists x_0 in ker (u - lambda id) \\ {0} \
  <=> u - lambda id in.not "GL"(E) quad script(vec("dimension", "finie"))
$

#card("somdirsep", "Somme directe des sous-espaces propres", ("Maths.Algèbre.Réduction",))

Démonstration du fait que les sous-espaces propres d'un endomorphisme sont en somme directe.

#answer

Soit $u in cal(L)(E)$, $lambda_1, dots, lambda_p in KK$ ses valeurs propres deux à deux distinctes.

Soit $(x_1, dots, x_p) in product_(k = 1)^p E_(lambda_k) (u)$ tels que $sum_(k = 1)^p x_k = 0$.

Par recurrence on montre que pour tout $P(X) in KK [X]$.
$
  0 = sum_(k = 1)^p P(lambda_k) x_k
$

En particulier avec $P = L_i$ pour $i in [|1,n|]$ on a
$
  0 = sum_(k = 1)^p L_i (lambda_k) x_k = x_i
$

On appelle spèctre de $u$

$
  "Sp"(u) = {lambda in KK | lambda "valeur propre"}
$

Qui est finit ($abs("Sp"(u)) <= n = dim E$).

// TODO: Stabilité des sous espaces propres, ça sert a quoique que ce soit ? I.5)

#card("polcar", "Polynôme caractèristique d'un endomorphisme", ("Maths.Algèbre.Réduction",))

Définitions, propriétés élémentaires et démonstrations autours du polynôme caractèristique d'un endomorphisme.

#answer

*Matrices*

Soit $A in M_n (KK)$, on définit le polynôme caractèristique de $A$ comme
$
  chi_A (X) = det(X I_n - A)
$
Et on a
$
  chi_A (X) = sum_(k = 0)^n a_k X^k
$
$
  a_n &= 1 quad & "("chi_A" unitaire)" \
  a_(n-1) &= - tr(A) \
  a_0 &= (-1)^n det(A)
$

*Endomorphismes*

Soit $u in cal(L)(E)$, $e$ base de $E$, $A = cal(M)_e (u)$. On définit
$
  chi_u (X) = chi_A (X)
$
Ceci ne dépend pas de la base $e$ choisie.

De plus
$
  "Sp"(u) = Z_KK (chi_u)
$

*Démonstration*

$
  chi_A (X) = sum_(sigma in frak(S)_n) epsilon(sigma) underbrace(product_(j = 1)^n (X delta_(sigma(j) j) - A_(sigma(j) j)), P_sigma (X))
$

Pour tout $sigma in frak(S)_n$, $P_sigma in KK_n [X]$ donc $chi_A in KK_n [X]$. De plus
$
deg (P_sigma) = abs({k in [|1, n|] | sigma(k) = k}) \
deg (P_sigma) = n <=> sigma = id
$
Donc $deg chi_A = n$ et $"cd" chi_A = 1$.

Si $sigma != id, space deg (P_sigma) <= n - 2$, donc $a_(n-1)$ est le terme en $X^(n-1)$ de $P_id$.
$
  P_id = product_(j = 1)^n (X - A_(j j)) \
  a_(n-1) = - sum_(j = 1)^n A_(j j) = - tr (A)
$
$
  a_0 &= chi_A (0) = det(0 - A) \ &= (-1)^n det(A)
$

Soient $e, e'$ deux bases de $E$, $A = cal(M)_e (u), A' = cal(M)_e' (u), P = P_(e'->e)$.

$
  A' = P A P^(-1)
$
$
  chi_A' (X) &= det(X I_n - A') \
  &= det(X P I_n P^(-1) - P A P^(-1)) \
  &= det(P) det(X I_n - A) det(P^(-1)) \
  &= chi_A (X)
$

#card("multvp", "Multiplicités d'une valeur propre", ("Maths.Algèbre.Réduction",))

Définitions des multiplicités d'une valeur propre.

#answer

Soit $lambda in KK$ une valeur propre de l'endomorphisme $u$.

- On appelle multiplicité algébrique ($m_lambda$), ou juste multiplicité de $lambda$ sa multiplicité en tant que racine de $chi_u$.

- On appelle multiplicité géométrique de $lambda$ la dimension de son espace propre.

On a toujours

$
  dim E_lambda (u) <= m_lambda
$

*Démonstration*

Soit $(e_1, dots, e_d)$ base de $E_lambda$ complété en $e = (e_1, dots, e_n)$ base de $E$.

$
  cal(M)_e (u) = mat(augment: #("hline": 1, "vline": 1), lambda I_d, B; 0, C) \
$
$
  chi_u &= chi_(cal(M)_e (u)) \
  &= mat(delim: "|", augment: #("hline": 1, "vline": 1), (X - lambda) I_d, -B; 0, X I_(n - d) - C) \
  &= (X-lambda)^d chi_C (X)
$

#card("proppolcaran", "Propriétés diverses du polynôme caractèristique", ("Maths.Algèbre.Réduction",))

Cas particuliers de calculs du polynôme caractèristique, et lien avec les endomorphisme induit.

#answer

- Pour tout $T in T_n (KK)$ #h(1fr)

  $
    chi_T = product_(k = 1)^n T_(k k)
  $

- Pour tout $M = mat(augment: #("hline": 1, "vline": 1), A, B; 0, C) in M_n (KK), A in M_r (KK), C in M_(n - r) (KK), B in M_(r,n-r) (KK)$

  $
    chi_M (X) = chi_A (X) chi_C (X)
  $

- Soient $u in cal(L)(E)$, $F$ sev stable par $u$, $accent(u,~)$ l'endomorphisme induit par $u$ sur $F$, on a toujours
  $
    chi_accent(u,~) | chi_u
  $

*Démonstration*

- L'écrire.

- L'écrire.

- Soit $e = (e_1, dots, e_n)$ base de $F$ complété en base de $E$.

  $
  cal(M)_e (u) = mat(augment: #("hline": 1, "vline": 1), A, B; 0, C)
  $

  Avec $A = cal(M)_accent(e,~) (accent(u,~))$.

#card("diag", "Diagonalisabilité", ("Maths.Algèbre.Réduction",))

Définition et premier critère de diagonalisabilité.

#answer

On dit que $u in cal(L)(E)$ est diagonalisable s'il existe une base $e$ de $E$ tel que $cal(M)_e (u)$ est diagonale.

Une tel base est par définition formée de vecteurs propres de $u$.

De plus
$
  u "diagonalisable" \
  <=> E = plus.o.big_(lambda in "Sp"(u)) E_lambda (u) \
  <=> sum_(lambda in "Sp"(u)) dim E_lambda (u) = dim E
$

En particulier
- Les homothéties sont diagonales dans toutes les bases

- Les projecteurs sont diagonalisables :
  $
    underbrace(ker (p - id), E_1 (p)) plus.o underbrace(ker p, E_0 (p)) = E
  $

- Les symétries sont diagonalisables :
  $
    underbrace(ker (s - id), E_1 (s)) plus.o underbrace(ker s + id, E_(-1) (s)) = E
  $

#card("autcrit", "Autre critère de diagonalisabilité", ("Maths.Algèbre.Réduction",))

Énoncer du critère de diagonalisabilité sur $chi_u$ et les multiplicités.

#answer

Soit $u in cal(L)(E)$
$
  u "diagonalisable" \
  <=> cases(space chi_u "scindé", space forall lambda in "Sp"(u)\, dim E_lambda (u) = m_lambda)
$
Où $m_lambda$ est la multiplicité (algébrique) de $lambda$.

Ainsi car $dim E_lambda (u) >= 1$ pour tout $lambda in "Sp"(u)$,

$
  chi_u "SARS" => u "diagonalisable"
$

*Démonstration*

- Supposons $u$ diagonalisable, notons $e$ la base qui le diagonalise.

  $
  cal(M)_e (u) = dmat(alpha_1, dots.down, alpha_n)
  $
  Donc $chi_u$ est scindé
  $
    chi_u (X) &= product_(k = 1)^n (X- alpha_k) \
    &= product_(k = 1)^p (X - lambda_k)^(m_lambda_k)
  $
  Ainsi
  $
    deg chi_u &= n = sum_(k = 1)^p m_lambda_k \
    n = sum_(k=1)^p m_lambda_k &>= sum_(k = 1)^p dim E_lambda_k = n
  $

- Supposons $chi_u$ scindé et pour tout $lambda in "Sp"(u), dim E_lambda (u) = m_lambda$.

  $
    chi_u = underbrace(product_(lambda in "Sp"(u)) (X - lambda)^(m_lambda), deg = n) \
    n = sum_(lambda in "Sp"(u)) m_lambda = sum_(lambda in "Sp"(u)) E_lambda (u)
  $

  Donc $u$ est diagonalisable.

#card("trigonalisabilite", "Trigonalisabilité", ("Maths.Algèbre.Réduction",))

Définition et premier critères de la trigonalisabilité.

#answer

Soit $u in cal(L)(E)$. On dit que $u$ est trigonalisable s'il existe une base $e = (e_1, dots, e_n)$ de $E$ tel que $cal(M)_e (u) in T_n^+ (KK)$

Dans ce cas
- $u(e_1) = t_(1 1) e_1$, donc $e_1$ est un vecteur propre de $u$.

- Notons $F_k = "Vect"(e_1, dots, e_k)$ le drapeau. #h(1fr)
  $
  forall k in [|1, n|], u(F_k) subset F_k
  $

- $chi_u (X) = product_(k = 1)^n (X - t_(k k)) space$ scindé.

La réciproque est aussi vraie : $chi_u "scindé" => u "trigonalisable"$.

Si $F != {0}$ est un sev stable par $u$ et $u$ trigonalisable, alors $accent(u,~)$ (induit par $u$ sur $F$) est trigonalisable (car $chi_accent(u,~) | chi_u$ scindé).

Si $KK$ est algébriquement clos, toute matrice ou endomorphisme est trigonalisable.

*Démonstration*

Par récurrence sur $n = dim E$.

Toute matrice de taille $1$ est supérieure.

Supposons pour un $n in NN$
$
  forall A in M_n (KK), \ chi_A "scindé" => A "trigonalisable"
$

Soit $A in M_(n+1) (KK)$ tel que $chi_A$ scindé.

$chi_A$ a au moins une racine, donc $A$ admet une valeur propre $lambda$.

On dispose de $X_0 in KK^(n+1)$ tel que 
$
A X_0 = lambda X_0
$
Ainsi on peut construire la base $e' = (X_0, dots, X_n)$ de $KK^(n+1)$. Notons $P = P_("can" -> e')$.

$
  A = P mat(augment: #("vline": 1, "hline": 1), lambda, *, dots.c, *; 0; dots.v,,accent(A,~);0) P^(-1)
$

Avec $accent(A,~) in M_n (KK)$ et $chi_A = chi_accent(A,~) (X - lambda)$ d'où $chi_accent(A,~)$ scindé.

Par hypothèse de récurrence $accent(A,~)$ est trigonalisable et on peut donc construire $P_0 in "GL"_(n+1) (KK)$ tel que

$
  A = P mat(alpha_1,,*;,dots.down;,,alpha_(n+1)) P^(-1)
$

#card("carnilp", "Caractèrisation des endomorphismes nilpotents", ("Maths.Algèbre.Réduction",))

Caractèrisation des endomorphisme nilpotents.

#answer

Soit $u in cal(L)(E)$, il y a équivalence entre

+ $u$ nilpotent

+ $u$ trigonalisable en une matrice strictement supérieure.

+ $u$ trigonalisable et $"Sp"(u) = {0}$

+ $chi_u = X^n$

*Démonstration*

- (4 $=>$ 3) $chi_u = X^n$ est scindé donc $u$ est trigonalisable et $"Sp"(u) = Z(X^n) = {0}$.

- (3 $<=>$ 2) Évident.

- (3 $=>$ 4) On dispose de $e$ base de $E$ tel que

  $
    cal(M)_e (u) = mat(0,,*;,dots.down;,,0) \
    "Donc" space chi_u = X^n
  $

- (2 $=>$ 1) On dispose de $e$ base de $E$ tel que $cal(M)_e (u) in T_n^(++) (KK)$, notons $F_k = "Vect"(e_1, dots, e_k)$.

  $
    u(F_k) subset.eq u(F_(k-1)) \
    u^n (F_n = E) subset.eq F_0 = { 0 } \
    u^n = 0
  $

- (1 $=>$ 2) $u$ est nilpotent d'indice $d$.

  $
    {0} subset.neq ker u subset.neq dots.c subset.neq ker u^d = E
  $

  Construisons une base adaptée

  $
    (overbrace(underbrace(e_1\, dots\, e_(i_1), "base de" ker u)\, dots\, e_(i_2), "base de" ker u^2), dots, e_(i_d))
  $

  Pour tout $x in ker u^k$ :
  $
  u(x) in ker u^(k-1)
  $
  Ainsi pour tout $k in [|1, n|]$ si $i_j + 1 <= k <= i_(j+1)$
  $
    e_k in ker u^j \
    u(e_k) in ker u^(j-1) \
    u(e_k) in "Vect"(e_1, dots, e_i_(j-1))
  $

#card("lienpolminpolcar", "Premier lien entre polynôme minimal et polynôme caractèristique", ("Maths.Algèbre.Réduction",))

Lien entre racines du polynôme minimal et celles du polynôme caractèristique.

#answer

Soit $u in cal(L)(E)$, $P in KK[X]$ annulateur de $u$.

$
  "Sp"(u) subset.eq Z_KK (P) \
  Z(chi_u) = "Sp"(u) = Z_KK (Pi_u)
$

*Démonstration*

- Soit $lambda in "Sp"(u)$ et $x in E_lambda (u) \\ {0}$ : #h(1fr)
  $
    P(X) = sum_(k = 0)^d a_k X^k \
  $
  $
    P(u)(x) &= sum_(k = 0)^d u^k (x) = sum_(k = 0)^d lambda^k x \
    &= P(lambda) x = 0
  $
  Or $x != 0$, donc $P(lambda) = 0$.

- $Pi_u$ annule $u$ d'où $"Sp"(u) subset.eq Z_KK (Pi_u)$

- Soit $lambda in KK$ racine de $Pi_u$

  $
    Pi_u = (X - lambda) Q(X) \
    0 = (u - lambda id) compose Q(u)
  $

  Donc $im Q(u) subset.eq ker (u - lambda id)$.

  Mais $Q(u) != 0$ car $Pi_u$ minimal, donc 
  $
  dim (im Q(u)) >= 1 \
  im Q(u) subset.eq ker (u - lambda id) = E_lambda (u) \
  lambda in "Sp"(u)
  $

#card("tdn", "Théorème des noyaux", ("Maths.Algèbre.Réduction",))

Énoncé et démonstrations du théorème des noyaux.

#answer

Soit $u in cal(L)(E)$ ($KK$-ev de dimension finie), $P in KK[X]$.

Si $P = product_(k = 1)^N P_k$ avec $P_1, dots, P_N$ deux à deux premiers entre eux, alors
$
  ker P(u) = plus.o.big_(k = 1)^N ker P_k (u)
$

Si de plus $P$ annule $u$ alors
$
  E = ker P(u) = plus.o.big_(k = 1)^N ker P_k (u) \
  cal(M)_e (u) = dmat(A_1,dots.down,A_N)
$
Où $e$ est la base construite par concaténation de bases des $ker P_k (u)$.

*Démonstration*

Par récurrence sur $N$.

Pour $P = P_1 P_2$ avec $P_1 and P_2 = 1$ :
$
  P_1 V_1 + P_2 V_2 = 1 \
  P_1 (u) compose V_1 (u) + P_2 (u) compose V_2 (u) = id quad (*)
$
En évaluant on trouve 
$
ker P_1 (u) inter ker P_2 (u) = {0}
$
De plus 
$
P_1 (u) compose P_2 (u) = P_2 (u) compose P_1 (u) = P(u) \
"Donc" space cases(space ker P_1 (u) subset.eq ker P(u), space ker P_2 (u) subset.eq ker P(u)) \
ker P_1 (u) plus.o ker P_2 (u) subset.eq ker P (u)
$

Soit $x in ker P(u)$, par $(*)$ on a
$
  x = underbrace(V_1 (u) compose P_1 (u) (x), x_2) + underbrace(V_2 (u) compose P_2 (u) (x), x_1)
$
$
  P_1 (u) (x_1) &= (P_1 V_2 P_2) (u) (x) \
  &= (V_1 P) (u) (x) \
  &= 0 \
  P_2 (u) (x_2) &= (P_2 V_1 P_1) (u) (x) \
  &= (V_2 P) (u) (x) \
  &= 0 \
$
$
x = underbrace(x_1, in ker P_1 (u)) + underbrace(x_2, in ker P_2 (u))
$
D'où $ker P(u) = ker P_1 (u) plus.o ker P_2 (u)$.

Supposons maintenant le résultat pour tout $P_1, dots, P_N$ respectant les conditions.

Soient $P = P_1 dots.c P_(N+1) in KK[X]$ avec $P_1, dots, P_(N+1)$ deux à deux premiers entre eux.

Donc $Q = P_1 P_2 dots.c P_N$ et $P_(N+1)$ sont premiers entre eux.

Ainsi 
$
ker P (u) &= ker (P_(N+1) Q) (u) \
&= underbrace(ker Q(u) plus.o ker P_(N+1) (u), "cas" N = 2) \
&= underbrace(plus.o.big_(k = 1)^N ker P_k (u) plus.o ker P_(N+1) (u), "H.R.") \
&= plus.o.big_(k = 1)^(N+1) ker P_k (u)
$

#card("projchelou", "Démonstration annexe du théorème des noyaux", ("Maths.Algèbre.Réduction",))

Démonstration secondaire du théorème des noyaux dans le cas d'un polynôme annulateur.

#answer

Soit $u in cal(L)(E)$.

On suppose $P = product_(k = 1)^N P_k$ annulateur de $u$, $P_1, dots, P_N$ premiers entre eux deux à deux. On pose
$
  Q_k = product_(i = 1 \ i != k)^N P_i
$
Qui sont premiers dans leur ensemble.
$
  sum_(k = 1)^N V_k Q_k = 1 \
  sum_(k = 1)^N underbrace(V_k (u) compose Q_k (u), Pi_k) = id quad (1)\
$
On remarque que
$
  P_k (u) compose Pi_k = (V_k P_k Q_k) (u) = (V_k P) (u) = 0 \
  "Donc" space im Pi_k subset.eq ker P_k (u)
$
Et pour $k != i, P | Q_i Q_k$ d'où
$
  P | (V_k P_k) (V_i P_i) \
  Pi_i compose Pi_k = 0
$
Donc par $(1)$
$
sum_(i = 1)^N Pi_k compose Pi_i = Pi_k compose Pi_k = Pi_k
$
Donc les $Pi_k$ sont des projecteurs.

Soit $x in ker P_k (u)$, pour tout $i != k$, $Pi_i (x) = 0$. Par $(1)$
$
  x = Pi_k (x) \
  x in im Pi_k
$
Ainsi
$
  ker P_k (u) = im Pi_k  \
  ker P_i (u) subset.eq ker Pi_k
$
Les $Pi_k$ projettent sur $ker P_k$.

*Théorème des noyaux*

Soient $(x_1, dots, x_N) in product_(k = 1)^N ker P_k (u)$ tels que $sum_(k = 1)^N x_k = 0$.

Pour tout $i in [|1, N|]$
$
  Pi_i (sum_(k = 1)^N x_k) = x_i = 0
$
Donc les $ker P_k (u) = im Pi_k$ sont en somme directe.

Soit $x in ker P(u) = E$, par $(1)$
$
  x = sum_(k = 1)^N Pi_k (x) in sum_(k = 1)^N ker P_k (u)
$
D'où
$
  E = plus.o.big_(k = 1)^N ker P_k (u)
$
Et de plus
$
  im Pi_k &= ker P_k (u) \
  ker Pi_k &= plus.o.big_(i = 1 \ i != k)^N ker P_i (u) \
  Pi_k &in KK[u]
$

#card("crtidiag", "Critère de Diagonalisabilité", ("Maths.Algèbre.Réduction",))

Démonstration d'une CNS de diagonalisabilité.

#answer

Soit $u in cal(L)(E)$, il y a équivalence entre

+ $u$ diagonalisable.

+ $u$ annule un polynôme SARS.

+ $Pi_u$ est SARS

*Démonstration*

- (2 $<=>$ 3) #h(1fr)
  $
    exists P in KK[X], space P "SARS et" P(u) = 0 \
    <=> exists P in KK[X], space P "SARS et" Pi_u | P \ 
    <=> Pi_u "SARS"
  $

- (3 $=>$ 1) $Pi_u$ SARS donc
  $
    Pi_u = product_(lambda in "Sp"(u))^N (X - lambda)
  $
  Par le TDN
  $
    E &= plus.o.big_(lambda in "Sp"(u)) ker (u - lambda id) \
    &= plus.o.big_(lambda in "Sp"(u)) E_lambda (u)
  $
  Donc $u$ diagonalisable.

- (1 $=>$ 3) $u$ diagonalisable
  $
    cal(M)_e (u) &= underbrace(inline(dmat(lambda_1, dots.down, lambda_1, dots.down, lambda_n, dots.down, lambda_n)), M) \
    P(X) &= product_(k = 1)^N (X - lambda_k) space "SARS" \
    P(M) &= inline(dmat(P(lambda_1), dots.down, P(lambda_1), dots.down, P(lambda_n), dots.down, P(lambda_n))) \
    &= 0
  $
  Donc $Pi_u | P$ SARS.

#card("diaginduit", "Diagonalisabilité d'un endomorphisme induit", ("Maths.Algèbre.Réduction",))

Diagonalisabilité d'un endomorphisme induit.

#answer

Soit $u in cal(L)(E)$, $F$ un sev stable par $u$.

Notons $accent(u,~)$ l'endomorphisme induit par $u$ sur $F$.

- $Pi_accent(u,~) | Pi_u$

- Si $u$ diagonalisable, alors $accent(u,~)$ aussi.

*Démonstration*

- $Pi_u (accent(u,~)) = 0$ donc $Pi_accent(u,~) | Pi_u$.

- Si $u$ diagonalisable, $Pi_u$ est SARS, donc $Pi_accent(u,~)$ aussi (car divise) donc $accent(u,~)$ est diagonalisable.

// TODO: M127 Dénombrement

#card("seceng", "Sous-espaces cycliques", ("Maths.Algèbre.Réduction",))

Définition de sous-espace cyclique et base associé.

#answer

Pour un $u in cal(L)(E)$ et $x_0 in E$ on appelle sous-espace cyclique engendré par $x_0$ (pour $u$)
$
  F_(x_0) = "Vect"(u^k (x_0))_(k in NN)
$
Cet espace admet comme base
$
  (x_0, u(x_0), dots, u^(d - 1) (x_0))
$
Où $d = deg Pi_(u,x_0)$ le polynôme minimal ponctuel, l'unique polynôme unitaire minimal tel que
$
  "Pour " theta_(x_0) : func(KK[X], E, P, P(u) (x_0)) \ \
  ker theta_(x_0) = Pi_(u,x_0) KK[X]
$

*Démonstration*

$theta_(x_0) in cal(L)(E)$, donc $ker theta_(x_0)$ est un sev, donc un sous-groupe de $(KK[X], +)$.

Soit $P in ker theta_x_0, Q in KK[X]$
$
  theta_x_0 (Q P) &= Q(u) (P(u) (x_0)) \ &= Q(u) (0) = 0
$
Donc $ker theta_x_0$ est un idéal de $KK[X]$, qui est principal d'où $Pi_(u,x_0)$ existe. Notons $d_x_0 = deg Pi_(u,x_0)$.

Par existance et unicité de la division euclidienne on a
$
  KK[X] = KK_(d_x_0 - 1) [X] plus.o ker theta_x_0
$
Donc $evaluated(theta_x_0)_(KK_(d_x_0 -1) [X])$ isomorphisme de $KK_(d_x_0 - 1) [X] -> im theta_x_0 = F_x_0$.

Donc $F_x_0$ a pour base
$
  (theta_x_0 (1), theta_x_0 (X), dots, theta_x_0 (X^(d_x_0 - 1))) \
  = (x_0, u(x_0), dots, u^(d - 1) (x_0))
$

#card("endocycl", "Endomorphismes cycliques", ("Maths.Algèbre.Réduction",))

Définition, propriétés, démonstration autour des endomorphismes cycliques.

#answer

Soit $u in cal(L)(E)$, on dit que $u$ est cyclique si l'une des conditions équivalentes suivantes est vérifiée

+ $exists x_0 in E, space "Vect"(u^k (x_0))_(k in NN) = E$.

+ $exists x_0 in E, space (x_0, u(x_0), dots, u^(n-1) (x_0))$ base de $E$.

*Propriétés en vrac (sans démonstration)*

- Si $u$ cyclique, tout endomorphisme induit l'est aussi.

- Si $u$ cyclique, $u$ admet un nombre fini de sev stables.
// TODO: Reprendre démo M140
- Si $KK$ est infini et $u$ admet un nombre fini de sev stables, alors $u$ est cyclique.

*Démonstration équivalence*

- (2 $=>$ 1) Évident.

- (1 $=>$ 2) $F_x_0 = "Vect"(u^k (x_0))_(k in NN)$ est les sous-espace engendré par $x_0$ pour $u$, donc

  $
    (x_0, u(x_0), dots, u^(d-1) (x_0))
  $
  Où $d = deg Pi_(u,x_0)$ en est une base.

  Or $F_x_0 = E$ par hypothèse, donc $dim F_x_0 = n$ et $d = n$.

#card("cycmat", "Vision matricielle de la cyclicité", ("Maths.Algèbre.Réduction",))

Lien entre endomorphisme cyclique et matrices de compagnon.

#answer

Soit $u in cal(L)(E)$, $u$ est cyclique ss'il existe une base $e$ de $E$ et $P$ unitaire de degré $n$ tel que $cal(M)_e (u) = C_P$.

Dans ce cas $Pi_u = P$.

*Démonstration*

Soit $u in cal(L)(E)$ cyclique pour $x_0 in E$. Notons $e = (x_0, u(x_0), dots, u^(n-1) (x_0))$ la base associé.

On dispose alors de $a_0, dots, a_(n-1) in KK$ tels que
$
  u^n (x_0) - sum_(k = 0)^(n-1) a_k u^k (x_0) = 0 \
  P = X^n - sum_(k = 0)^(n - 1) a_k X^k \
  P(u) (x_0) = 0
$
Et alors
$
  cal(M)_e (u) &= 
    mat(delim: #none, #{
      diagram(
      spacing: 0pt,
      cell-size: 0pt,
      $
        node(enclose: #("tl", "bl"), lr(size: #800%, \())
        node(enclose: #("tr", "br"), lr(size: #800%, \))) \
        && u(x_0) edge("rr", "..") & #h(0.6em) & u^n (x_0) & \
        x_0 & node(name: "tl") & 0 edge("ddr", "..") && a_0 & node(name: "tr") \
        u(x_0) edge("dd", "..") && 1 edge("ddr", "..") && a_1 edge("dd", "..") & \
        &&& 0 && \
        u^(n-1) (x_0) & node(name: "bl") && 1 & a_(n-1) & node(name: "br") \
      $
    )
  }) \
  &= C_P
$

Réciproquement :

Soit $u in cal(L)(E)$ et $e = (e_1, dots, e_n)$ base de $E$ tel que

$
  cal(M)_e (u) = mat(augment: #3,
    0,,,a_0;
    1,dots.down,,a_1;
    ,dots.down,0, dots.v;
    ,,1, a_(n-1)
  )
$

Alors pour $k in [|1, n-1|]$
$
  u(e_k) = u(e_(k+1)) \
  "Donc" e = (e_1, u(e_1), dots, u^(n-1)(e_1))
$
Donc $u$ est cyclique.

Ainsi :
$
  P(u) (x_0) = u^n (x_0) - underbrace(sum_(k = 0)^(n-1) a_k u^k (x_0), u^n (x_0)) = 0 \
$
Donc pour tout $m in [|0,n-1|]$
$
  P(u)  (u^m (x_0)) = u^m (P(u) (x_0)) = 0
$
Ainsi $P(u)$ annule une base, d'où $Pi_u | P$.

Or $deg Pi_(u,x_0) = n$ car $u$ cyclique et $Pi_(u,x_0) | Pi_u$, donc 
$
n <= deg Pi_u <= deg P = n
$
Et comme $Pi_u$ et $P$ sont unitaires
$
  Pi_u = P
$

#card("matcomp", "Matrice compagnon", ("Maths.Algèbre.Réduction",))

Définition de matrice compagnon.

#answer

Soit $P = X^d sum_(k = 0)^(d-1) a_k X^k in KK[X]$ un polynôme unitaire. On appelle matrice compagnon de $P$ la matrice
$
  C_P = mat(augment: #3,
    0,,,-a_0;
    1,dots.down,,-a_1;
    ,dots.down,0, dots.v;
    ,,1, -a_(d-1)
  )
$
Ainsi (en développant selon la dernière colonne)
$
  chi_C_P (X) = P(X)
$

#card("exx0tqpiux0egpiu", "Exercice : vecteur dont le polynôme minimal ponctuel est le polynôme minimal", ("Maths.Exercice.Réduction",))

Soit $u in cal(L)(E)$, montrer qu'il existe $x in E$ tel que $Pi_(u,x) = Pi_u$.

En déduire que $u$ cyclique ssi $deg Pi_u = n$.

#answer

Soit $u in cal(L)(e)$.

On pose
$
  Pi_u = product_(k = 1)^N P_k^d_k
$
Avec $P_1, dots, P_N$ irréductibles deux à deux distincts.

*Démonstration $KK$ quelconque*

Par le TDN
$
  E = plus.o.big_(k = 1)^N ker underbrace(P_k^d_k (u), F_k) \
  ker P_k^(d_k - 1) (u) subset.eq ker P_k^d_k (u) = F_k
$

Supposons par l'absurde qu'on ai égalité pour un $k$.
$
  E &= plus.o.big_(j != k) ker P_j^d_j (u) plus.o ker P_k^(d_k - 1) (u) \
  &= ker underbrace(( P_k^(d_k - 1) product_(j != k) P_j^d_j), "ne peut annuler" u \ "car" Pi_u "minimal") (u)
$
Donc $ker P_k^(d_k - 1) (u) subset.neq ker P_k^d_k (u)$.

Pour tout $k in [|1, N|]$ on dispose de 
$
x_k in F_k \\ ker P_k^(d_k - 1) (u) \
"Donc" cases(space P_k^d_k (u) (x_k) = 0, space P_k^(d_k - 1) (x_k) != 0) \
"Donc" cases(space Pi_(u,x_k) | P_k^d_k, space Pi_(u,x_k) divides.not P_k^(d_k - 1) ) \
"Donc" underbrace(Pi_(u, x_k) = P_k^(d_k), "car" P_k "irréductible")
$
On pose $x = sum_(k = 1)^N x_k$, alors pour tout $P in Pi_(u,x) KK[X]$
$
  P(u) (x) = 0 \
  <=> sum_(k = 1)^N P(u) (x_k) = 0 \
  underbrace(<=> forall k in [|1, N|]\, space P(u) (x_k) = 0, "somme directe") \
  <=> forall k in [|1, N|], space P_k^d_k = Pi_(u,x_k) | P \
  <=> product_(k = 1)^N P_k^d_k = Pi_u | P \
  <=> P in Pi_u KK[X]
$
Donc $Pi_u | Pi_(u,x) | Pi_u$.

*Démonstration $KK$ infini*

Pour tout $x in E$, $Pi_(u,x) | Pi_u$ donc
$
  Pi_(u,x) in D = Set("Diviseurs unitaires de" Pi_u) \
  abs(D) = product_(k = 1)^N (d_k + 1) \
  D' = Set(Pi_(u,y), y in E) subset.eq D
$
Et $x in ker Pi_(u,x) (u)$ d'où
$
  E &= union.big_(x in E) ker Pi_(u,x) (u) \
  &= underbrace(union.big_(P in D') ker P(u), "union finie de sev")
$
Donc on dipose de $Q = Pi_(u,y) in D'$ tel que (cf. exercice union de sev dans un corps infini)
$
  E = ker Q(u)
$
Par minimalité de $Pi_u$, $Pi_(u,y) = Pi_u$.

*CNS de cyclicité*

On sait que si $u$ cyclique, alors on dispose de $e$ base de $E$ tel que 
$
cal(M)_e (u) = C_(Pi_u)
$
Avec $Pi_u in KK[X]$ unitaire de degré $n$.

Supposons maintenant que $deg Pi_u = n$. 

On dispose de $x_0 in E$ tel que $Pi_(u,x_0) = Pi_u$, d'où 
$
deg Pi_(u,x_0) = n = dim underbrace("Vect"(u^k (x_0))_(k in NN), F_x_0)
$ 
D'où $F_x_0 = E$ et $u$ cyclique.

#card("cayleyhamilton", "Théorème de Cayley-Hamilton", ("Maths.Algèbre.Réduction",))

Énoncé et démonstration du théorème de Cayley-Hamilton.

#answer

Soit $u in cal(L)(E)$, on a $chi_u (u) = 0$ c'est à dire $Pi_u | chi_u$.

*Démonstration*

Soit $x_0 in E\\{0}$, on veut montrer $chi_u (u) (x_0) = 0$.

On pose $F_x_0 = "Vect"(u^k (x_0))_(k in NN)$ sev de $E$ stable par $u$.

Soit $accent(u,~)$ endomorphisme induit par $u$ sur $F_x_0$, qui est donc cyclique.

Soit $d in NN$ tel que 
$
e_0 = (x_0, u(x_0), dots, u^(d-1) (x_0))
$
Soit une base de $F_x_0$.
$
  cal(M)_e_0 (accent(u,~)) = C_P = mat(augment: #3, 0,,,a_0;1,dots.down,,dots.v;,dots.down,0,a_(n-2);,,1,a_(n-1))
$
Où 
$
  accent(u,~)^d (x_0) = u^d (x_0) = sum_(k = 0)^(d-1) a_k u^k (x_0) \
  P(X) = X^d - sum_(k = 0)^(d-1) a_k X^k \
  P(u)(x_0) = 0
$

Or $P = chi_C_P = chi_accent(u,~) | chi_u$ donc
$
  chi_u (u) (x_0) = Q(u) (P(u) (x_0)) = 0
$

#card("expropcycl", "Exercice : propriétés des endomorphismes cycliques", ("Maths.Exercice.Réduction",))

+ Soit $u in cal(L)(E)$ diagonalisable, CNS pour $u$ cyclique.

+ Soit $u in cal(L)(E)$ nilpotent, CNS pour $u$ cyclique.

+ Soit $u in cal(L)(E)$ cyclique, montrer que pour tout $lambda in "Sp"(u)$, $dim E_lambda (u) = 1$.

+ Soit $u in cal(L)(E)$ cyclique, montrer que $"Com" u = KK[u]$.

#answer

+ Soit $u in cal(L)(E)$ diagonalisable.

  $
    Pi_u = product_(k = 1)^N (X - lambda_k)
  $
  Où les $lambda_1, dots, lambda_N$ sont deux à deux distincts ($Pi_u$ SARS).

  $u$ cyclique ssi $N = n = dim E$.

  - Si $u$ cyclique, $deg Pi_u = n = N$.

  - Si $deg Pi_u = n$

    Soit $e = (e_1, dots, e_n)$ base de vecteurs propres associés aux $lambda_1, dots, lambda_n$.

    Posons $x = sum_(k = 1)^n e_k$.

    $
    cal(M)_e (x_0, u(x_0), dots, u^(n-1) (x_0)) \
    = mat(1, lambda_1, lambda_1^2, dots.c, lambda_1^n; dots.v, dots.v, dots.v, dots.down, dots.v; 1, lambda_n, lambda_n^2, dots.c, lambda_n^n)
    $

    Matrice de Vandermonde inversible, d'où $(x_0, u(x_0), dots, u^(n-1) (x_0))$ base.

+ Soit $u in cal(L)(E)$ nilpotent d'indice $q$.

  $
    Pi_u = X^q
  $

  - Si $u$ cyclique, alors $deg Pi_u = q = n$.

  - Si $q = n$, $u^(n - 1) != 0$, donc on dispose de $x_0 in E$ tel que $u^(n - 1) (x_0) != 0$.

    Et $(x_0, u(x_0), dots, u^(n-1) (x_0))$ est libre et donc une base.

    (En évaluant $u^i (sum_(k = 0)^(n-1) lambda_k u^k (x_0))$).

+ Soit $u in cal(L)(E)$ cyclique, donc on dispose de $e$ base de $E$ tel que pour $lambda in "Sp"(u)$

  $
    cal(M)_e (u - lambda id) = mat(augment: #("hline": 1, "vline": 4), -lambda,,,,a_0;1,-lambda,,,a_2;,1,dots.down,,dots.v;,,dots.down,-lambda,a_(n-2);,,,1,a_(n-1) - lambda)
  $
  Dont le quadrant inférieur gauche est une sous-matrice inversible de taille $n - 1$.
  $
    "rg" (u - lambda id) >= n - 1 \
    1 <= dim E_lambda (u) = dim ker (u - lambda id) <= 1
  $

+ Soit $u in cal(L)(E)$ cyclique. On dispose de $x_0 in E$ tel que
  $
    (x_0, u(x_0), dots, u^(n-1) (x_0))
  $
  Est une base.

  On a déjà $KK[u] subset.eq "Com"(u)$. 

  Soit $v in "Com"(u)$. On dispose de $alpha_0, dots, alpha_(n-1) in KK$ tels que
  $
    v(x_0) = sum_(k = 0)^(n-1) alpha_k u^k (x_0)
  $
  Soit $m in [|0, n - 1|]$
  $
    v(u^m (x_0)) &= u^m (v(x_0)) \ 
    &= u^m (sum_(k = 0)^(n - 1) alpha_k u^k (x_0)) \
    &= sum_(k = 0)^(n - 1) alpha_k u^k (u^m (x_0))
  $
  Donc $v$ et $sum_(k = 0)^(n-1) alpha_k u^k$ coincident sur une base, d'où $v in KK[u]$.

#card("polmintz", "Critère de trigonalisabilité sur le polynôme minimal", ("Maths.Algèbre.Réduction",))

Soit $u in cal(L)(E)$, CNS de trigonalisabilité sur $Pi_u$.

#answer

Soit $u in cal(L)(E)$, $u$ est trigonalisable ssi $Pi_u$ scindé.

*Démonstration*

- Supposons $u$ trigonalisable, donc $chi_u$ est scindé or $Pi_u | chi_u$ donc $Pi_u$ est scindé.

- Supposons $Pi_u$ scindé.
  $
    Pi_u = product_(k = 1)^N (X - lambda_k)^(d_k)
  $
  Avec $lambda_1, dots, lambda_N in KK$ deux à deux distincts.

  Par le TDN
  $
    E = plus.o.big_(k = 1)^N underbrace(ker (u - lambda_k id)^(d_k), F_k)
  $
  Pour $k$ fixé, $F_k$ est stable par $u$ et $u - lambda id$, posons $u_k$ induit par $u$ sur $F_k$.

  $u_k - lambda_k id$ est nilpotent, donc on dispose de $e_k$ base de $F_k$ tel que
  $
    cal(M)_(e_k) (u_k - lambda_k id) = mat(0,,*;,dots.down;,,0) \
    cal(M)_(e_k) (u_k) = A_k = mat(lambda_k,,*;,dots.down;,,lambda_k)
  $

  Notons $e$ la base concatenant les bases $e_1, dots, e_N$.
  $
    cal(M)_e (u) &= dmat(A_1,dots.down,A_N) \
  $
  Où les $A_1, dots A_N$ sont triangulaires.

- (Autre méthode) Par récurrence sur $n$.

  Cas $n = 1$ évident.

  Supposons le résultat pour $n in NN$. Soit $u in cal(L)(E)$ où $dim E = n + 1$ et $Pi_u$ scindé.

  $Pi_u$ admet au moins une racine $lambda$, on dispose donc de $x in E$ vecteur propre associé.

  On forme la base $(lambda, e_1, dots, e_(n-1))$ de $E$.
  $
    cal(M)_e (u) = A = mat(augment: #("hline": 1, "vline": 1), lambda,*,dots.c,*;0;dots.v,,A_1;0)
  $
  Or
  $
    0 &= cal(M)_e (Pi_u (u)) = Pi_u (A) \
    &= mat(augment: #("hline": 1, "vline": 1), Pi_u (lambda),*,dots.c,*;0;dots.v,,Pi_u (A_1);0)
  $
  D'où $Pi_u (A_1) = 0$ donc $Pi_(A_1) | Pi_u$ et $Pi_(A_1)$ scindé, donc par hypothèse de récurrence $A_1$ est trigonalisable.

#card("exchiudivpiun", "Exercice : polynôme caractèristique divisant une puissance du polynôme minimal", ("Maths.Exercice.Réduction",))

Soit $u in cal(L)(E)$, $n = dim E$. Montrer que $chi_u | Pi_u^n$

#answer

Par récurrence forte sur $n$.

Cas $n = 1$ évident.

Supposons le résultat pour tout $m in [|1, n-1|]$.

Si $u$ est cyclique, $Pi_u = chi_u$ d'où $chi_u | Pi_u^n$.

Sinon on prend $x_0 in E\\{0}$, $k = deg Pi_(u,x_0) < n$ donc $(x_0, u(x_0), dots, u^(k-1) (x_0))$ est libre, on la complète en une base $e$ de $E$.
$
  cal(M)_e (u) = mat(augment: #(hline: 1, vline: 1), C_Pi_(u,x_0), *; 0, A)
$
Donc
$
chi_u = underbrace(chi_C_Pi_(u,x_0), Pi_(u,x_0)) chi_A \
chi_u | Pi_u chi_A
$
Or par hypothèse de récurrence $chi_A | Pi_A^(n - k)$ et
$
  0 = cal(M)_e (Pi_u (u)) = mat(augment: #(vline: 1, hline: 1), Pi_u (C_Pi_(u,x_0)), *;0,Pi_u (A)) \
  "Donc" Pi_A | Pi_u
$
Ainsi
$
  chi_u | Pi_u Pi_A^(n-k) | Pi_u^(n - k + 1) | Pi_u^n
$

#card("decompsec", "Décomposition en sous espaces caractèristiques", ("Maths.Algèbre.Réduction",))

Définition et démonstration de la décomposition en sous-espaces caractèristiques.

#answer

Soit $u in cal(L)(E)$ tel que $chi_u$ scindé, l'espace $E$ se décompose en somme directe de sev stables par $u$ :
$
  E = plus.o.big_(k = 1)^N F_k
$
Où pour tout $k in [|1,N|]$, $u_k$ induit par $u$ sur $F_k$ vérifie
$
  u_k = lambda_k id + n_k
$
Où $n_k$ est nilpotent et $lambda_k in "Sp"(u)$.

Dé plus $dim F_k = m_k$ et $F_k = ker (u - lambda_k id)^(m_k)$.

*Cas diagonalisable*

Si $u$ est diagonalisable
$
  dim F_k = m_k = dim E_lambda_k (u) \
$
$
  E_lambda_k (u) &= ker (u - lambda_k id) \ &subset.eq ker (u-lambda_k id)^(m_k) = F_k
$
$
  E_lambda_k (u) = F_k
$

*Démonstration*

Soit $u in cal(L)(E)$ tel que $chi_u$ scindé.
$
  chi_u = product_(k = 1)^N (X - lambda_k)^(m_k)
$
Où $"Sp"(u) = {lambda_1, dots, lambda_N}$.

Par le TDN on a
$
  E = plus.o.big_(k = 1)^N underbrace(ker (u - lambda_k id)^(m_k), F_k)
$
Les $F_k$ sont stables par $u$, on peut donc poser $u_k$ induit par $u$ sur $F_k$.

On note $n_k = u_k - lambda_k id in cal(L)(F_k)$ qui est nilpotent d'ordre inférieur à $m_k$.

Soit $e_k$ base de $F_k$ tel que $cal(M)_e_k (n_k) = N_k in T_(dim F_k)^(++) (KK)$.

Ainsi $cal(M)_e_k (u_k) = lambda_k I_(dim F_k) + N_k$.

En concatenant les bases $(e_k)_k$ en une base $e$ de $E$ on trouve
$
  cal(M)_e (u) = dmat(A_1, dots.down, A_N) \
  forall k in [|1, N|], space A_k = mat(lambda_k,,*;,dots.down;,,lambda_k)
$
D'où
$
product_(k = 1)^N (X - lambda_k)^(m_k) = chi_u = product_(k = 1)^N (X - lambda_k)^(dim F_k) \
m_k = dim F_k
$

#card("secarpolmin", "Sous-espaces caractèristiques et polynôme minimal", ("Maths.Algèbre.Réduction",))

Lien entre la décomposition en sous-espaces caractèristiques et le polynôme minimal.

#answer

Soit $u in cal(L)(E)$ tel que $chi_u$ scindé, à fortiori, $Pi_u$ est scindé.

$
  Pi_u &= product_(k = 1)^N (X - lambda_k)^(d_k) \ chi_u &= product_(k = 1)^N (X - lambda_k)^(m_k)
$
On peut décomposer par le TDN sur $Pi_u$ et en les espaces caractèristiques
$
  E &= plus.o.big_(k = 1)^N overbrace(ker (u - lambda_k id)^(m_k), F_k) \
  &= plus.o.big_(k = 1)^N underbrace(ker (u - lambda_k id)^(d_k), G_k) \
$
Or $d_k <= m_k$ (car $Pi_u | chi_u$), d'où
$
  G_k &= ker (u - lambda_k id)^(d_k) \ &subset.eq ker (u - lambda_k id)^(m_k) = F_k
$
Mais $plus.o.big_(k = 1)^N G_k = plus.o.big_(k = 1)^N F_k$ donc $G_k = F_k$.

Soit $q_k <= d_k$ l'indice de nilpotence de $n_k = evaluated((u - lambda_k id))_(F_k)^(F_k)$.

$
F_k &subset.eq ker (u - lambda_k id)^(q_k) \ &subset.eq ker (u - lambda_k id)^(d_k) = F_k
$

Posons $Q = product_(k = 1)^N (X - lambda_k)^(q_k)$
$
  E &= plus.o.big_(k = 1)^N ker (u - lambda_k)^(d_k) \
  &= plus.o.big_(k = 1)^N ker (u - lambda_k)^(q_k) \
$
Donc par le TDN $ker Q(u) = E$, $Pi_u | Q$ donc $d_k <= q_k <= d_k$.

#card("expiuxdq", "Exercice : valuation X-adique du polynôme minimal.", ("Maths.Exercice.Réduction",))

Soit $u in cal(L)(E)$, $Pi_u = X^d Q$ avec $X divides.not Q$.

+ Montrer que  #h(1fr)
  $
  d = min Set(k in NN^*, ker u^k = ker u^(k+1))
  $

+ Montrer que
  $
    E = ker u^d plus.o im u^d
  $

#answer

Soit $u in cal(L)(E)$, $Pi_u = X^d Q$ avec $X divides.not Q$.

+ Notons #h(1fr)
  $
    q = min Set(k in NN^*, ker u^k = ker u^(k+1))
  $

  Soit $accent(u,~)$ l'induit par $u$ sur $ker u^q$.
  $
    cases(space accent(u,~)^q = 0, space accent(u,~)^(q - 1) != 0) " Donc " Pi_accent(u,~) = X^q \
    X^q | Pi_accent(u,~) | Pi_u = X^d Q \
    q <= d
  $
  Donc $ker u^q = ker u^d$
  $
    ker u^d compose Q(u) = E \
    im Q(u) subset.eq ker u^d = ker u^q \
    ker u^q compose Q(u) = E \
    X^d Q | X^q Q \
    q >= d
  $

+ On a (TDN) #h(1fr)
  $
    E = ker u^d plus.o ker Q(u)
  $
  Soit $y in im u^d$, on dispose donc de $x in E$ tel que $y = u^d (x)$.
  $
    y = u^d (x) \
    Q(u) (y) = (X^d Q) (u) (x) = 0 \
    im u^d subset.eq ker Q(u)
  $
  Or par le théorème du rang 
  $
  dim im u^d &= dim E - dim ker u^d \ &= dim ker Q(u) \
  $
  D'où $im u^d = ker Q(u)$.

#card("dunford", "Décomposition de Dunford", ("Maths.Algèbre.Réduction",))

Définition et démonstration de la décomposition de Dunford.

#answer

Soit $u in cal(L)(E)$ tel que $chi_u$ scindé.

On dispose de $d, n in cal(L)(E)$ tel que
- $u = d + n$
- $d$ diagonalisable
- $n$ nilpotent
- $d compose n = n compose d$

De plus cette décomposition est unique.

Elle peut entre autre servire pour les puissances de matrices :
$
  A^k = P dmat((lambda_1 I_m_1 + N_1)^k, dots.down, (lambda_n I_m_n + N_n)^k) P^(-1)
$

*Démonstration*

On reprend la décomposition en sous-espaces caractèristiques
$
  Pi_u = product_(k = 1)^N (X - lambda_k)^(d_k) \
  chi_u = product_(k = 1)^N (X - lambda_k)^(m_k) \
  E = plus.o.big_(k = 1)^N underbrace(ker (u - lambda_k id)^m_k, F_k) \
  forall k in [|1, n|], space F_k = ker (u - lambda_k id)^(d_k)
$
On note $u_k$ l'endomorphisme induit par $u$ sur $F_k$.
$
  F_k = ker (u - lambda_k id_E)^(m_k) \
  "D'où " (u_k - lambda_k id_F_k)^(m_k) = 0_(cal(L) (F_k)) \
$
Posons
$
  n_k = u_k - lambda_k id_F_k \
  "Donc" u_k = lambda_k id_F_k + n_k
$
Où $n_k$ est nilpotent d'ordre $d_k$ (cf démonstration sous-espaces caractèristiques).

On pose alors $d, n in cal(L)(E)$ tel que
$
  forall k in [|1,n|], \ d|_(F_k)^(F_k) = lambda_k id_F_k \
  n|_(F_k)^(F_k) = n_k \
$
Donc $d$ diagonalisable et $n$ nilpotent d'odre $max_(k in [|1;n|])(d_k)$.

Matriciellement
$
  cal(M)_e (d) = dmat(lambda_1 I_m_k, dots.down, lambda_N I_m_k) in D_n (KK) \
  cal(M)_e (n) = dmat(N_1, dots.down, N_N) in T_n^(++) (KK) \ \
  D N = dmat(lambda_1 N_1, dots.down, lambda_N N_N) = N D
$

*Unicité*

On prend $p_1, dots, p_N$ les projecteurs associés à la décomposition (cf. démonstration du TDN)
$
  E = plus.o.big_(k = 1)^N F_k = plus.o.big_(k = 1)^N ker (u - lambda_k id)^(d_k)
$
On avait montrer que $p_1, dots, p_N in KK[u]$.

On a
$
  d = sum_(k = 1)^N lambda_k p_k in KK[u] \
  n = u - d in KK[u] \
$

Soient $d', n' in cal(L)(E)$ respectent les conditions.

Comme $u = d' + n'$, $d'$ commute avec $u$ et $n'$ aussi, donc $d'$ commute avec $d in KK[u]$ et $n'$ avec $n in KK[u]$.

Ainsi $d'$ et $d$ sont codiagonalisables, d'où $d' - d$ est diagonalisable.

Et $n - n'$ est nilpotent (binôme de Newton).

Or $d' + n' = d + n$ d'où 
$
underbrace(d' - d, "diagonalisable") = underbrace(n - n', "nilpotent")
$

D'où $d' - d = 0$ et $n' - n = 0$.

#card("codiag", "Codiagonalisabilité", ("Maths.Algèbre.Réduction",))

Définition et critère de codiagonalisabilité.

#answer

Soient $(u_i)_i in cal(L)(E)^I$ une famille d'endomorphismes. 

On dit que les $(u_i)_i$ sont codiagonalisables s'il existe une base $e$ de $E$ tels que pour tout $i in I$, $cal(M)_e (u_i) in D_n (KK)$.

*Démonstration : deux endomorphismes*

Soient $u, v in cal(L)(E)$ diagonalisables tels que $u compose v = v compose u$.
$
  E = plus.o.big_(k = 1)^N E_lambda_k (u) " où " "Sp"(u) = {lambda_1, dots, lambda_N}
$
Comme $u compose v = v compose u$, les $E_lambda_k (u)$ sont stables par $v$. 

Soit $v_k$ l'induit de $v$ sur $E_lambda_k (u)$, qui est diagonalisable car $v$ l'est.

Pour chaque $k in [|1, N|]$ on dispose de $e_k$ base de vecteurs propres de $v_k$ (donc de $v$ et $u$).

En concatenant on obtient une base qui convient.

*Démonstration famille quelconque*

Par récurrence sur $n = dim E$.

Cas $n = 1$ évident.

Supposons la propriété pour tout $KK$-ev de dimension inférieur à $n$.

Soit $(u_i)_i in cal(L)(E)^I$ diagonalisables commutant avec $dim E = n+1$.

Si tout les $u_i$ sont des homothéties n'importe quelle base convient.

Sinon on dispose de $j in I$ tel que $u_j$ n'est pas une homothétie.

$
  E = plus.o.big_(k = 1)^N E_lambda_k (u_j) " où " "Sp"(u_j) = {lambda_1, dots, lambda_N}
$

Pour tout $i in I$, les $E_lambda_k (u_j)$ sont stables par $u_i$ car $u_i compose u_j = u_j compose u_i$.

Notons $u_(i,k)$ l'induit de $u_i$ sur $E_lambda_k (u_j)$ qui est de dimension inférieur à $n$ car $u_j$ n'est pas une homothétie. 

Les $(u_(i,k))_i$ sont donc diagonalisables et commutent entre eux, on peut appliquer l'hypothèse de récurrence.

On dispose donc de $e_k$ base de $E_lambda_k (u_j)$ formée de vecteurs propres commmun aux $(u_i)_i$. Il suffit alors de les concatener.

// TODO: Ex 64 de la fiche réduction

#card("comendo", "Commutant d'un endomorphisme diagonalisable", ("Maths.Algèbre.Réduction",))

Propriétés sur le commutant d'un endomorphisme diagonalisable.

#answer

Soit $u in cal(L)(E)$ diagonalisable.

- Pour tout $v in cal(L)(E)$, $v in "Com" (u)$ ssi les espaces propres de $u$ sont stables par $v$.

- $dim "Com" (u) = display(sum_(lambda in "Sp"(u)) (dim E_lambda (u))^2)$

*Démonstration*

- L'implication directe est évidente. 

  Supposons $v in cal(L)(E)$ qui stabilise les espaces propres de $u$.

  Pour $lambda in "Sp"(u)$ soit $x in E_lambda (u)$, d'où $v(x) in E_lambda (u)$.
  $
    v(u(x)) &= v(lambda x) = lambda v(x) \
    u(v(x)) &= lambda v(x)
  $

  Or $u$ diagonalisable, donc on dispose d'une base de vecteurs propres de $u$.

  Ainsi $u compose v$ et $v compose u$ coincident sur une base d'où l'égalité.

- On note $"Sp"(u) = {lambda_1, dots, lambda_N}$.

  On considère
  $
    theta : func("Com"(u), product_(k = 1)^N cal(L)(E_lambda_k (u)), v, (evaluated(v)_(E_lambda_1 (u)), dots, evaluated(v)_(E_lambda_N (u))))
  $
  Qui est linéaire.

  Soit $v in ker theta$ : pour tout $k in [|1, N|]$
  $
    v(E_lambda_k (u)) = 0 \
    "Or " E = plus.o.big_(k = 1)^N E_lambda_k (u) \
    "Donc " v = 0
  $

  Soit $(v_1, dots, v_k) in product_(k = 1)^N cal(L)(E_lambda_k (u))$.

  Pour $k in [|1,N|]$, on note $e_k$ base de $E_lambda_k (u)$.

  On définit $v in cal(L)(E)$ qui coincide avec $v_k$ sur tout les vecteurs de $e_k$.

  Ainsi $theta(v) = (v_1, dots, v_k)$, et $theta$ isomorphisme.
  $
    dim "Com"(u) &= sum_(k = 1)^N dim cal(L)(E_lambda_k (u)) \
    &= sum_(k = 1)^N (dim E_lambda_k (u))^2
  $

#card("exbicom", "Exercice : le bicommutant", ("Maths.Exercice.Réduction",))

Soit $u in cal(L)(E)$ diagonalisable. On définit le bicommutant de $u$
$
B(u) = Set(w in cal(L)(E), vec(delim: #none, forall v in "Com"(u), space v compose w = w compose v) space)
$
Montrer que $B(u) = KK[u]$.

#answer

Comme $u in "Com" (u)$ on remarque
$
  KK[u] subset.eq B(u) subset.eq "Com"(u)
$
On construit $e$ concatenation de bases des $E_lambda_k (u)$ pour $k in [|1, N|]$ et $"Sp"(u) = {lambda_1, dots, lambda_N}$.

Soit $w in B(u) subset.eq "Com"(u)$ donc les $(E_lambda_k)_k$ sont stables par $w$.
$
  M = cal(M)_e (w) = dmat(M_1, dots.down, M_N)
$
Pour tout $v in "Com"(u), w compose v = v compose w$.
$
A = cal(M)_e (v) = dmat(A_1, dots.down, A_N)
$
Or $A M = M A$ donc
$
  forall k in [|1, N|], A_k M_k = M_k A_k
$
Ainsi $M_k$ est une matrice qui commute avec toutes les autres. 

On montre facilement grâce à $E_(i j)$ que $M_k = alpha_k I_(m_k)$.

Par interpolation de Lagrange on dispose de $P in KK_(N+1) (X)$ tel que $P(lambda_k) = alpha_k$. Or
$
  cal(M)_e (u) &= dmat(lambda_1 I_(m_1), dots.down, lambda_N I_(m_N)) \
  cal(M)_e (P(u)) &= dmat(P(lambda_1) I_(m_1), dots.down, P(lambda_N) I_(m_N)) \
   &= dmat(alpha_1 I_(m_1), dots.down, alpha_N I_(m_N)) \
   &= cal(M)_e (w)
$
D'où $w in KK[u]$.

#card("projspect", "Projecteurs spectraux d'un endomorphisme diagonalisable", ("Maths.Algèbre.Réduction",))

Définition et propriétés des projecteurs spectraux d'un endomorphisme diagonalisable.

#answer

Soit $u in cal(L)(E)$ diagonalisable.

$
  chi_u = product_(k = 1)^N (X - lambda_k)^(m_k) \
  Pi_u = product_(k = 1)^N (X - lambda_k)
$
Soient $p_1, dots, p_N$ les projecteurs associés à la décomposition
$
  E = plus.o.big_(k = 1)^N underbrace(ker (u - lambda_k id), E_lambda_k (u)) \
$
On a alors pour tout $i, j in [|1,N|]$
$
  evaluated(p_i)_(E_lambda_j (u)) = delta_(i j) lambda_i id \
$
Dans la base $e$ diagonalisant $u$ et pour tout $P in KK[X]$ on a 
$
  cal(M)_e (P(u)) = dmat(P(lambda_1) I_m_1, dots.down, P(lambda_N) I_m_N) \
  cal(M)_e (p_k) = dmat(0, dots.down, I_m_k, dots.down, 0) \
$
Donc $p_k = L_k (u) in KK_(N-1) [u]$ avec $L_k$ polynôme de Lagrange associés aux $(lambda_i)_i$.

Ainsi pour tout $q in NN$
$
  u = sum_(k = 1)^N lambda_k p_k \
  u^p = sum_(k = 1)^N lambda_k^q p_k in KK_(N - 1) [u]
$

#card("sesendodiag", "Sous-espaces stables d'un endomorphisme diagonalisable", ("Maths.Algèbre.Réduction",))

Propriétés sur les sous-espaces stables d'un endomorphisme diagonalisable.

#answer

Soit $u in cal(L)(E)$ diagonalisable, $"Sp"(u) = {lambda_1, dots, lambda_N}$.

+ Si $G$ sev stable par $u$ alors #h(1fr)
  $
    G = plus.o.big_(k = 1)^N G inter E_lambda_k (u)
  $

+ Réciproquement si $G_1, dots, G_N$ sont des sevs de $E_lambda_1 (u), dots, E_lambda_N (u)$ respectivements alors
  $
    G = plus.o.big_(k = 1) G_k
  $
  Est un sev stable par $u$.

*Démonstration*

+ Soit $accent(u,~)$ induit par $u$ sur $G$ donc diagonalisable. #h(1fr)
  $
    G &= plus.o.big_(lambda in "Sp"(accent(u,~))) E_lambda (accent(u,~)) \
    &= plus.o.big_(k = 1)^N ker (accent(u,~) - lambda_k id_G) \
    &= plus.o.big_(k = 1)^N G inter underbrace(ker (u - lambda_k id), E_lambda_k (u)) \
  $

+ L'écrire.

#card("dopsprev", "Existence d'une droite ou d'un plan stable dans un espace vectoriel réel", ("Maths.Algèbre.Réduction",))

Démonstration de l'existence d'une droite ou d'un plan stable dans un espace vectoriel réel.

#answer

Soit $E$ un $RR$-ev et $u in cal(L)(E)$, $u$ admet une droite ou un plan stable.

$
  Pi_u = product_(k = 1)^N P_k^(m_k)
$
Avec $P_1, dots, P_N$ irréductibles deux à deux distincts.

- Si l'un des $P_k$ est de degré $1$. #h(1fr)
  $
    P_k = X - lambda
  $
  Et $lambda$ est racine de $Pi_u$ et est donc une valeur propre de $u$ d'où l'existence d'une droite stable.

- Si l'un des $P_k$ est de degré $2$.
  $
    P_k = X^2 - a X - b
  $

  Supposons par l'absurde que $ker P_k (u) = {0}$.
  $
    Pi_u (u) = P_k (u) compose Q(u) = 0
  $
  D'où $Q(u) = 0$ qui est absurde car $Pi_u$ est minimal.

  On dispose donc de $x in ker P_k (u) \\ {0}$.

  $
    u^2 (x) = a u(x) + b x
  $
  D'où $F = "Vect"(x, u(x))$ stable par $u$.

  Si $u(x) = alpha x$, $alpha in RR$.
  $
    alpha^2 x = (a alpha + b) x \
    alpha | X^2 - a X - b
  $
  Absurde donc $F$ est un plan.

#card("endosimple", "Endomorphismes simples", ("Maths.Algèbre.Réduction",))

Soit $u in cal(L)(E)$, il y a équivalence entre

+ Les seuls sev stables de $u$ sont $E$ et ${0}$.

+ $chi_u$ irréductible.

+ $u$ est dit simple.

#answer

+ (2 $=>$ 1) Par contraposé #h(1fr)

  Soit $F$ sev stable par $u$ de dimension dans $[|1, n - 1|]$, et $accent(u,~)$ l'endomorphisme induit.

  $
    chi_accent(u,tilde) | chi_u
  $
  Avec $chi_accent(u,~) = dim F != deg chi_u$ d'où $chi_u$ non irréductible.

+ (1 $=>$ 2) Par contraposé : Soit $x in E\\{0}$ on note
  $
    F_x = "Vect"(u^k (x_0))_(k in NN)
  $
  Qui est stable par $u$.

  Si $deg Pi_(u,x) = dim F_x <= n - 1$, alors $u$ possède un sev stable non trivial.

  Sinon $Pi_(u,x) | Pi_u | chi_u$ tous unitaires de degré $n$, donc égaux. Ainsi
  $
    Pi_(u,x) = chi_u = P Q \
    y = Q(u) (x) \
    Pi_(u,y) = P \
  $
  D'où $F_y$ stable non trivial.

#card("endosemsimple", "Endomorphismes semi-simples", ("Maths.Algèbre.Réduction",))

Définition et propriétés des endomorphismes semi-simples.

#answer

Soit $u in cal(L)(E)$, il y a équivalence entre

+ Tout sev stable par $u$ admet un supplémentaire stable.

+ $Pi_u$ est sans carrés
  $
    Pi_u = product_(k = 1)^N P_k
  $
  Avec $P_1, dots, P_N$ irréductibles deux à deux distincts.

+ $u$ est semi-simple.

*Démonstration*

+ (1 $=>$ 2) On pose #h(1fr)
  $
    Pi_u = product_(k = 1)^N P_k^(d_k)
  $
  Pour $i in [|1,N|]$, $F = ker P_k (u)$ admet un supplémentaire stable $G$.

  Soient $u_F, u_G$ induient par $u$ sur $F$ et $G$.
  $
    Pi_(u_F)  = P_i
  $
  Car annule et irréductible.

  De plus
  $
    P(u) = 0 \ <=> cases(space forall x in F\, space  P(u) (x) &= 0, space forall x in G\, space P(u) (x) &= 0) \
    <=> Pi_(u_F) | P "et" Pi_(u_G) | P \
    <=> Pi_u_F or Pi_u_G | P \
    "Donc" Pi_u = Pi_u_F or Pi_u_G
  $
  Ainsi
  $
    Pi_u_G | product_(k = 1)^N P_k^(d_k) \
    Pi_u = Pi_u_G or P_i
  $
  Mais 
  $
  G inter F = {0} \
  G inter ker P_1 (u) = {0} \
  0 != P_i (u_G) in "GL"(E) \
  P_i divides.not Pi_u_G
  $
  Ainsi comme $Pi_u = P_i or Pi_u_G$
  $
  d_i = 1
  $

+ (2 $=>$ 1) Cas $Pi_u$ irréductible.

  On suppose $Pi_u$ irréductible de degré $d$.

  Donc pour tout $x in E\\{0}$
  $ 
    Pi_(u,x) | Pi_u " d'où " Pi_u = Pi_(u,x) \ "et" dim F_x = d
  $
  
  Soit $F$ sev stable par $u$, si $F = E$, $G = 0$ convient.

  On dispose alors de $x_1 in E \\ F$.

  Comme $F$ et $F_x_1$ sont stables par $u$, $F inter F_x_1$ l'est.

  Supposons par l'absurde qu'il existe $x in F inter F_x_1 \\ {0}$.

  $
    underbrace(F_x, dim d) subset.eq underbrace(overbrace(F_x_1, dim d) inter F, dim <= d) \
    F_x_1 subset.eq F \
    x_1 in F
  $
  Qui est absurde : $F plus.o F_x_1 subset.eq E$.

  Supposons construits $x_1, dots, x_k$ tels que
  $
    underbrace(F plus.o (plus.o.big_(i = 1)^k F_x_i), F_k "stable") subset.eq E
  $

  Si $F_k = E$ on a fini.

  Sinon on choisit $x_(k+1) in E \\ F_k$ et on répéte.

  $
    F_x_(k+1) inter F_k = {0} \
    F_k plus.o F_x_(k+1) subset.eq E \
    F plus.o (plus.o.big_(i = 1)^(k+1) F_x_i) subset.eq E
  $

  Qui se termine en au plus $floor(n / d)$ étapes.
  // TODO: Que faire de la remarque Frobenius M142 ?

+ (2 $=>$ 1) Cas général.
  $
    Pi_u = product_(k = 1)^N P_k
  $

  Par le TDN
  $
    E = plus.o.big_(k = 1)^N ker P_k (u)
  $
  Soit $F$ sev stable par $u$, $accent(u,~)$ induit par $u$ sur $F$. Par TDN 
  $
    F &= plus.o.big_(k = 1)^N ker P_k (accent(u,~)) \
     &= plus.o.big_(k = 1)^N underbrace((ker P_k (accent(u,~))) inter F, F_k)
  $
  $F_k$ sev de $E_k = ker P_k (u)$ stable par $u_k$ induit par $u$ sur $E_k$.

  De plus $Pi_u_k = P_k$ (annule et irréductible).

  Donc par le premier cas on trouve $G_k$ sev de $E_k$ stable par $u$ tel que
  $
    E_k = G_k plus.o F_k
  $
  Enfin
  $
    E &= plus.o.big_(k = 1)^N E_k \
    &= underbrace((plus.o.big_(k = 1)^N (F_k)), F "stable par" u) plus.o underbrace((plus.o.big_(k = 1)^N G_k), G "stable par" u)
  $

#card("diagsisevstabl", "Exercice : critère de diagonalisabilité sur l'existence de supplémentaires stables", ("Maths.Exercice.Réduction",))

Soit $u in cal(L)(E)$ tel que $chi_u$ scindé. Montrer que $u$ est diagonalisable ssi tout sev stable par $u$ admet un supplémentaire stable.

#answer

- Supposons $u$ diagonalisable, soit $F$ un sev stable par $u$.

  On dispose donc de $f = (f_1, dots, f_d)$ base de $F$ et $e = (e_1, dots, e_n)$ base de vecteurs propres de $E$.

  On peut donc complétée la base $f$ par des vecteurs de $e$:
  $
    (f_1, dots, f_d, e_i_1, dots, e_i_(n - d)) "base de" E
  $
  Ainsi $G = "Vect"(e_i_1, dots, e_i_(n-d))$ est un supplémentaire de $F$ stable par $u$.

- Supposons que tout sev stable par $u$ admettent un supplémentaire stable.

  $
    F = plus.o.big_(lambda in "Sp"(u)) E_lambda (u)
  $
  Est un sev stable, et admet donc $G$ comme supplémentaire stable. Notons $accent(u,~)$ l'induit sur $G$ de $u$.
  $
    Pi_accent(u,~) | Pi_u "scindé"
  $
  Donc $accent(u,~)$ admet une valeur propre $lambda$ et un vecteur propre $x in F inter G = {0}$ qui est absurde. Donc $G = {0}$ et $F = E$ : $u$ est diagonalisable.

#card("endomatrix", "Endomorphismes de produit de matrices", ("Maths.Algèbre.Réduction",))

Propriétés sur les endomorphismes de la forme $M |-> A M$ et $M |-> M A$ de $cal(L)(M_n (KK))$.

#answer

Soit $A in M_n (KK)$. Posons
$
  L_A : func(M_n (KK), M_n (KK), M, A M "ou" M A) in cal(L)(M_n (KK)) \
$
Pour tout $P in KK[X]$ et $M in M_n (KK)$
$
  P(L_A) (M) = cases(space P(A) M, space M P(A)) = L_P(A) (M) \
$
De plus $L_B = 0 => L_B (I_n) = B = 0$ d'où
$
  P(L_A) = 0 <=> P(A) = 0
$
C'est à dire $Pi_L_A = Pi_A$

On en déduit

- $L_A$ est nilpotent ssi $A$ l'est et est de même ordre.

- $L_A$ est diagonalisable ssi $A$ l'est.

- $"Sp"(A) = "Sp"(L_A)$

De plus pour $lambda in "Sp"(A)$
$
dim E_lambda (L_A) = n dim E_lambda (A)
$

*Démonstration*

- Pour $L_A (M) = A M$

  Soit $M = (C_1, dots, C_n) in M_n (KK)$

  $
    M in E_lambda (L_A) <=> A M = lambda M \
    <=> forall j in [|1,n|], space A C_j = lambda C_j \
    <=> {C_1, dots, C_n} subset.eq E_lambda (A)
  $
  Ainsi $E_lambda (L_A) tilde.eq E_lambda (A)^n$.

- Pour $L_A (M) = M A$ 

  Soit $M = vec(L_1, dots.v, L_n) in M_n (KK)$

  $
    M in E_lambda (L_A) <=> M A = lambda M \
    <=> forall i in [|1,n|], space A L_i = lambda L_i \
    <=> {L_1, dots, L_n} subset.eq E_lambda (A)
  $
  Ainsi $E_lambda (L_A) tilde.eq E_lambda (A)^n$.

#card("endodiffprodmat", "Endomorphisme différence de produits de matrices", ("Maths.Algèbre.Réduction",))

Propriétés sur l'endomorphisme $phi : M |-> A M - M B$ in $cal(L)(M_n (KK))$

#answer

Soit $A, B in M_n (KK)$, tel que $chi_A$ scindé et $B$ admet au moins une valeur propre. ($KK$ algébriquement clos suffit).

Posons
$
  phi : func(M_n (KK), M_n (KK), M, A M - M B) in cal(L)(M_n (KK))
$
Il y a équivalence entre

+ $"Sp"(A) inter "Sp"(B) = emptyset$.

+ $chi_A (B) in "GL"_n (KK)$.

+ $phi$ injectif.

+ $phi$ est un automorphisme.

De plus on a

- $"Sp"(phi) = {lambda - mu, (lambda, mu) in "Sp"(A) times "Sp"(B)}$

*Démonstration*

- (3 $<=>$ 4) Argument dimensionnel.

- (1 $=>$ 2) Pour tout $lambda in "Sp"(A)$ #h(1fr)
  $
    lambda in.not "Sp"(B) \
    ker (B - lambda I_n) = E_lambda (B) = {0} \
    B - lambda I_n in "GL"_n (KK)
  $
  Ainsi
  $
    chi_A (B) = product_(lambda in "Sp"(A)) (B - lambda I_n)^(m_lambda) in "GL"_n (KK)
  $

- (2 $=>$ 3) Soit $M in ker phi$

  $
    A M = M B \
    forall k in NN, space A^k M = M B^k \
    0 = chi_A (A) M = underbrace(chi_A (B), in "GL"_n (KK)) M \
    M = 0
  $

- (3 $=>$ 1) Par contraposé, supposons qu'on dispose de $lambda in "Sp"(A) inter "Sp"(B)$.

  On sait que $chi_B = chi_(B^TT)$ donc toute valeur propre de $B$ est valeur propre de $B^TT$.
  
  Soit $X, Y$ vecteurs propres non nuls de $A$ et $B^TT$.
  $ 
  phi(X Y^TT) &= A X Y^TT - X Y^TT B \
  &= A X Y^TT - X (B^TT Y)^TT \
  &= lambda X Y^TT - lambda X Y^TT \
  &= 0
  $
  Or $X Y^TT != 0$ d'où $phi$ non injective.

- Soit $lambda in "Sp"(A), mu in "Sp"(B)$. $X, Y$ vecteurs propres non nuls de $A$ et $B^TT$.
  $
  phi(X Y^TT) &= A X Y^TT - X Y^TT B \
  &= lambda X Y^TT - mu X Y^TT \
  &= (lambda - mu) X Y^TT
  $
  D'où $lambda - mu in "Sp"(phi)$

- Soit $alpha in "Sp"(phi)$, $M$ vecteur propre non nul associé.

  $
    phi(M) = A M - M B = alpha M \
    underbrace((A - alpha I_n), accent(A,~)) M - M B = 0
  $
  Avec $chi_accent(A,~)$ scindé (pour toute valeur propre $lambda$ de $A$, $lambda - alpha$ est valeur propre de $accent(A,~)$)

  Posons $phi' : N |-> accent(A,~) N - N B$
  $
    phi' (M) = 0
  $
  Donc $phi'$ non injectif d'où $
  {mu} subset.eq "Sp"(accent(A,~)) inter "Sp"(B) != emptyset
  $
  Ainsi $alpha + mu in "Sp"(A)$.

#card("endocommuta", "Endomorphisme commutateur de matrices", ("Maths.Algèbre.Réduction",))

Propriétés sur les endomorphismes de la forme $M |-> A M - M A in cal(L)(M_n (KK))$.

#answer

Soit $A in cal(M)_n (KK)$ tel que $chi_A$ scindé.

$
  phi_A : func(M_n (KK), M_n (KK), M, A M - M A) in cal(L)(M_n (KK))
$

On a les propriétés de $M |-> A M - M B$, et de plus

- Si $A$ est nilpotent alors $phi_A$ l'est.

- Si $A$ est diagonalisable alors $phi_A$ aussi.

*Démonstration*

- Supposons $A$ nilpotent d'ordre $q$. Posons
  $
  mat(delim: #none,,M_n (KK), ->, M_n (KK);L_A :, M, |->, A M; R_A :, M, |->, M A)
  $
  On sait que $L_A$ et $R_A$ sont nilpotents d'ordre $q$ car $A$ l'est.

  De plus $L_A compose R_A = A M A = R_A compose L_A$ d'où
  $
    phi_A = L_A - R_A \
    phi_A^(2q) = sum_(k = 0)^(2q) vec(2q, k) (-1)^k R_A^k compose L_A^(2q - k) = 0
  $

- Supposons $A$ diagonalisable.

  On sait que $L_A$ et $R_A$ commutent et sont diagonalisables, donc ils sont codiagonalisables :
  $
    phi_A = L_A - R_A
  $
  Est diagonalisable.

#card("endonilpcyc", "Endomorphismes nilpotents cycliques", ("Maths.Algèbre.Réduction",))

Caractèrisation des sev stables par un endomorphisme nilpotent cyclique.

#answer

Soit $u in cal(L)(E)$ nilpotent cyclique.

Les seuls sev de $E$ stables par $u$ sont les $(ker u^k)_(k in [|0, n|])$.

*Démonstration*

Ils sont stables comme $ker$ d'un endomorphisme commutant avec $u$.

Soit $F$ sev stable par $u$. Soit $accent(u,~)$ induit par $u$ sur $F$ qui est nilpotent car car $accent(u,~)^n = 0$.

Or l'ordre de nilpotence de $accent(u,~)$ est majoré par $d = dim F$ : $accent(u,~)^d = 0$.

Donc $F subset.eq ker u^d$.

De plus par les noyaux itérées
$
underbrace(ker u, dim 1) subset.neq dots.c subset.neq underbrace(ker u^d, dim d) subset.neq dots.c subset.neq underbrace(ker u^n, dim n)
$

D'où $F = ker u^d$.

#card("prodkroc", "Produit de Kronecker et diagonalisabilité", ("Maths.Algèbre.Réduction",))

Diagonalisabilité du produit de Kronecker de matrices (dimension $2n$).

#answer

Soit $L = mat(alpha, beta; gamma, delta) in M_2 (KK)$ et $A in M_n (KK)$. On pose le produit de Kronecker
$
  M = L times.o A = mat(alpha A, beta A; gamma A, delta A) in M_(2n) (KK)
$

Alors

- Si $L$ est diagonalisable, $M$ est diagonalisable ssi $A$ l'est.

- Si $L = mat(1, 1; 0, 1)$, $M$ est diagonalisable ssi $A = 0$.

*Démonstration*

- On suppose $L$ diagonalisable :

  $
    L = P dmat(lambda, mu) P^(-1) quad vec(delim: #none, P = mat(a, b; c, d) in "GL"_2 (KK), P^(-1) = mat(a', b'; c', d'))
  $
  On remarque
  $
    Q = P times.o I_n = mat(a I_n, b I_n; c I_n, d I_n) \
    Q' = P times.o I_n = mat(a' I_n, b' I_n; c' I_n, d' I_n) \ 
    Q Q' = dmat(I_n, I_n) = I_(2n) \
  $
  $
    Q' M Q &= mat(a' I_n, b' I_n; c' I_n, d' I_n) mat(alpha A, beta A; gamma A, delta A) mat(a I_n, b I_n; c I_n, d I_n) \
    &= dmat(lambda A, mu A)
  $

  Donc $M$ est diagonalisable ssi $A$ l'est.

- Pour $L = mat(1, 1; 0, 1)$.
  $
    M^k = mat(A^k, k A^k;0, A^k) quad "(récurrence)"
  $
  Donc pour tout $P in KK[X]$
  $
    P(M) = mat(P(A), A P'(A); 0, P(A))
  $
  Si $M$ est diagonalisable, $Pi_M$ est SARS.
  $
    Pi_M (M) = 0 <=> cases(space Pi_M (A) = 0, space A Pi_M (A) = 0)
  $
  Comme $Pi_M (A) = 0$, $A$ est diagonalisable.

  Or $Pi_M$ est SARS : $Pi_M and Pi_M' = 1$ donc $P' and Pi_A = 1$ car $Pi_A | Pi_M$.

  Donc $Pi_M'(A) in "GL"_n (KK)$ et $A Pi_M' (A) = 0$ d'où $A = 0$.
// TODO: Exo 51 Reduc

#card("cotz", "Cotrigonalisation", ("Maths.Algèbre.Réduction",))

Critère de Cotrigonalisabilité d'une famille d'endomorphismes.

#answer

Soit $(u_i)_i in cal(L)(E)^I$ une famille d'endomorphismes trigonalisables qui commutent. 

Il existe une base $e$ de $E$ tel que pour tout $i in I$, $cal(M)_e (u_i)$ soit triangulaire supérieure.

*Démonstration : structure*

On voudra toujours
+ Trouver un vecteur propre commun
+ Faire une récurrence sur la dimension.

Faisons d'abord la 2#super[e] étape dans le cas général :

Supposons que toute famille $(u_i)_i in cal(L)(E)^I$ d'endomorphismes trigonalisables qui commutent admete un vecteur propre commun.

Cas $n = 1$ évident.

Supposons la propriété sur tout $KK$-ev de dimension strictement inférieur à $n$.

Soit $e_1$ vecteur propre commun aux éléments de $(u_i)_i$ associé aux valeurs propres $(lambda_i)_i in KK^I$.

On complète $e_1$ en la base $(e_1, dots, e_n)$. Pour tout $i in I$

$
    cal(M)_e (u_i) = mat(augment: #(hline: 1, vline: 1), lambda_i, *; 0, A_i) quad chi_u_i = chi_A_i (X - lambda)\ 
$
Or $chi_u_i$ scindé donc $chi_A$ scindé : $chi_A$ est trigonalisable.

De plus les $(A_i)_i$ commutent car mes $(u_i)_i$ aussi.

Par hypothèse de récurrence on conclut.

*Démonstration : deux endomorphismes*

Soit $u, v in cal(L)(E)$ trigonalisables qui commutent.

Soit $lambda in "Sp"(u)$, $E_lambda (u) != {0}$ est stable par $v$.

Notons $accent(v, ~)$ induit par $v$ sur $E_lambda (u)$, qui est encore trigonalisable, et admet donc un vecteur propre $e_1$.

Puis récurrence.

*Démonstration : famille finie*

Par récurrence sur $d$ cardinal de la famille.

Cas 1 et 2 endomorphismes traités.

On suppose que toute famille de cardinal inférieur à $d$ admet un vecteur propre commun.

Soit $u_1, dots, u_(d+1) in cal(L)(E)$ trigonalisables qui comuttent.

Soit $x$ vecteur propre commun aux $u_1, dots, u_d$ associé aux valeurs propres $lambda_1, dots, lambda_d in KK$.

$
{x} in F = inter.big_(k = 1)^d underbrace(E_lambda_k (u_k), "stable par" v) != emptyset
$
Donc $F$ est stable par $v$, on peut donc y induire $accent(v,~)$ qui est trigonalisable et admet donc $e_1$ vecteur propre commun aux $u_1, dots, u_(d+1)$.

*Démonstration : famille infinie*

Soit $(u_i)_i in cal(L)(E)^I$ une famille quelconqe d'endomorphismes trigonalisables qui commutent.

$"Vect"(u_i)_(i in I)$ est un sev de $cal(L)(E)$ et admet donc une base $u_i_1, dots, u_i_d$.

C'est une famille finie, donc cotrigonalisable dans une base $e$.

Et pour tout $i in I$, $u_i in "Vect"(u_i_1, dots, u_i_d)$ donc $cal(M)_e (u_i)$ est triangulaire supérieur (comme combinaison linéaire de matrices qui le sont).

#card("polcarsomme", "Exercice : polynôme caractèristique d'une somme d'endomorphismes", ("Maths.Exercice.Réduction",))

Soit $E$ un $CC$-ev de dimension finie, $u, v in cal(L)(E)$ qui commutent, tel que $v$ est nilpotent. 

Montrer que $chi_(u + v) = chi_u$ (Exercice 106).

#answer

Deux perspectives

+ Comme $E$ est un $CC$-ev, $u$ et $v$ sont trigonalisables, et commutent, donc sont cotrigonalisable.

  Ainsi on dispose de $e$ base de $E$ tel que
  $
    cal(M)_e (u) &= mat(lambda_1,,*;,dots.down;,,lambda_n) \
    cal(M)_e (v) &= mat(0,,*;,dots.down;,,0) \
    cal(M)_e (u + v) &= mat(lambda_1,,*;,dots.down;,,lambda_n) \
    chi_(u + v) &= chi_u
  $

#card("excomuveu", "Exercice : commutateur qui vaut l'un des opérande", ("Maths.Exercice.Réduction",))

Soit $E$ un $KK$-ev ($"car" KK = 0$) et $u, v in cal(L)(E)$ tels que $u v - v u = u$.

+ Montrer que $u$ est nilpotent.

+ Montrer que si $KK = CC$, $u$ et $v$ sont cotrigonalisable.

#answer

+ Deux méthodes : #h(1fr)
  - On considère
    $
      phi_v : func(cal(L)(E), cal(L)(E), w, w v - v w) \
      phi_v (u^k) = k u^k \
    $
    Donc si $u^k != 0$, $k in "Sp"(phi_v)$ qui est fini, donc on dispose de $k in NN^*$ tel que $u^k = 0$.

  - On remarque
    $
      P(u) v - v P(u) = u P'(u)
    $
    En particulier pour $P = Pi_u$
    $
    0 = u Pi'_u (u) \
    underbrace(Pi_u, deg d) | underbrace(X Pi'_u, deg d) \
    X Pi'_u = c Pi_u
    $
    Donc
    $
    d X^d + sum_(k = 0)^(d-1) k a_k X^k = c X^d + sum_(k = 0)^(d-1) c a_k X^k \
    c = d \
    forall k in [|0, d-1|], space d a_k = k a_k \
    forall k in [|0, d-1|], a_k = 0 \
    Pi_u = X^d
    $

+ Comme $u$ est nilpotent, $"Sp"(u) = {0}$.
  $
    (u v - v u) (ker u) &= u (ker u) \
    u (v (ker u)) &= 0 \
    v(ker u) &subset.eq ker u
  $
  Donc $ker u$ est stable par $v$, posons $accent(v,~)$ induit sur $ker u$. Or $accent(v,~)$ admet un vecteur propre commun $x in ker u = E_0 (u)$.

  Ainsi par récurrence sur la dimension de $E$ :

  Supposons la propriété pour tout $CC$-ev de dimension inférieur strictement à $n$.

  Soit $e_1$ vecteur propre commun à $u$ et $v$ associé aux valeurs propres $0$ et $lambda$.

  Soit $e' = (e_1, e'_2 dots, e'_n)$ base de $E$.
  $
    cal(M)_e' (u) = mat(augment: #(hline: 1, vline: 1), 0, *; 0, A) \
    cal(M)_e' (v) = mat(augment: #(hline: 1, vline: 1), lambda, *; 0, B) \
  $
  Et $A B - B A = A$ car $u v - v u = u$ donc on dispose de $(e_2, dots, e_n)$ qui cotrigonalisent $A$ et $B$.

#card("exunilpssitruk", "Exercice : critère de nilpotence sur la trace des puissances", ("Maths.Algèbre.Réduction",))

Soit $E$ un $KK$-ev de dimension $n$ ($KK subset.eq CC$).

+ Soit $u in cal(L)(E)$, montrer que $u$ est nilpotent ssi pour tout $k in NN^*$, $tr(u^k) = 0$.

+ Soit $u in cal(L)(E)$ tel que pour tout $k in NN^*$
  $
    tr u^k = sum_(i = 1)^n lambda_i^k quad lambda_1, dots, lambda_n in CC
  $
  Montrer que
  $
    chi_u = product_(k = 1)^n (X - lambda_k)
  $

#answer

Dans les deux cas, $KK subset.eq CC$, donc $u$ est trigonalisable dans $CC$.
$
  cal(M)_e (u) = mat(mu_1,,*;,dots.down;,,mu_n) = D \
  forall k in NN, space tr u^k = tr D^k = sum_(i = 1)^n mu_i^k
$
Posons ${mu_1, dots, mu_n} = {alpha_1, dots, alpha_d}$ deux à deux distincts.
$
  chi_u = product_(k = 1)^d (X - alpha_k)^(m_k) \
  tr u^k = sum_(i = 1)^d m_i alpha_i^k quad (*)
$

+ Par l'absurde : on suppose $d >= 2$ et $alpha_1 = 0$ (éventuellement $m_1 = 0$).

  Par $(*)$ :
  $
    forall P in X KK[X], space sum_(k = 1)^d m_k P(alpha_k) = 0
  $
  Ainsi par interpolation de lagrange : pour $i in [|2, d|]$,
  $
    P(alpha_i) = 1 \
    forall j != i, space P(alpha_j) = 0 \
    P(alpha_i) = P(0) = 0 "d'où" X | P \
    sum_(k = 1)^d m_k P(alpha_k) = m_i = 0
  $

+ Pour tout $k in NN^*$
  $
    sum_(i = 1)^n mu_i^k = sum_(i = 1)^n lambda_i^k
  $
  On considère ${lambda_1, dots, lambda_n} union {mu_1, dots mu_n} = {beta_1, dots, beta_N}$ deux à deux distincts.

  Pour $i in [|1, n|]$
  $
    n_i &= abs(Set(k in [|1,n|], mu_k &= beta_i)) \
    m_i &= abs(Set(k in [|1,n|], lambda_k &= beta_i)) \
  $
  Donc pour tout $k in NN^*$
  $
    forall k in NN^*, space sum_(i = 1)^N n_i beta_i^k = sum_(k = 1)^N m_i beta_i^k \
    <=> forall k in NN^*, space sum_(i = 1)^N (n_i - m_i) beta_i^k = 0
  $
  Or $V(beta_1, dots, beta_N) != 0$ d'où $m_i = n_i$.

#card("calcpmatdz", "Calcul de puissance de matrice : cas diagonalisable", ("Maths.Algèbre.Réduction",))

Méthodes de calcul des puissances d'une matrice diagonalisable.

#answer

Soit $A in M_n (KK)$ diagonalisable.

+ Matrice diagonale :

  On dispose de $P in "GL"_n (KK)$ (à calculer) tel que
  $
    A &= P dmat(alpha_1, dots.down, alpha_n) P^(-1) \
    A^k &= P dmat(alpha_1^k, dots.down, alpha_n^k) P^(-1)
  $

+ Lagrange : notons $d = deg Pi_A$ #h(1fr)
  $
    A^k in KK[u] = "Vect"(I_n, A, dots, A^(d-1)) \
  $
  Donc on dispose de $P in KK_(d-1) [X]$ tel que $A^k = P(A)$.

  Explicitons le :
  $
    KK^n = plus.o.big_(i = 1)^N E_lambda_i
  $
  Soit $X in KK^n$
  $
    X = underbrace(X_1, in E_lambda_1) + dots.c + underbrace(X_d, in E_lambda_d) \
    A X = lambda_1 X_1 + dots.c + lambda_d X_d \
    A^k X = lambda_1^k X_1 + dots.c + lambda_d^k X_d \
    P(A) X = P(lambda_1) X_1 + dots.c + P(lambda_d) X_d \
  $
  Ainsi avec $P$ construit par interpolation de Lagrange afin de vérifier
  $
    forall i in [|1, d|], space P(lambda_i) = lambda_i^k \
    P in KK_(d - 1) [X]
  $
  On a alors $P(A) X = A^k X$ pour tout $X$, d'où $P(A) = A^k$.

#card("calcpmatde", "Calcul de puissance de matrice : polynôme annulateur", ("Maths.Algèbre.Réduction",))

Méthodes de calcul des puissances d'une matrice grâce à un polynôme annulateur.

#answer

Soit $A in M_n (KK)$, $P in KK[X]$ annulateur de degré $d$.
$
  X^k = Q P + R \
  A^k = underbrace(Q P (A), 0) + R(A)
$
Avec $R in KK_(d-1) [X]$.

Si $P = (X - lambda)^m$ on trouve le reste de la division euclidienne grâce à la formule de Taylor :

$
  Q &= overbrace(sum_(k = 0)^(m-1) (Q^((k)) (lambda)) / k! (X - lambda)^k, "reste") \
  &+ (X - lambda)^m underbrace(sum_(k = m)^(deg Q) (Q^((k)) (lambda)) / k! (X - lambda)^(k - m), "quotient") \
  A^p &= sum_(k = 0)^(m - 1) vec(p, k) lambda^(p - k)(A - lambda I_n)^(k)
$

#card("eqmat", "Équations matricielles", ("Maths.Algèbre.Réduction",))

Méthodes de résolutions d'équations matricielles.

#answer

Soit $A in M_n (KK), P in KK[X]$.

On cherche à résoudre les équations de la forme
$
  P(M) = A
$
*Idées*
- $M A = A M$ car $A in KK[M]$.

- Ainsi $M$ laisse stable
  - Les sous-espaces propres de $A$
  - Les sous-espaces caractèristiques de $A$
  - Tout les $ker Q(A)$

- Pour $Q$ annulateur de $A$, $Q compose P$ est annulateur de $M$ : si $Q compose P$ est SARS, $M$ est diagonalisable.

*Résolutions cas simple*

Si $chi_A$ SARS :
$
  chi_A = product_(k = 1)^n (X - lambda_k) \
  A = R dmat(lambda_1, dots.down, lambda_n) R^(-1) \
  R = mat(C_1, dots.c, C_n)
$
Avec $C_1, dots, C_n$ vecteurs propres associés aux $lambda_1, dots, lambda_n$.

Si $M$ est solution, $M$ laisse stable tout les $E_lambda_k = "Vect"(C_k)$
$
  M C_k = mu_k C_k \
  M = R dmat(mu_1, dots.down, mu_n) R^(-1)
$
Or
$
  P(M) &= R dmat(P(mu_1), dots.down, P(mu_n)) R^(-1) \
  &= A
$
D'où $P(mu_k) = lambda_k$ pour tout $k in [|1,n|]$.

#card("eqmatxk", "Racine k-ème de matrices", ("Maths.Algèbre.Réduction",))

Méthodes général de résolution de l'équation $M^p = A$.

#answer

Soit $A in M_n (KK)$ et $p in NN$.

- Si $A$ est nilpotent : il peut ne pas exister de solutions, par exemple :

  Si $A$ nilpotent d'ordre $n$ et $p >= 2$
  $
    A^n = (M^p)^n = 0
  $
  D'où $M$ nilpotent
  $
    M^n = A^ceil(n / p) = 0
  $
  Absurde.

- Cas $A = I_n + N$ avec $N$ nilpotent.

  Idée : DL de $(1+x)^(1/k)$
  $
    (1 + x)^(1/k) = P_k (x) + o_(x->0) (x^(n-1)) \
    P_k (X) = 1 + sum_(j = 1)^(n-1) product_(i = 0)^(n-1) (1 / k - i) x^j / j! in RR_(n-1) [X] \
  $
  $
    1 + x &= (P_k (x) + o_(x->0)(x^(n-1)))^k \
    &= Q_k (x) + o_(x->0) (x^(n-1))
  $
  Par unicité de la partie principale du DL :
  $
    1 + X = Q_k (X)
  $
  Où $Q_k$ est $P_k^k$ tronqué à $n - 1$ termes
  $
    1 + X = P_k^k (X) - X^n R_k (X) \
    A = I_n + N = P_k^k (N) - underbrace(N^n R_k (N), 0)
  $
  D'où $P_k (N)$ est solution.
- Cas $A in M_n (CC)$ tel que $0 in.not "Sp"(A)$ :
  Pour tout $k in NN^star$ :

  $
    chi_A = product_(k = 1)^q (X - lambda_k)^(m_k) \
    A = P dmat(lambda_1 I_m_1 + N_1, dots.down, lambda_q I_m_q + N_q) P^(-1)
  $
  Pour tout $j in [|1, q|]$, on dispose de $accent(M,~)_j$ et $mu_j$ tels que
  $
    mu_j^k = lambda_j \
    accent(M,~)_j^k = I_m_j + 1/lambda_j N_j \
  $
  On définit alors
  $
    M_j &= mu_j accent(M,~)_j \
    M_j^k &= mu_j^k I_m_j + mu_j^k / lambda_j N_j \
    &= lambda_j I_m_j + N_j
  $
  Ainsi
  $
    M = P dmat(M_1, dots.down, M_q) P^(-1) \
  $
  Est solution :
  $
    M^k &= P dmat(M_1^k, dots.down, M_q^k) P^(-1) \
    &= A
  $

#card("exoquejspoumettre", "Exercice : lien entre diagonalisabilité d'un endomorphisme et son carré", ("Maths.Algèbre.Réduction",))

Soit $u in cal(L)(E)$ où $E$ est un $CC$-ev, montrer que
$
  u "diagonalisable" \ <=> cases(space u^2 "diagonalisable", space ker u = ker u^2)
$

#answer

- Supposons $u$ diagonalisable, on dispose de $e$ base de $E$ tel que
  $
    cal(M)_e (u) = dmat(lambda_1, dots.down, lambda_n) \
    cal(M)_e (u^2) = dmat(lambda_1^2, dots.down, lambda_n^2) \
  $
  D'où $u^2$ diagonalisable, et de plus $ker u subset.eq ker u^2$.

  Posons $k in [|0, n|]$ tel que 
  $
  lambda_1 = dots.c = lambda_k = 0 \
  lambda_(k+1), dots, lambda_n != 0
  $
  On a bien $ker u^2 = ker u$ (Vision matricielle).

- Supposons $0 in.not "Sp"(u)$, $u^2$ diagonalisable et $ker u^2 = ker u$.
  $
    Pi_(u^2) = product_(k = 1)^q (X - lambda_k) \
    Pi_(u^2) (u^2) = product_(k = 1)^q (X - delta_k)(X + delta_k) (u) = 0
  $
  Avec $delta_k^2 = lambda_k$. Ainsi $u$ est annuler par un polynôme SARS, donc diagonalisable.

- Supposons $0 = lambda_1 in "Sp"(u)$, $u^2$ diagonalisable et $ker u^2 = ker u$.
  $
    E &= plus.o.big_(k = 1)^q ker (u^2 - lambda_k id) \
    &= plus.o.big_(k = 2)^q ker (u^2 - lambda_k id) plus.o ker u^2\
    &= plus.o.big_(k = 2)^q ker (u - delta_k id)(u + delta_k id) \
    &plus.o underbrace(ker u^2, ker u) \
  $
  D'où $u$ diagonalisable.
// TODO: Exo 16/17 cf photos
#card("rechhypstab", "Recherche d'hyperplans stables", ("Maths.Algèbre.Réduction",))

Méthodes de recherche d'hyperplans stables.

#answer

Soit $A in M_n (KK)$, $H$ hyperplan de $KK^n$.

On dispose de $L in M_(1 n) (KK)$ tel que
$
  H = Set(X in KK^n, L X = 0) = ker L
$
$H$ est stable par $A$ ssi
$
  L^T "vecteur propre de" A^TT
$

*Démonstration*

$
  A H subset.eq H <=> ker L subset.eq ker L A \
  <=> exists lambda in KK, L A = lambda L \
  <=> exists lambda in KK, A^TT L^TT = lambda L^TT
$

#card("polcarabba", "Pseudo-commutativité du polynôme caractèristique", ("Maths.Algèbre.Réduction",))

Pour $A in M_(p n) (KK)$ et $B in M_(n p) (KK)$, lien entre $chi_(A B)$ et $chi_(B A)$.

#answer

Soient $A in M_(p n) (KK)$ et $B in M_(n p) (KK)$.
$
  A B in M_p (KK) quad quad B A in M_n (KK) \
  X^n chi_(A B) = X^p chi_(B A) \
  "Sp"(A B) \\ {0} = "Sp"(B A) \\ {0} \
  forall lambda in KK\\{0}, \ dim E_lambda (A B) = dim E_lambda (B A)
$
Si $p = n$ ($A$ et $B$ sont carrés) alors
$
  chi_(A B) = chi_(B A)
$

*Démonstration*

- Cas $A = J_r$ : #h(1fr)
  $
    A &= mat(augment: #(hline: 1, vline: 1), I_r, 0; 0, 0) quad quad
    &B &= mat(augment: #(hline: 1, vline: 1), B_1, B_2; B_3, B_4) \
    A B &= mat(augment: #(hline: 1, vline: 1), B_1, B_2; 0, 0)  quad quad
    &B A &= mat(augment: #(hline: 1, vline: 1), B_1, 0; B_3, 0) \
  $
  $
    chi_(A B) &= chi_B_1 X^(p - r) \
    chi_(B A) &= chi_B_1 X^(n - r) \
  $

- Cas général : $A = P J_r Q$
  $
  A B &= P J_r Q B \
  &= P (J_r Q B P) P^(-1) \
  B A &= B P J_r Q \
  &= Q^(-1) (Q B P J_r) Q
  $
  Donc
  $
    X^n chi_(A B) &= X^n chi_(J_r Q B P) \
    &= X^p chi_(Q B P J_r) = X^p chi_(B A)
  $

- Pour tout $X in E_lambda (A B)$
  $
    A B X = lambda X \
    B A B X = lambda B X \
    B X in E_lambda (B A) \
  $
  Ainsi
  $
    theta : func(E_lambda (A B), E_lambda (B A), X, B X)
  $
  Est linéaire injectif, donc
  $
    dim E_lambda (B A) >= dim E_lambda (A B)
  $
  Avec égalité par symétrie.

#card("redmatrg1", "Réduction de matrice dans rang 1", ("Maths.Algèbre.Réduction",))

Propriétés de réduction de matrices de rang $1$. 

#answer

Soit $A in M_n (KK)$ tel que $"rg" A = 1$.

+ On dispose de $L in M_(1 n) (KK), C in M_(n 1) (KK)$ tels que $A = C L$.

+ $A^2 = (tr A) A$.

+ $X(X - tr A)$ annule $A$.

+ Si $tr A != 0$, $A$ est diagonalisable.

+ Si $tr A = 0$, $A$ est nilpotente.

*Démonstration*

+ Comme $"rg" A = "rg" mat(C_1, dots.c, C_n) = 1$, on dispose de $k in [|1, n|]$ tel que ${C_1, dots, C_n} subset.eq "Vect"(C_k)$ : #h(1fr)
  $
    A &= mat(C_1, dots.c, C_n) = C_k mat(alpha_1, dots.c, alpha_n) \
    &= underbrace(vec(x_1, dots.v, x_n), C) underbrace(mat(alpha_1, dots.c, alpha_n), L)
  $

+ $
  A^2 = C underbrace(L C, tr A) L = (tr A) A
  $

+ Évident.

+ Si $tr A != 0$, $A$ est annuler par $X(X - tr A)$ SARS donc $A$ est diagonalisable.

+ Si $tr A = 0$, $X^2$ annule $A$, donc $A$ est nilpotente.

#card("suitreclin", "Suites récurrentes linéaires", ("Maths.Algèbre.Réduction", "Maths.Analyse.Suites"))

Propriétés, méthodes d'étude de suites récurrentes linéaires.

#answer

Pour tout $(x_0, dots, x_(p-1)) in KK^p$, pour tout $n in NN$ on définit la suite $(x_n)_n in KK^NN$
$
  x_(n + p) = sum_(k = 0)^(p-1) a_k x_(n + k) quad (*) \
  cal(S) = Set((x_n)_n in KK^NN, (*)) \
  dim cal(S) = p
$
Où $cal(S)$ est un $KK$-ev.

$
  A = mat(augment: #(hline: 3), 0, 1;,dots.down, dots.down;,,0,1;a_0, a_1, dots.c, a_(p - 1)) = C_P^TT \
  P = X^p - sum_(k = 0)^(p-1) a_k X^k
$
Ainsi si $X_n = vec(X_n, dots.v, X_(n + p))$
$
  A X_n = X_(n+1) \
  X_n = A^n X_0
$
Si $chi_A$ est SARS
$
  chi_A = product_(k = 1)^p (X - lambda_k) \
 cal(S) = "Vect" ((lambda_k^n)_(n in NN))_(k in [|1, p|])
$

*Démonstration*

- Si $P = chi_C_P = chi_A$ est SARS #h(1fr)
  $
    X^p - sum_(k = 0)^(p-1) a_k X^k = product_(k = 1)^p (X - lambda_k)
  $
  $A$ est diagonalisable comme $chi_A$ est SARS
  $
    A = Q dmat(lambda_1, dots.down, lambda_p) Q^(-1) \
    A^n = sum_(k = 1)^p lambda_k^p Pi_k
  $
  Où les $Pi_k$ sont les projecteurs issus de la décomposition en sous-espaces propres.
  $
    vec(x_n, dots.v, x_(n+p)) &= X_n = A^n X_0 \
    &= sum_(k = 1)^p lambda_k^n Pi_k X_0 \
    x_n &= sum_(k = 1)^p lambda_k^n gamma_k \
    (x_n)_n &= sum_(k = 1)^p gamma_k (lambda_k^n)_n \
    &in "Vect" ((lambda_k^n)_(n in NN))_(k in [|1, p|])
  $
  Soit $k in [|1, p|]$
  $
    chi_A (lambda_k) = 0 \
    "Donc " lambda_k^p = sum_(i = 0)^(p-1) a_i lambda_k^i \ 
    forall n in NN, space lambda_k^(p + n) = sum_(i = 0)^(p-1) a_i lambda_k^(n + i) \
    (lambda_k^n)_(n in NN) in cal(S)
  $

- Sinon 
  $
    P = product_(k = 1)^q (X - lambda_k)^(m_k)
  $
  Posons
  $
    delta : func(KK^NN, KK^NN, (y_n)_n, (y_(n+1))_n)
  $
  Ainsi on a
  $
    cal(S) &= ker P(delta) \
    &= plus.o.big_(k = 1)^q ker (delta - lambda_k)^(m_k)
  $
  - Montrons que $(n^d lambda_k^n)_n in ker (delta - lambda_k id)^(m_k) subset.eq ker P(delta) = cal(S)$ :

    Définissons d'abord
    $
      Delta : func(KK[X], KK[X], P(X), P(X+1) - P(X))
    $
    On remarque que
    $
      P = sum_(k = 0)^d a_k X^k \
    $
    $
      Delta (P) &= sum_(k = 0)^d a_k [(X + 1)^k - X^k] \
      &= sum_(k = 0)^d a_k [sum_(i = 0)^(k - 1) underbrace(X^(k - 1 - i) X^i, deg <= k - 1)] \
      deg Delta (P) &<= deg P - 1
    $
    Ainsi $Delta^(d+1) P = 0$.
    
    Alors pour tout $k in [|1, q|]$, $P in KK_(m_k - 1) [X]$
    $
      (delta - lambda_k id) (P(n) lambda_k^n)_n \
      = ([P(n+1) - P(n)] lambda_k^(n+1))_n \
      = (Delta(P)(n) lambda_k^(n+1))_n
    $
    Donc 
    $
    (delta - lambda_k)^(m_k) (P(n) lambda_k^n)_n \
      = (Delta^(m_k)(P)(n) lambda_k^(n+1))_n \
      = 0
    $
    Ainsi pour $P(X) = X^d$ avec $d in [|0, m_k - 1|]$, $
    (n^d lambda_k^n)_n in ker (delta - lambda_k id)^(m_k) 
    $

  - Montrons que la famille $((n^d lambda_k^n)_(n in NN))_(d in [|0, m_k - 1|])$ est libre.

    Notons $u_d = (n^d lambda_k^n)_(n in NN) $.

    Supposons
    $
      sum_(i = 0)^(m_k - 1) gamma_i u_i = 0
    $
    Alors pour tout $n in NN$
    $
      underbrace((sum_(i = 0)^(m_k - 1) gamma_i n^i), P_k (n)) underbrace(lambda_k^n, != 0) = 0
    $
    Et $P_k$ est un polynôme qui s'annule sur $NN$ entier, et est donc nul.

  Donc on dispose de bases des $ker (delta - lambda_k id)^(m_k)$
  $
    cal(S) = "Vect"((n^d lambda_k^n)_(n in NN))_(d in [|0, m_k - 1|] \ k in [|1, q|])
  $
]
#[

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

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

  Soit $partial$ tel que $partial | a$ et $partial | b$. $forall x in I, partial | x$, en particulier $partial | d$ d'où $partial <= d$.

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
$
A attach(t: sscript(L\,C), ~) B space "ssi" "rg" A = "rg" B
$
$
"rg"(phi compose psi) &= "rg" psi - dim(ker phi inter im phi) \ &<= min("rg" phi, "rg" psi)
$

#card("forml", "Formes lineaires et hyperplans", ("Maths.Algèbre.Espaces Vectoriels",))

Formes lineaires et hyperplans.

#answer

Soit $E$ un $KK$-ev

Un hyperplan de $E$ est un sev de codimension $1$, c'est à dire qui admet un supplémentaire de dimension $1$.

- Si $alpha in E^star\\{0}$, alors $ker alpha$ est un hyperplan.
- Si $H$ est un hyperplan de $E$, il existe une forme linéaire $alpha$ unique à constante multiplicative prés tel que $H = ker alpha$.

Deux hyperplans on toujours un supplémentaire commun.

*Démonstration*

- Si $H_1$ et $H_2$ sont des hyperplans, $H_1 union H_2 != E$ 

  - Par l'absurde : supposons $H_1 union H_2 = E$ sev de $E$

    Or $H_1 union H_2 = (H_1 "ou" H_2) = E$ (cf unions de sev) qui est absurde.

  Donc on dispose de $x_0 in E\\(H_1 union H_2)$ 

  Ainsi $"Vect"(x_0)$ est un supplémentaire de $H_1$ et $H_2$

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

*Entiers algébrique de degré 2*

2. $alpha in CC$ entier algébrique de degré $2$ : on dispose de $pi_alpha in ZZ[X]$ unitaire de degré $2$ qui annule $alpha$. $ZZ[alpha] = im theta_alpha$ est un sous-anneau de $RR$ (et donc de $CC$).

+ $ZZ[alpha] = {x + alpha y, (x, y) in ZZ^2}$ et tout élément s'écrite de manière unique sous cette forme.

+ On peut écrire 
  $
  pi_alpha = (X - alpha)(X - beta)
  $
  
  On remarque que $beta in ZZ[alpha]$ car $alpha + beta = a in ZZ$ d'où $beta = a - alpha in ZZ[alpha]$.

  On définit
  $
    tau : func(ZZ[alpha], ZZ[alpha], x + alpha y, x + beta y)
  $

  On a alors

  $
    forall z, z' in ZZ[alpha], space tau(z z') = tau(z) tau(z')
  $

+ Et on peut alors définir

  $
    N : func(ZZ[alpha], ZZ, z = x + alpha y, z tau(z))
  $

  Qui est aussi multiplicatif.

+ $z in ZZ[alpha]$ est inversible ssi $N(z) = abs(1)$.

*Démonstration*
+ Notons $P_alpha$ ce polynôme, comme $Q(alpha) = 0, P_alpha | Q$ dans $QQ[X]$, d'où 
  $
  ZZ[X] in.rev Q = P_alpha R in QQ[X]
  $

  Et donc $P_alpha, R in ZZ[X]$ car $Q$ unitaire (cf. exercices sur le contenu).

3. $alpha$ de degré $2$ donc 
  $
  pi_alpha (X) = X^2 + a X + b
  $
  
  - On a déjà ${x + alpha y, (x, y) in ZZ^2} subset.eq ZZ[alpha]$.

  - Soit $x = P(alpha) in ZZ[alpha]$, $P = Q pi_alpha + R$ avec $Q in KK[X], R in KK_1 [X]$.

    Donc
    $
      R = y X + x in ZZ[X] \
      P(alpha) = underbrace(Q(alpha) pi_alpha(alpha), 0) + y alpha + x
    $

  - Soit $x_1 + alpha y_1 = x_2 + alpha y_2$ avec $x_1, x_2, y_1, y_2 in ZZ$.

    $
      x_1 - x_2 = (y_2 - y_1) alpha
    $

    Par l'absurde, si $y_1 != y_2$ :

    $
      alpha = (x_1 - x_2) / (y_2 - y_1) in QQ[X]
    $

    Qui est absurde car $pi_alpha$ serait de degré $1$.

+ Soit $z = x + alpha y, z' = x' + alpha y'$ \

  On a $alpha^2 = a alpha - b$ et $beta^2 = a beta - b$ donc

  $
    tau(z z') &= tau(x x' + alpha (x y' + x' y) + alpha^2 y y') \
&= tau(x x' - b y y' + alpha (x y' + x y' + a y y')) \
&= x x' - b y y' + beta (x y ' + x' y + a y y') \
&= (x + beta y) (x' + beta y) \
&= tau(z) tau(z')
  $

+ Soit $z = x + alpha y in ZZ[alpha]$

  $
    N(z) = z tau(z) &= (x + alpha y)(x + beta y) \ 
&= x^2 + (alpha + beta) x y + alpha beta y^2 \
&= x^2 = a x y + b y^2 in ZZ
  $

+ - Soit $z in ZZ[alpha]$ inversible, on dispose de $z' in ZZ[alpha]$ tel que $z z' = 1$.

    $
      N(z z') = N(1) = 1 = N(z) N(z')
    $

    Donc $abs(N(z)) = 1$

  - Soit $z in ZZ[alpha]$ tel que $N(z) = epsilon in {1, -1}$

    $
      (x + alpha y)(x + beta y) = epsilon \
      z (epsilon x + epsilon beta y) = 1 = epsilon^2 \
z^(-1) = epsilon(x + beta y)
    $

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

On a évidement $B^times subset B inter A^times$.

On suppose $b in B inter A^times$, on dispose de $a in A, a b = b a = 1$.

On pose
$
  phi_b = func(B, B, x, b x) in cal(L)(B)
$

Soit $x in ker phi_b$, on a $b x = 0$ donc $(a b) x = x = 0$.

Donc $phi_b$ bijectif (argument dimensionnel), et $phi_b^(-1)(1) = a$ existe et $a in B$.

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
    KK[X] = B KK[X] plus.o KK_(d - 1) [X]
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
    KK[X] = pi_alpha KK[X] plus.o KK_(d - 1) [X]
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

#card("gaussluca", "Exercice : Gauss-Lucas", ("Maths.Exercice.Polynômes",))

Soit $P in CC[X]$, montrer que les racines de $P'$ sont dans l'enveloppe convexe des racines de $P$.

#answer

Soit $P in CC[X]$, montrer que les racines de $P'$ sont dans l'enveloppe convexe des racines de $P$.

On écris

$
  P = c product_(k = 1)^N (X - a_k)^(m_k)
$
Soit $b$ une racine de $P'$.

Si $b in {a_1, dots, a_N}$, b est nécéssairement dans leur enveloppe convexe.

Sinon

$
  P' / P = sum_(k = 1)^n m_k / (X - a_k) \
$
$
  0 &= P' / P (b)
= sum_(k = 1)^N m_k / (b - a_k)
= sum_(k = 1)^N m_k / overline(b - a_k) \
&= sum_(k = 1)^N m_k / abs(b - a_k)^2 (b - a_k) \
b &= (sum_(k = 1)^N (a_k m_k) / abs(b - a_k)^2) / (sum_(k = 1)^N m_k / abs(b - a_k)^2) \
 &= sum_(k = 1)^N lambda_k a_k
$

Où $lambda_k = (a_k m_k) / abs(b - a_k)^2 / (sum_(i = 1)^N m_i / abs(b - a_i)^2)$ (on a alors $sum_(k = 1)^N lambda_k = 1$).

$b$ est donc un barycentre à coéfficients positifs des $a_1, dots, a_n$ et est donc dans leur enveloppe convexe.

#card("exdenommorp", "Exercice : Dénombrement de morphismes", ("Maths.Exercice.Algèbre Générale",))

+ Dénombrer les morphismes de $G_1$ vers $G_2$, avec $abs(G_1) and abs(G_2) = 1$.

+ Dénombrer les morphismes de $G_1$ vers $G_2$ où $G_1$ et $G_2$ sont cyclique.

+ Même chose avec les injections et les surjections.

#answer

*Remarque générale*

Soit $phi : G_1 -> G_2$ morphisme de groupe, $x in G_1$

$
  phi(x)^("ord"(x)) = e_G_2 \
  "donc" "ord"(phi(x)) | abs(G_2) \
  "et" "ord"(phi(x)) | abs(G_1) 
$

Ainsi $"ord"(phi(x)) | abs(G_1) and abs(G_2)$.

*Exercices*

+ Soit $phi : G_1 -> G_2$ morphisme, $x in G_1$. Par la remarque ci dessus $"ord"(phi(x)) | p and q = 1$ donc $phi(x) = 0$, il n'y a donc que morphisme le morphisme triviale.

+ Notons $G_1 = gen(a)$, posons

  $
    theta : func(hom(G_1, G_2), G_2, phi, phi(a))
  $

  Qui est injectif car tout morphisme est uniquement déterminé par son image du générateur $a$.

  Pour tout $phi in hom(G_1, G_2)$ on a

  $
    phi(a)^abs(G_1) = phi(a^abs(G_1)) = phi(e_G_1) = e_G_2
  $

  D'où

  $
    im theta subset { y in G_2 | y^abs(G_1) = e_G_2 }
  $

  Soit $y in im theta$ posons

  $
    phi : func(G_1, G_2, x = a^k, y^k)
  $

  Qui ne dépend pas du $k$ choisi, soit $x = a^k = a^l$ :

  $
    a^(k - l) = e_G_1 \
    "donc" abs(G_1) | k - l \
    "et" y^(k - l) = e_G_2 \
    "d'où" y^k = y^l
  $

  Donc $theta (phi) = y$.

  $
    &abs(hom(G_1, G_2)) \ &= abs(im theta) \
&= abs({y in G_2 | y^abs(G_1) = e_G_2}) \
&= abs({y in G_2 | "ord"(y) | abs(G_1)}) \
&= union.big.plus_(d | abs(G_1)) {y in G_2 | "ord"(y) = d} \
&= sum_(d | abs(G_1) and abs(G_2)) phi(d) \
&= abs(G_1) and abs(G_2)
  $

+ - Pour les injections on veut $phi in hom(G_1, G_2)$ tels que $ker phi = {e_G_1}$.

  Pour $k in [|1, abs(G_1) - 1|]$,

  $
    phi(a)^k = phi(a^k) != 0 \
    "ord" phi(a) = abs(G_1)
  $

  Si $abs(G_1) divides.not abs(G_2)$, $G_2$ ne contient pas éléments d'ordre $abs(G_1)$ donc auncune injection.

  Si $abs(G_1) divides abs(G_2)$, il y a $phi(abs(G_1))$ éléments d'ordre $abs(G_1)$, donc autant d'injections.

  - Pour les surjections on veut $"ord" phi(a) = abs(G_2)$, donc 

    $
    cases(space 0 &"si" abs(G_2) divides.not abs(G_1), space phi(abs(G_2)) space &"sinon")  
    $

#card("exunionsev", "Exercice : Union de sous espaces vectoriels", ("Maths.Exercice.Algèbre Linéaire",))

$E$ un $KK$ espace vectoriel.

+ Soit $F, G$ deux sev de $E$, montrer que $F union G$ sev ssi $F subset.eq G$ ou $G subset.eq F$.

+ Supposons $KK$ infini, soit $F_1, dots, F_n$ $n$ sevs, montrer que si $union.big_(k = 1)^n F_k$ est un sev, alors il existe $i in [|1, n|]$ tel que 
  
  $
  union.big_(k = 1)^n F_k = F_i
  $

#answer

+ Soit $F, G$ sevs de $E$ un $KK$-ev tel que $F union G$ est un sev.

  Si $F subset.eq.not G$, on pose $z in F\\G$, soit $x in G$.

  $
    x + z in F union G
  $

  $x + z in.not G$ car sinon 
  $
  F\\G in.rev z = underbrace((x + z), in G) - underbrace(x, in G) in G
  $
  Donc $x + z in F$ d'où
  $
    x = (x + z) - z in F
  $

  Et $G subset.eq F$.

+ Soient $F_1, dots, F_n$ sevs de $E$ tels que $union.big_(k = 1)^n F_k$ est un sev.

  Notons $U_m = union.big_(k = 1)^m F_k$ pour $m in NN$.

  On à déjà fait le cas $n = 2$ et le cas $n = 1$ est trivial.

  Supposons la propriété vraie pour un $n in NN$.

  Si $U_n subset.eq F_(n+1)$ alors on a fini.

  Si $F_(n+1) subset.eq U_n$ alors par hypothèse de récurrence, on dispose de $i in [|1, n|]$
  $
    U_(n+1) = U_n = F_i
  $

  Sinon, on dispose de 
  $
    x in F_(n+1)\\U_n subset.eq U_(n+1) \
    y in U_n\\F_(n+1) subset.eq U_(n+1)
  $

  Soient $lambda_0, dots, lambda_(n+1) in KK$ deux à deux distincts.
  $
    z_k = x + lambda_k y
  $
  Par le lemme des tiroirs, on dispose de $k != l$ et $j$ tel que $z_k, z_l in F_j$

  Si $j = n+1$
  $
    z_k - z_l = underbrace((lambda_k - lambda_l), != 0)y in F_(n+1)
  $
  Et $y in F_(n+1)$ impossible.

  Si $j in [|1,n|]$
  $
    lambda_l z_k - lambda_k z_l = underbrace((lambda_l - lambda_k), != 0) x in F_j
  $
  Et $x in F_j$ impossible.

#card("somdir", "Somme directe de sous espaces vectoriels", ("Maths.Algèbre.Algèbre Linéaire",))

Définition et propriétés de somme directe de sev.

#answer

Soient $F_1, dots, F_n$ sev de $E$ un $KK$-ev. On dit qu'ils sont en somme directe si pour tout $x in sum_(k = 1)^n F_k$

$
  exists! (x_1, dots, x_n) in product_(k = 1)^n F_k, space x = sum_(k = 1)^n x_k
$

Il y a équivalence entre $F_1, dots, F_n$ en somme directe et

+ $forall (x_1, dots, x_n) in product_(k = 1)^n F_k, space sum_(k = 1)^n x_k = 0 => forall k in [|1, n|], space x_k = 0$.

+ $forall i in [|1, n|], space F_i inter (sum_(i != k)^n F_k) = {0}$

+ $F_n inter plus.big_(k = 1)^(n-1) F_k = {0}$

*En dimension finie*

4. $dim sum_(k = 1)^n F_n <= sum_(k = 1)^n dim F_n$ avec égalité ssi les $F_1, dots, F_n$ sont en somme directe.

*Démonstration*

+ $=>$ il s'agit d'un cas particulier pour $x = 0$.
  
  $arrow.double.l$ Supposons $sum_(k = 1)^n x_k = sum_(k = 1)^n x'_k$

  Alors $sum_(k = 1)^n (x_k - x'_k) = 0$ donc $x_k = x'_k$ pour tout $k in [|1, n|]$.

3. $=>$ Soit $x in F_n inter plus.big_(k = 1)^n F_k$

  $
    x &= sum_(k = 1)^(n-1) 0 + x \ 
&= sum_(k = 1)^(n-1) x_k + 0 quad "car" x in plus.big_(k = 1)^(n-1) F_k
  $

  Donc par unicité de la décomposition $x = sum_(k = 1)^n 0 = 0$.

  $arrow.double.l$ Soit $x_1, dots, x_n in E$ tels que

  $
    sum_(k = 1)^n x_k = 0 \
  -x_n = sum_(k = 1)^(n-1) x_k in F_n inter plus.big_(k = 1)^(n - 1) F_k
  $

  Donc $x_n = 0$ et $sum_(k = 1)^(n-1) x_k = 0$ donc $x_1 = x_2 = dots.c = x_n = 0$.

#card("espsup", "Espaces supplémentaires", ("Maths.Algèbre.Algèbre Linéaire",))

Définition, propriétés des espaces supplémentaires.

#answer

Soient $F_1, dots, F_n$ sevs de $E$ un $KK$-ev. On dit qu'ils sont supplémentaires si
$
  E = plus.big_(k = 1)^n F_k
$

Et on a

$
E = plus.big_(k = 1)^n F_k \

<=> cases(space E = sum_(k = 1)^n F_k, space dim(E) = sum_(k = 1)^n dim(F_k))  \

<=> cases(space sum_(k = 1)^n F_k = plus.big_(k = 1)^n F_k, space dim(E) = sum_(k = 1)^n dim(F_k)) \
$

#card("notmat", "Notations de matrices", ("Maths.Algèbre.Algèbre Linéaire",))

Notations de matrices : changements de bases, matrices d'un endomorphisme, ...

#answer

Soit $u in cal(L)(E, F)$, $e = (e_1, dots, e_n), e' = (e'_1, dots, e'_n)$ bases de $E$ et $f = (f_1, dots, f_p)$ base de $F$.

*Applications linéaires*

$
  cal(M)_(e, f) (u) = cal(M)_(e <- f) (u) = cal(M)_e^f (u) in M_(p n) (KK) \
$
Et la matrice est alors
$
    cal(M)_(f <- e) (u) = mat(delim: #none, #diagram(
      spacing: 0pt,
      $
        node(enclose: #("tl", "bl"), lr(size: #600%, \())
        node(enclose: #("tr", "br"), lr(size: #600%, \))) \
        && u(e_1) & u(e_2) edge("rr", "..") & #h(0.6em) & u(e_n) & \
        f_1 & node(name: "tl") & a_11 & a_12 edge("rr", "..") && a_(1n) & node(name: "tr") \
        f_2 edge("dd", "..") && a_21 edge("dd", "..") & a_22 edge("dd", "..") edge("rr", "..") edge("drdr", "..") && a_(2n) edge("dd", "..") & \
        thin \
        f_p & node(name: "bl") & a_(p 1) & a_(p 2) edge("rr", "..") & & a_(p n) & node(name: "br")
      $
    ))
$

Où pour $j in [|1, n|]$

$
  u(e_j) = sum_(k = 1)^p  a_(k j) f_k
$

*Endomorphismes*

$
  cal(M)_e (u) = cal(M)_(e <- e) (u) = cal(M)_e^e (u) \
$

$
  u(e_j) = sum_(k = 1)^p  a_(k j) f_k
$

*Changement de base*

$
  P_(e -> e') = cal(M)_(e) (e') = cal(M)_(e <- e') (id)
$

#card("noyimgiter", "Exercice : Noyaux et images itérées", ("Maths.Exercice.Algèbre Linéaire",))

Soit $u in cal(L)(E)$ avec $E$ un $KK$-ev. Que peut on dire des suites $(ker u^k)_k$ et $(im u^k)_k$ ?

#answer

Soit $u in cal(L)(E)$ avec $E$ un $KK$-ev.

*Dimension quelconque*
- Si $ker u^k = ker u^(k+1)$ pour un $k in NN$ alors pour tout $n >= k$, $ker u^k = ker u^n$.
- De même pour les images.

*Dimension finie*

En notant $n = dim E$ on a
$
  d_k = dim ker u^k in [|0, n|] arrow.tr \
  r_k = "rg" u^k in [|0, n|] arrow.br
$

Ces deux suites sont donc stationnaires, on peut poser

$
  m_K &= min { k in NN | ker u^k = ker u^(k+1) } \
  m_I &= min { k in NN | im u^k = im u^(k+1) } \
$

On a de plus $m_K = m_I = m$.

Et en notant
$
  K = union.big_(k in NN) ker u^k = ker u^m \
  I = inter.big_(k in NN) im u^k = im u^m
$

Qui sont les valeurs auquelles les suites stationnent, on a

- $K plus.o I = E$

- $K, I$ stables par $u$

- $u|_(K)^(K)$ est nilpotent

- $u|_I^I$ est inversible.

- Si $E = K' plus.o I'$ avec $K', I'$ stables par $u$, $u|_K'^K'$ nilpotent et $u|_I'^I'$ inversible, alors $K' = K$ et $I' = I$.

*Démonstration*

- Soit $l >= k$, on a évidement $ker u^l subset.eq ker u^(l+1)$. #h(1fr)

  Soit $x in ker u^(l + 1)$ :
  $
    u^(k+1) (u^(l - k) (x)) = 0 \
    u^(l - k)(x) in ker u^(k+1) = ker u^k \
    u^k (u^(l - k) (x)) = 0 \
    x in ker u^l
  $

- Soit $l >= k$, on a évidement $im u^(l+1) subset.eq im u^l$. 

  Soit $u^l (x) = y in im u^l$ :
  $
    u^(l-k) (u^k (x)) = y \
    u^k (x) in im u^k = im u^(k+1) \
    u^k (x) = u^(k+1) (x') \
    u^(l - k) (u^(k+1) (x')) = y \
    y in im u^(l+1)
  $

*Dimension finie*

- Par le théorème de rang on a $d_k = n - r_k$, donc si $r_k$ est constante à partire du rang $m_I$, alors $d_k$ est aussi constante a partire de ce rang, donc $m_K = m_I$.

- Soit $y in K inter I$, on dispose de $x in E$ tel que

  $
    u^m (x) = y \
    u^m (y) = 0 \
    u^(2m) (x) = 0 \
    x in ker u^(2m) = ker u^m \
    u^m (x) = y = 0
  $

  donc $K plus.o I = E$.

- Soit $x in K = ker u^m$

  $
    u^m (u(x)) = u^(m+1) (x) = 0 
  $

  donc $u(x) in K$.

- Soit $y in I = im u^m$, on dispose de $x in E$ tel que

  $
    u^m (x) = y \
    u^(m+1) (x) = u(y) in im u^m \
    u(y) = u^m (x')
  $

  et $u(y) in I$.

- Notons $accent(u, ~) = u|_K^K$ l'endomorphisme induit par $u$ sur $K$.

  $
    accent(u, ~)^m (K) = u^m (K) = {0}
  $

  Donc $accent(u, ~)$ est nilpotent d'indice $m$.

- Notons $accent(u,~) = u |_I^I$ l'endomorphisme induit par $u$ sur $I$.

  $
    accent(u,~) (I) &= u (im u^m) = im u^(m+1) \
    &= im u^m = I
  $

  Donc $accent(u, ~)$ est inversible.

- Soit $K' plus.o I' = E$ qui respectent les hypothèses.

  On dispose de $d in NN^*$ tel que

  $
    u^d (K') = {0} \
    K' subset.eq ker u^d subset K = union.big_(k in NN) ker u^k
  $

  Et on a

  $
    u(I') = I' \
    u^m (I') = I' \
    I' subset.eq im u^m = I
  $

  Donc

  $
    dim K' <= dim K \
    dim I' <= dim I \
  $

  Et on obtient l'égalité par supplémentarité, d'où $K' = K$ et $I' = I$.

#card("detligcol", "Développement du déterminant par ligne ou par colonne", ("Maths.Algèbre.Algèbre Linéaire",))

Formules et définitions du développement du déterminant par ligne ou par colonne.

#answer

Soit $A in M_n (KK)$

- pour tout $j in [|1, n|]$ : #h(1fr)

  $
    det(A) = sum_(i = 1)^n (-1)^(i + j) a_(i j) det(accent(A, ~)_(i j))
  $

- pour tout $i in [|1, n|]$ : #h(1fr)

  $
    det(A) = sum_(j = 1)^n (-1)^(i + j) a_(i j) det(accent(A, ~)_(i j))
  $

Où $accent(A, ~)_(i j) in M_(n - 1) (KK)$ est la matrice $A$ privée de sa $i$#super[ème] ligne et $j$#super[ème] colonne.

On appelle $accent(A,hat)_(i j) = (-1)^(i + j) det (accent(A, ~)_(i j))$ cofacteur.

On appelle $"com"(A)$ la matrice des cofacteurs.

Et on a

$
  A dot "com"(A)^T = det(A) I_n
$

// TODO: Démo de tout ça ?

#card("exrgcom", "Exercice : rang d'une comatrice", ("Maths.Exercice.Algèbre Linéaire",))

Soit $A in M_n (KK)$ ($n >= 3$), calculer $"rg" "com"(A)$ en fonction de $"rg" A$.

#answer

Soit $A in M_n (KK)$ avec $n >= 3$.

- Si $"rg" A = n$, $A in "GL"_n (KK)$ donc $"com" A in "GL"_n (KK)$ et $"rg" "com"(A) = n$.

- Si $"rg" A <= n - 2$, pour tout $i, j in [|1, n|]$ la matrice $accent(A, ~)_(i j)$ extraite de $A$ privée de sa $i$#super[ème] ligne et $j$#super[ème] colonne est de rang inférieur à $n - 2$ et n'est donc pas inversible, $"com" A = 0$ et $"rg" "com"(A) = 0$.

- Si $"rg" A = n - 1$, on dispose d'une matrice éxtraite de taille $n - 1$ inversible, donc au moins un des cofacteur est non nul d'où $"rg" "com"(A) >= 1$.

  De plus 
  $
    A_T "com"(A) = det(A) I_n = 0
  $
  Donc $im "com" (A) subset.eq ker A^T$ et $dim ker A^T = 1$ d'où $"rg" "com" (A) <= 1$.

#card("algopivgau", "Algorithme du pivot de Gauss", ("Maths.Algèbre.Algèbre Linéaire",))

Déscription de l'algorithme du pivot de Gauss, et propriétés qui en découlent.

#answer

*Opérations, représentation matricielle*

Notons $(E_(i j))_(i j)$ la base cannonique de $M_n (KK)$. On a

$
  E_(i k) E_(l j) = delta_(k l) E_(i j)
$

Pour $A in M_(n p) (KK)$
$
  E_(k l)^((n)) A = mat(augment: #1,,1;, dots.v; L_l, k;,dots.v;,n) \
  A E_(k l)^((p)) = mat(augment: #("hline": 1),,,C_k,,;1,dots.c,l,dots.c,n)
$

Ainsi on peut définir

- $T_(k l) (lambda) = I_n + lambda E_(k l)^((n))$ la transvection sur les lignes ($L_k <- L_k + lambda L_l$)

- $T'_(k l) (lambda) = I_p + lambda E_(k l)^((p))$ la transvection sur les colonnes ($C_l <- C_l + lambda C_k$)

- $P_(k l) = I_n - E_(k k)^((n)) - E_(l l)^((n)) + E_(k l)^((n)) + E_(l k)^((n))$ la transposition de lignes ($L_l <-> L_k$)

- $P_(k l) = I_p - E_(k k)^((p)) - E_(l l)^((p)) + E_(k l)^((p)) + E_(l k)^((p))$ la transposition de colonnes ($C_l <-> C_k$)

*Algorithme*

Prenons $A = mat(C_1, dots.c, C_n) in M_n (KK)$

- Si $A = 0$ fini.

- Soit $j = min {k in [|1, n|] | C_k != 0}$ #h(1fr)

  $
  A^((1)) : quad C_j <-> C_1
  $

- Soit $i = min {k in [|1, n|] | a_(i 1) != 0}$

  - Si $i = 1$ on effectue $L_2 <- L_2 + L_1$ et on prend $i = 2$.

  $
    A^((2)) : quad L_1 <- L_1 + (1 - a_(1 1) / a_(i 1)) L_i \

    A^((2)) = mat(augment: #("hline": 1, "vline": 1), 1, *, dots.c, *; *;dots.v,,*;*)
  $

- Pour tout $i in [|2, n|]$ on effectue

  $
    A^((i + 1)) : quad L_i <- L_i - a_(i 1) L_1 \
  $
  Ainsi
  $
    A^((n + 1)) = mat(augment: #("hline": 1, "vline": 1), 1, *, dots.c, *; 0;dots.v,,accent(A,~);0)
  $

On repète l'algorithme sur $accent(A,~)$, on obtient alors

$
  accent(accent(A, ~),~) = mat(augment: #("hline": (4, 3), "vline": (4, 3)),
    1,,(*),*;
    ,dots.down,,dots.v,,(*);
    ,,1,*;
    ,,,mu,*,dots.c,*;
    ,,,,0;
    ,,,,,dots.down;
    ,,,,,,0
  )
$

Avec $mu != 1$ ssi le blocs de zéros à la fin est de taille nulles (on ne dispose pas des lignes nécéssaires pour se ramener à $mu = 1$).

On peut alors finalement effectuer pour tout $i in [|1, "rg" A|]$, puis pour $j in [|i + 1, n|]$

$
  accent(accent(accent(A,~),~),~) : quad C_j <- C_j - accent(accent(A,~),~)_(i j) / (accent(accent(A,~),~)_(i i)) C_i \
  accent(accent(accent(A,~),~),~) = mat(
    1;
    ,dots.down;
    ,,1;
    ,,,mu;
    ,,,,0;
    ,,,,,dots.down;
    ,,,,,,0
  )
$

On remarque que si $A$ est inversible, les transpositions sont inutiles car il n'éxiste pas de colonnes nulles.

*Propriétés*

- Les transvections engendrent $"SL"_n (KK)$.

- Les transvections et une dilatation (pour atteindre n'importe quel déterminant) suffisent à engendrer $"GL"_n (KK)$.

#card("interhyppl", "Intersection d'hyperplans", ("Maths.Algèbre.Algèbre Linéaire",))

Propriétés sur les intersections d'hyperplans.

#answer

Soient $(phi_1, dots, phi_p) in cal(L)(E, KK)^p$

$
  dim inter.big_(k = 1)^p ker phi_k &= n - "rg"(phi_1, dots, phi_p) \
  &>= n - p
$

*Démonstration*

On montre l'inégalité par récurrence sur $p$.

Montrons l'égalité.

Quitte à extraire et renuméroter, $(phi_1, dots, phi_r)$ est libre.

Or pour tout $k in [|r + 1, p|]$,
$
phi_k in "Vect" (phi_1, dots, phi_r) \
"Donc" space inter.big_(i = 1)^r ker phi_i subset.eq ker phi_k \
"D'où" space inter.big_(k = 1)^p ker phi_k = inter.big_(k = 1)^r ker phi_k
$ 

Donc (cf. lemme sur la liberté d'une famille de formes linéaires)
$
  theta : func(E, KK^r, x, vec(phi_1 (x), dots.v, phi_r (x))) quad "surjective" \
  ker theta = inter.big_(k = 1)^r ker phi_k
$
Donc par le théorème du rang
$
  dim (inter.big_(k = 1)^p ker phi_k) = n - "rg" (phi_1, dots, phi_p)
$

#card("lemutihyp", "Liberté d'une famille de l'espace dual", ("Maths.Algèbre.Algèbre Linéaire",))

Démonstration d'une CNS pour la liberté d'une famille de $cal(L) (E, KK)$ où $E$ est un $KK$-ev.

#answer

Soient $phi_1, dots, phi_p in cal(L)(E, KK)$.

La famille $(phi_1, dots, phi_p)$ est libre ssi

$
  theta : func(E, KK^p, x, vec(phi_1 (x), dots.v, phi_p (x))) quad "surjective"
$

*Démonstration*

- Supposons $theta$ surjective, on considère $lambda_1, dots, lambda_p in KK$ tels que

  $
    sum_(k = 1)^p lambda_k phi_k = 0
  $

  Soit $i in [|1, p|]$, on dispose de $x in E$ tel que 

  $
  theta(x) = mat(augment: #1,,1;,dots.v;1,i;,dots.v;,p) = vec(phi_1 (x), dots.v, phi_i (x), dots.v, phi_p (x))
  $
  Ainsi
  $
    (sum_(k = 1)^(p) lambda_k phi_k) (x) = 0 = lambda_i
  $
- Par contraposé supposons $theta$ non surjective : $"rg" theta <= p - 1$.

  On dispose de $H$ hyperplan tel que $im theta subset.eq H$. Donc on dispose de $(alpha_1, dots, alpha_p) in KK^p\\{0}$ tels que

  $
    H = {lr(vec(x_1, dots.v, x_p) in KK^p |) sum_(k = 1)^p alpha_k x_k = 0}
  $

  Donc pour tout $x in E$,

  $
    theta(x) = vec(phi_1 (x), dots.v, phi_p (x)) in im theta subset.eq H \
    sum_(k = 1)^p alpha_k phi_k (x) = 0
  $

  Donc $sum_(k = 1)^p alpha_k phi_k = 0$ et la famille est liée

#card("condindepfl", "Condition de liberté d'une forme linéaire à une famille", ("Maths.Algèbre.Algèbre Linéaire",))

Soit $phi_1, dots, phi_p, psi in cal(L)(E, KK)$.

Démonstration d'une CNS pour que $psi in "Vect"(phi_1, dots, phi_p)$.

#answer

Soit $phi_1, dots, phi_p, psi in cal(L)(E, KK)$.

Pour tout $psi in cal(L)(E, KK)$

$
  phi in "Vect"(phi_1, dots, phi_p) \ "ssi" space inter.big_(k=1)^p ker phi_k subset.eq ker psi
$

*Démonstration*

- Si $phi in "Vect"(phi_1, dots, phi_p)$, on dispose de $lambda_1, dots, lambda_p in KK$ tels que

  $
    psi = sum_(k = 1)^p lambda_k phi_k
  $

  D'où

  $
    psi(inter.big_(k = 1)^p ker psi_p) &= sum_(k = 1)^p lambda_k phi_k (inter.big_(i = 1)^p ker phi_p) \
    &= {0}
  $

  Et donc $inter.big_(k = 1)^p ker phi_p subset.eq ker psi$.

- Supposons $inter.big_(k = 1)^p ker phi_p subset.eq ker psi$.

  Quitte à extraire et renuméroter, $(phi_1, dots, phi_r)$ est libre.

  Or pour tout $k in [|r + 1, p|]$,
  $
  phi_k in "Vect" (phi_1, dots, phi_r) \
  "Donc" space inter.big_(i = 1)^r ker phi_i subset.eq ker phi_k \
  "D'où" space inter.big_(k = 1)^p ker phi_k = inter.big_(k = 1)^r ker phi_k
  $ 

  Donc
  $
    theta : func(E, KK^r, x, vec(phi_1 (x), dots.v, phi_r (x))) quad "surjective"
  $
  Posons alors
  $
    theta' : func(E, KK^(r+1),x, vec(phi_1 (x), dots.v, phi_r (x), psi(x)))
  $
  Or
  $
  inter.big_(k = 1)^r ker phi_k = inter.big_(k = 1)^p ker phi_k subset.eq ker psi \
  "Donc" space vec(0, dots.v, 0, 1) in.not im theta'
  $
  La famille $(phi_1, dots, phi_r, psi)$ est liée d'où $psi in "Vect"(phi_1, dots, phi_p)$.

#card("baseduale", "Base duale, antéduale", ("Maths.Algèbre.Algèbre Linéaire",))

Définitions, propriétés, démonstrations autours des bases duals.

#answer

*Base duale*

Soit $E$ un $KK$-ev de dimension finie, $e = (e_1, dots, e_n)$ une base de $e$.

Il existe une unique famille $(phi_1, dots, phi_n) in cal(L)(E, KK)^n$ tel que

$
  forall i, j in [|1,n|], space phi_i (e_j) = delta_(i j)
$

Cette famille est appelée base duale de $e$ et est une base de $cal(L)(E, KK)$.

Dans ce cas
$
  forall x in E, space x = sum_(k = 1)^n phi_k (x) e_k \
  forall psi in cal(L)(E, KK), space psi = sum_(k = 1)^n psi(e_k) phi_k
$

*Base antéduale*

Pour toute base $(phi_1, dots, phi_n)$ de $cal(L)(E, KK)$, il existe une unique base $(e_1, dots, e_n)$ de $E$ tel que $(phi_1, dots, phi_n)$ en est la base duale.

*Démonstration*

- Existence / Unicité : car les formes linéaire sont uniquement déterminés par leurs image d'une base.

- Génératrice : Soit $psi in cal(L)(E, KK)$

  pour tout $i in [|1, n|]$

  $
    (sum_(k = 1)^n psi(e_k) phi_k) (e_i) &= sum_(k = 1)^n psi(e_k) phi_k (e_i) \
    &= psi(e_k) \
  $
  $
    "Donc" space psi = sum_(k = 1)^n psi(e_k) phi_k
  $

  Donc $(phi_1, dots, phi_n)$ est une base.

- Soit $x = sum_(k = 1)^n x_k e_k in E, i in [|1, n|]$

  $
    phi_i (x) &= phi_i (sum_(k = 1)^n x_k e_k) \
    &= sum_(k = 1)^n x_k delta_(i k) = x_i
  $

- Soit $(phi_1, dots, phi_n)$ base de $cal(L)(E, KK)$

  $
  theta : func(E, KK^n, x, vec(phi_1 (x), dots.v, phi_n (x))) quad "surjective"
  $

  Par liberté de la famille, donc bijective par argument dimensionnel.

  Notons $(b_1, dots, b_n)$ la base cannonique de $KK^n$.

  La famille $(e_k = theta^(-1) (b_k))_(k in [|1, n|])$ est l'unique base de $E$ tel que

  $
    forall i, j in [|1,n|], space phi_i (e_j) = delta_(i j)
  $
// TODO: point de vue matricielle

#card("lemfacalgl", "Lemme de factorisation", ("Maths.Algèbre.Algèbre Linéaire",))

Énoncé et démonstration du lemme de factorisation en algèbre linéaire.

#answer
Soient $E, F, G$ trois $KK$-ev

+ Soient $u in cal(L)(E, F), v in cal(L)(E, G)$, dans ce cas

  $
    ker u subset.eq ker v \
    <=> exists w in cal(L)(F, G), space v = w compose u
  $
  (Si $u$ est inversible $w = v compose u^(-1)$).

+ Soient $u in cal(L)(E, F), v in cal(L)(G, F)$, dans ce cas

  $
    im v subset.eq im u \
    <=> exists w in cal(L)(G, E), v = space u compose w
  $

*Démonstration*

+
  - Supposons qu'il existe $w in cal(L)(F, G)$ tel que $v = w compose u$. #h(1fr)

    $
    v(ker u) &= w(u(ker u)) \
    &= w({0}) = 0
    $

    D'où $ker u subset.eq ker v$.

  - Supposons que $ker u subset.eq ker v$.

    Soient $H, K$ tels que 
    $
      ker u plus.o H &= E \
      im u plus.o K &= F \
    $
    Posons
    $
      accent(u,~) : func(H, im u, x, u(x)) \
      ker accent(u,~) = ker u inter H = {0} \
      space dim H = "rg" u \
    $
    Donc $accent(u, ~)$ inversible.

    On peut donc écrire
    $
      w : func(F &= im u &plus.o& K, G, x &= y &+& z, v compose accent(u, ~)^(-1) (y))
    $

    Soit $x = y + z in E = ker u plus.o H$.

    $
     w compose u (x) &= v(accent(u, ~)^(-1) (u(z))) \
     &= v(z) \
     v(x) &= underbrace(v(y), 0) + v(z)
    $

+ 
  - Supposons qu'il existe $w in cal(L)(G, E)$ tel que $v = u compose w$
    $
      v(E) = u compose w (E) subset.eq u (E)
    $
    D'où $im v subset.eq im u$.

  - Supposons que $im v subset.eq im u$.

    Soit $H$ tel que $ker u plus.o H = E$.
    $
      accent(u,~) : func(H, im u, x, u(x)) \
      w : func(G, E, x, accent(u,~)^(-1) compose v (x))
    $
    On a bien pour $x in E$
    $
      u compose w(x) = accent(u,~)(accent(u,~)^(-1)(v(x))) = v(x)
    $

// TODO: VI.2) Liberté des familles de F(X, K) (flm la vrm)

#card("vanlag", "Vandermonde, interpolation de Lagrange", ("Maths.Algèbre.Algèbre Linéaire",))

Définitions, propriétés et démonstrations de l'interpolation de Lagrange et des matrices des Vandermonde.

#answer

Soit $KK$ un corps, $n in NN$, $a_0, dots, a_n in KK$ deux à deux distincts.

$
  theta : func(KK_n [X], KK^(n+1), P, vec(P(a_0), dots.v, P(a_n))) in cal(L)(KK_n [X], KK^(n+1))
$

Pour tout $P in ker theta$, 
$
P(a_0) = P(a_1) = dots.c = P(a_n) = 0
$ 
Donc $P$ est de degré $n$ avec $n+1$ racines distinctes, d'où $P = 0$.

Donc $theta$ est un isomorphisme.

Notons 
$
e &= (e_0, dots, e_n) \ c &= (1, X, dots, X^n)
$ 
Les bases cannoniques de $KK^(n+1)$ et $KK_n [X]$.
$
  forall k in [|0, n|], space theta^(-1)(e_k) = product_(i = 0 \ i != k)^n (X - a_i) / (a_k - a_i) = L_k (X)
$
La matrice de $theta$ dans les bases cannoniques est appelée matrice de Vandermonde de $a_0, dots, a_n$.
$
  cal(M)_(e <- c)(theta) = mat(1, a_0, a_0^2, dots.c, a_0^n; dots.v, dots.v, dots.v, dots.down, dots.v; 1, a_n, a_n^2, dots.c, a_n^n)
$

Sont déterminant vaut

$
  V(a_0, dots, a_n) &= det(cal(M)_(e <- c) (theta)) \ &= product_(0 <= i < j <= n) (a_j - a_i)
$

*Démonstration*

Par récurrence sur $n$, initialisée aisément pour $n = 1$.

On suppose la formule pour un $n in NN$.

$
  P(X) &= V(a_0, dots, a_n, X) \
  &= mat(delim: "|", 1, a_0, a_0^2, dots.c, a_0^(n+1); dots.v, dots.v, dots.v, dots.down, dots.v; 1, a_n, a_n^2, dots.c, a_n^(n+1); 1, X, X^2, dots.c, X^(n+1)) \
  &= sum_(j = 0)^(n+1) (-1)^(n + j) X^j V_(j)
$
Où $V_j$ est le déterminant mineur en $(n+2,j+1)$. De plus
$
  deg P <= n+1 \
  "cd" P = V(a_0, dots, a_n) != 0
$
De plus pour tout $k in [|0,n|]$, $P(a_k) = 0$ donc
$
  P &= V(a_0, dots, a_n) product_(k = 0)^n (X - a_k) \
  &= product_(0 <= i < j <= n) (a_j - a_i) product_(k = 0)^n (X - a_k) \
$
Ainsi on peut calculer
$
  P(a_(n+1)) &= V(a_0, dots, a_(n+1)) \
  &= product_(0 <= i < j <= n) (a_j - a_i) product_(k = 0)^n (a_(n+1) - a_k) \
  &= product_(0 <= i < j <= n + 1) (a_j - a_i)
$

// TODO: Pas sur de les mettres, sous espaces stables, droite stables, definition de vecteur et valeurs propres.

#card("extvp", "Exercice : endomorphisme qui stabilise toutes les droites", ("Maths.Exercice.Algèbre Linéaire",))

Soit $u in cal(L)(E)$ qui stabilise toute les droites, qui dire de $u$ ?

#answer

Par définition pour tout $x in E, space u(x) = lambda_x x$ avec $lambda_x in KK$.

Soit $x, y in E\\{0}$.

- Si $(x, y)$ est liée, $y = alpha x$ #h(1fr)

  $
    lambda_y alpha x = u(y) = alpha u(x) = lambda_x alpha x \
    lambda_y = lambda_x
  $

- Sinon $(x, y)$ est libre

  $
    lambda_(x + y) (x + y) = u(x + y) = u(x) + u(y) \
    lambda_(x + y) x + lambda_(x + y) y = lambda_x x + lambda_y y \
    lambda_x = lambda_(x + y) = lambda_y
  $

Donc pour tout $x in E, lambda_x = lambda$ et $u = lambda id$.

#card("nilp", "Endomorphismes nilpotents", ("Maths.Algèbre.Algèbre Linéaire",))

Définition d'un endomorphisme nilpotent et inégalité sur son indice.

#answer

Soit $u in cal(L)(E)$, $u$ est dit nilpotent s'il existe $q in NN^*$ tel que $u^q = 0$.

On appelle indice de nilpotence la valeur
$
  d = min Set(q in NN^*, u^q = 0)
$
On a toujours $d <= dim E$.

*Démonstration*

Comme $u^(d-1) != 0$ on dispose de $x in E$ tel que $u^(d-1) != 0$.

Considèrons la famille $(x, u(x), dots, u^(d-1) (x))$, soient $lambda_0, dots, lambda_(d - 1)$ tels que
$
  sum_(k = 0)^(d-1) lambda_k u^k (x) = 0 \
$
$
  u^(d - 1) (sum_(k = 0)^(d - 1) lambda_k u^k (x)) &= lambda_0 u^(d-1) (x) = 0 \
  & => lambda_0 = 0 \
  u^(d - 2) (sum_(k = 1)^(d - 1) lambda_k u^k (x)) &= lambda_1 u^(d-1) (x) = 0 \
  & => lambda_1 = 0 \
  dots.v
$
$
  lambda_0 = lambda_1 = dots.c = lambda_(d-1) = 0
$
D'où $d <= n$.

]
