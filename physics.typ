#import "cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#import "utils.typ": *
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
