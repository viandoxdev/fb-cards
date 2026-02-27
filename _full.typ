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

#card("formondeav", "Formules d'analyse vectoriel pour les ondes", ("Physique.Analyse Vectorielle",))

Formules d'analyse vectoriel pour les ondes.

#answer

Pour
$
  f(va(r), t) = f_0 e^(plus.minus i (omega t - va(k) dot va(r))) \
  va(F)(va(r), t) = va(F_0) e^(plus.minus i (omega t - va(k) dot va(r))) \
$
On a
$
  grad f &= minus.plus i va(k) f(va(r), t) \
  curl va(F) &= minus.plus i va(k) curl va(F)(va(r), t) \
  div va(F) &= minus.plus i va(k) dot va(F)(va(r), t) \
  laplace f &= -omega^2 f \
  laplace va(F) &= -k^2 va(F)
$

#card("cstesphys", "Constantes physiques", ("Physique",))

Valeurs numériques et unités de

#answer

$
  h &= 6.63 dot 10^(-34) J dot s \ e &= 1.6 dot 10^(-19) C \
  k_B &= 1.38 dot 10^(-23) J dot K^(-1) \ cal(N)_A &= 6.02 dot 10^(23) "mol"^(-1) \
  mu_0 &= 4pi dot 10^(-7) H dot m^(-1) \ epsilon_0 &= 8.9 dot 10^(35) F dot m^(-1) \
  m_e &= 9.1 dot 10^(-31) "kg" \ m_p &= 1.7 dot 10^(-27) \
$

// TODO: finir ça 
]
#[

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

#card("ptribu", "Tribu", ("Maths.Probabilités",))

Définition et propriétés de tribu.

#answer

Soit $Omega$ un ensemble non vide. Une tribu sur $Omega$ est un $cal(T) subset.eq cal(P)(Omega)$ tel que

- $emptyset in cal(T)$.

- $cal(T)$ est stable par passage au complémentaire.

- $cal(T)$ est stable par union dénombrable.

$(Omega, cal(T))$ est appelé espace probabilisable.

On a alors

- $Omega in cal(T)$.
- $cal(T)$ est stable par union finie.
- $cal(T)$ est stable par intersection dénombrable.
- Pour tout $A, B in cal(T)$, $A \\ B in cal(T)$.

*Démonstration*

- $Omega = overline(emptyset)$
- Pour $(A_i)_i in cal(T)^I$, #h(1fr)
  $
    inter.big_(i in I) A_i = overline(union.big_(i in I) overline(A_i)) in cal(T)
  $
- Pour $A, B in cal(T)$
  $
    A \\ B = A inter overline(B) in cal(T)
  $

#card("espprob", "Espace probabilisé", ("Maths.Probabilités",))

Définition et propriétés des espaces probabilisés.

#answer

Soit $(Omega, cal(T))$ un espace probabilisable. Une probabilité sur $(Omega, cal(T))$ est la donné d'un
$
  PP : cal(T) -> [0, 1]
$
Tel que

- $PP(Omega) = 1$.

- Pour tout $(A_n)_n in cal(T)^NN$ deux à deux disjoints
  $
    PP(union.plus.big_(n in NN) A_n) = sum_(n in NN) PP(A_n)
  $
  Avec convergence de la somme.

Dans ce cas

- $PP(emptyset) = 0$. #h(1fr)

- Pour tout $A subset.eq B in cal(T)$
  $
    PP(A) <= PP(B) \
    PP(B \\ A) = PP(B) - PP(A)
  $

- Pour tout $A in cal(T)$
  $
    PP(overline(A)) = 1 - PP(A)
  $

- Pour tout $(A_n)_n in cal(T)^NN$ une suite croissante d'évenements
  $
    PP(union.big_(n in NN) A_n) = lim_(n -> oo) PP(A_n)
  $

- Pour tout $(A_n)_n in cal(T)^NN$ une suite décroissante d'évenements
  $
    PP(inter.big_(n in NN) A_n) = lim_(n -> oo) PP(A_n)
  $

*Démonstration*

- On pose $(A_n)_n = (emptyset)_n$ deux à deux disjoints #h(1fr)
  $
    PP(emptyset) = PP(union.plus.big_(n in NN) A_n) = sum_(n in NN) PP(emptyset)
  $
  Qui converge d'où $PP(emptyset) = 0$.

- Soit $A subset.eq B in cal(T)$, on a
  $
    B = A union.plus (B \\ A) \
    PP(B) = PP(A) + PP(B \\ A)
  $

- Cas croissant :
  $
  B_0 = A_0 \
  B_(n + 1) = A_(n + 1) \\ A_n
  $
  Ainsi
  $
    A_n &= union.plus.big_(k = 0)^n B_k \
    &= union.big_(k = 0)^n A_n
  $
  De même
  $
    union.big_(n in NN) A_n &= union.plus.big_(n in NN) B_n \
    PP (union.big_(n in NN) A_n) &= sum_(n in NN) PP(B_n) \
    &= lim_(n -> oo) sum_(k = 0)^n PP(B_k) \
    &= lim_(n -> oo) PP(A_n)
  $

- Cas décroissant : On pose $B_n = overline(A_n)$, suite croissante.

#card("borcant", "Lemme de Borel-Cantelli", ("Maths.Probabilités",))

Énoncé et démonstration du lemme de Borel-Cantelli, version faible et version forte.

#answer

*Borel-Cantelli faible*

Pour $(A_n)_in in cal(T)^NN$ où $(Omega, cal(T), PP)$ est un ep, on pose
$
  S &= inter.big_(N in NN) union.big_(n >= N) A_n \
  &= lim sup A_n
$
Si $sum PP(A_n)$ converge, alors $PP(S) = 0$.

*Démonstration*

On pose $B_N = union.big_(n >= N) A_n$, une suite décroissante d'évenements, d'où
$
  PP(S) &= PP(inter.big_(N in NN) B_N) \ 
  &= lim_(N -> oo) PP(B_N) \
  &<= lim_(N -> oo) sum_(n = N)^(+oo) PP(A_n) = 0
$

*Borel-Cantelli fort*

Avec les même notations, si $sum PP(a_n)$ diverge et $(A_n)_n$ mutuellement indépendants, alors $PP(S) = 1$.

*Démonstration*

On a
$
  overline(S) = union.big_(N in NN) inter.big_(n >= N) overline(A_n)
$
Ainsi
$
  PP(S) &= 1 - PP(overline(S)) \
  &>= 1 - sum_(N in NN) PP(inter.big_(n >= N) overline(A_n))
$
Or
$
  PP(inter.big_(n >= N) overline(A_n)) &= lim_(n -> oo) PP(inter.big_(k = N)^(n) overline(A_k)) \
  &= lim_(n -> oo) product_(k = N)^(n) (1 - PP(A_n))
$
Et
$
  product_(k = N)^(n) (1 - PP(A_n)) &<= product_(k = N)^n e^(-PP(A_k)) \
  &= exp(-sum_(k = N)^n PP(A_k)) \
  &tends(n -> oo) 0
$

#card("vadp", "Variables aléatoires discrètes", ("Maths.Probabilités",))

Définition de variable aléatoire discrète.

#answer

Soit $(Omega, cal(T), PP)$ un ep, $E != emptyset$ un ensemble. Une variable aléatoire discrète sur $Omega$ à valeur dans $E$ est une application $X : Omega -> E$ tel que
- $X(Omega)$ est fini ou dénombrable.

- $forall x in X(Omega), X^(-1){x} in cal(T)$

Qui détermine une distribution de probabilité discrète sur $E$ ou $X(Omega)$.

// NOTE: Indépendance d'évenements, formules de probabilité totales, de Bayes, conditionelles...

#card("loibas", "Lois classique de probabilité", ("Maths.Probabilités",))

Lois classique de probabilité, définition, espérance, variance et série génératrice.

#answer

#align(center, table(
  stroke: none,
  columns: 1,
  table.hline(),
  [*Bernoulli* ($p in [0, 1]$)],
  table.hline(),
  $
    X(Omega) &= {0, 1} quad quad& PP(X = 1) &= p\ 
    EE(X) &= p quad quad& VV(X) &= p q \
  $,
  $
    G_X (t) = p t + q \
    X ~ cal(B)(p)
  $,
  table.hline(),
  [*Binomiale* ($n in NN, p in [0, 1]$)],
  table.hline(),
  $
    X(Omega) &= [|0, n|] quad& PP(X = k) &= vec(n, k) p^k q^(n - k) \
    EE(X) &= n p quad quad& VV(X) &= n p quad \
  $,
  $
    G_X (t) &= (p t + q)^n \
    X &~ cal(B)(n, p)
  $,
  table.hline(),
  [*Géométrique* ($p in Ioc(0, 1)$)],
  table.hline(),
  $
    X(Omega) &= NN^* quad& PP(X = k) &= q^(n - 1) p \
    EE(X) &= 1 / p quad quad& VV(X) &= q / p^2 quad \
  $,
  $
    G_X (t) = (p t) / (1 - q t) \
    X ~ cal(G)(p)
  $,
  table.hline(),
  [*Poisson* ($lambda > 0$)],
  table.hline(),
  $
    X(Omega) &= NN quad& PP(X = k) &= e^(-lambda) lambda^k / (k!) \
    EE(X) &= lambda quad quad& VV(X) &= lambda quad \
  $,
  $
    G_X (t) = e^(lambda (t - 1)) \
    X ~ cal(P) (lambda)
  $,
))

// NOTE: lois usuels - M287, résultats connus qui existent
// - indépendance de variable à faire ?

#card("lemdescoal", "Lemme des coalitions", ("Maths.Probabilités",))

Lemme des coalitions.

#answer

Soit $(X_1, dots, X_(n + m))$ une famille de variables aléatoires discrètes indépendantes sur $(Omega, cal(T), PP)$.
$
  f : product_(i = 1)^n X_i (Omega) -> E \
  g : product_(j = n+1)^(n + m) X_j (Omega) -> F \
$
Alors $f(X_1, dots, X_n)$ et $g(X_(n+1), dots, X_(n+m))$ sont des variables aléatoires discrètes indépendantes.

*Démonstration*

Calculs pas très beau, fubini.

// NOTE: Interpretation des lois usuels M289

#card("esppb", "Espérance d'une variable aléatoire", ("Maths.Probabilités",))

Définition et propriétés élémentaires de l'ésperance d'une variable aléatoire.

#answer

- Pour $X$ une variable aléatoire sur $(Omega, cal(T), PP)$ complexe, on dit que $X$ est d'ésperance finie si $(x P(X = x))_(x in X^(-1) (Omega))$ est sommable, on note $X in LL^1$ et on pose
  $
    EE(X) = sum_(x in X^(-1) (Omega)) x PP(X = x)
  $

- Pour $X$ à valeur dans $RR_+$ on définit l'ésperance dans $RR_+ union {+oo}$, avec $EE(X) = +oo$ si la somme diverge.

- Pour $X$ à valeur dans $NN$ on a
  $
    EE(X) = sum_(n = 0)^(+oo) PP(X >= n)
  $

- Si $X$ est à valeur dans $NN$ et $EE(X) < +oo$, alors
  $
    PP(X >= n) tends(n -> oo) 0 \
    PP(X >= n) = o_(n -> oo) (1/n)
  $

*Démonstration*

- $X$ à valeur dans $NN$ #h(1fr)
  $
    sum_(n = 0)^(+oo) PP(X >= n) &= sum_(n = 0)^(+oo) sum_(k = n)^(+oo) PP(X = k) \
    &= sum_(k = 0)^(+oo) sum_(n = 0)^(k) PP(X = k) \
    &= sum_(k = 0)^(+oo) k PP(X = k) \
    &= EE(X)
  $

- La première ligne est toujours vraie car 
  $
    sum_(n = 0)^(+oo) PP(X >= n) = EE(X) < +oo
  $
  Pour la deuxième
  $
    n PP(X >= n) &= n sum_(k = n)^(+oo) PP(X = k) \
    &<= sum_(k = n)^(+oo) k PP(X = k) tends(n -> oo) 0
  $
  Car série reste d'une série convergente.

#card("ldtpb", "Lemme de tranfert", ("Maths.Probabilités",))

Énoncé et démonstration du lemme de transfert.

#answer

Soit $X$ variable aléatoire discrète à valeur dans $E$, et $f : E -> CC$.

Alors $f(X) in LL^1$ ssi $(f(x)P(X = x))_(x in X^(-1)(Omega))$ est sommable et 
$
  EE(f(X)) = sum_(x in X^(-1)(Omega)) f(x) PP(X = x)
$

On en déduit que $X in LL^1$ ssi $EE(abs(X)) < +oo$.

*Démonstration*

Sommation par paquets.

#card("propesppb", "Propriétés de l'ésperance", ("Maths.Probabilités",))

Propriétés de l'ésperance.

#answer

On a les propriétés suivantes

- Toute variable aléatoire bornée est d'ésperance finie.
- $EE$ est linéaire : #h(1fr)
  $
  EE(alpha A + beta B) = alpha EE(A) + beta EE(B)
  $
- $EE$ est croissante :
  $
    X <= Y => EE(X) <= EE(Y)
  $
- On à l'inégalité triangulaire
  $
    abs(EE(X)) <= EE(abs(X))
  $
- Pour $X tack.t.double Y$
  $
    EE(X Y) = EE(X) EE(Y)
  $
- Pour $A in cal(T)$
  $
    EE(bb(1)_A) = PP(A)
  $
- Pour $X, Y in LL^2$
  $
    EE(X Y)^2 <= EE(X^2) EE(Y^2)
  $
  avec égalité ssi $X = alpha Y$ ps.

// NOTE: Démonstrations M294 et avant

#card("varvapb", "Variance d'une variable aléatoire", ("Maths.Probabilités",))

Définition et propriétés élémentaires de la variance d'une variable aléatoire.

#answer

*Variance*

Pour $X$ une variable aléatoire discrète réelle, on note $X in LL^2$ si $X^2 in LL^1$.

Dans ce cas $X in LL^1$, et on définie
$
  VV(X) &= EE((X - EE(X))^2) \
  &= underbrace(EE(X^2) - EE(X)^2, "Koenig-Huygens")
$

On a alors

- Si $Y = a X + b$ #h(1fr)
  $
    VV(Y) = a^2 VV(X)
  $

- $VV(X) = 0$ ssi $X$ ps constante.

*Covariance*

On définit de plus la covariance de $X, Y in LL^2$
$
"Cov" (X, Y) \ = EE((X - EE(X))(Y - EE(Y))) \
= EE(X Y) - EE(X) EE(Y)
$
Qui est une forme bilinéaire, symétrique, positive.

Si $"Cov"(X, Y) = 0$ on dit que $X$ et $Y$ sont décorélées, et dans ce cas
$
  VV(X + Y) = VV(X) + VV(Y)
$

- Deux variables indépendantes sont décorélées.

- Pour $X, Y in LL^2$
  $
    "Cov"(X, Y)^2 <= VV(X) VV(Y)
  $

*Démonstration*

- Pour $X in LL^2$ #h(1fr)
  $
    EE((X - EE(X))^2) \ = EE(X^2 - 2X EE(X) + EE(X)^2) \
   = EE(X^2) - 2 EE(X) EE(X) + EE(X^2) \
   = EE(X^2) - EE(X)^2
  $

- Pour $Y = a X + b$ \
  $
    VV(Y) &= EE((a X + b - EE(a X + b))^2) \ 
    &= EE((a X - a EE(X))^2) \
    &= a^2 EE((X - EE(x))^2) \
    &= a^2 VV(X)
  $

#card("inegprob", "Premières inégalités de probabilités", ("Maths.Probabilités",))

Premières inégalités de probabilités.

#answer

*Markov*

Pour $X in LL^1$ reélle, et pour tout $delta > 0$
$
  EE(abs(X) >= delta) <= EE(|X|) / delta
$
Et de plus pour $f : RR_+ -> RR_+$ strictement croissante et $X >= 0$
$
  PP(X >= delta) <= EE(f(X)) / f(delta)
$

*Bienaymé-Tchebychev*

Soit $X in LL^2$, $m = EE(X)$ et $delta > 0$
$
  PP(abs(X - m) >= delta) <= VV(X) / delta^2
$

*Démonstration*

Pour $X >= 0$
$
  X = X bb(1)_(X < delta) + X bb(1)_(X >= delta)
$
$
  EE(X) &= underbrace(EE(X bb(1)_(X < delta)), >= 0) + EE(X bb(1)_(X >= delta)) \ 
  &>= EE(delta bb(1)_(X >= delta)) = delta PP(X >= delta)
$

Et ainsi pour $X in LL^2$
$
  PP(abs(X - m) >= delta) &= PP((X - m)^2 >= delta^2) \
  &<= EE((X - m)^2) / delta^2 \
  &= VV(X) / delta^2
$

#card("loigrandnmbr", "Loi des grands nombres", ("Maths.Probabilités",))

Loi faible et loi forte des grands nombres.

#answer

Soit $(X_n)_(n in NN^*)$ vaiid de $LL^2$. On note $m = EE(X_1)$ et $sigma = sigma(X_1)$, pour $n in NN, S_n = sum_(k = 1)^n X_k$.

*Faible*

Pour tout $delta > 0$
$
  PP(abs(S_n / n - m) >= delta) tends(n -> oo) 0
$
$(S_n / n)_n$ converge en probabilité vers $m$.

*Forte*

$(S_n / n)_n$ converge presque surement vers $m$.

*Démonstration : faible*

$
  PP(abs(S_n / n - m) >= delta) \ <= VV(S_n / n) / delta^2 = VV(sum_(k = 1)^n X_k) / (n^2 delta^2) = sigma^2 / (n delta^2) \
  tends(n -> oo) 0
$

*Démonstration : forte*

Si $VV(X) = 0$, $X = m$ presque surement et le résultat est évident.

On peut alors centrer et réduire $X_n$ afin de se ramener à $m = 0$ et $sigma = 1$.

Par la version faible
$
  PP(abs(S_(n^2) / n^2) >= delta) <= 1 / (n^2 delta^2)
$
Qui est le terme général d'une série convergente. Donc par le lemme de Borel-Cantelli faible, on montre que $abs(S_(n^2) / n^2)$ converge presque surement vers $0$.

Soit $m in [|n_m^2, (n_m + 1)^2 - 1|]$
$
  abs(S_m / m) <= underbrace(abs(S_(n_m^2) / m), <= abs(S_(n^2_m)) / n^2_m) + 1/m abs(sum_(j = n_m^2 +1)^m X_j)
$
Or
$
  &PP(abs(1/m sum_(j = n_m^2+1)^m X_j) >= delta) \
  =& PP((sum_(j = n_m^2+1)^m X_j)^2 >= m^2 delta^2) \
  <=& EE((sum_(j = n^2_m + 1)^m X_j)^2) / (m^2 delta^2) \
  =& (m - n^2_m) / (m^2 delta^2) = (sqrt(m)^2 - floor(sqrt(m))^2) / (m^2 delta^2) \
  <=& (2sqrt(m) - 1) / (m^2 delta^2) = O(1/m^(3/2))
$
Qui est le terme général d'une série convergente
$
  PP(abs(1/m sum_(j = n_m^2+1)^m X_j) tends(m -> oo) 0) = 1
$
Et en sommant on a le résultat demandé.

#card("exweieprob", "Exercice : Démonstration probabiliste du théorème de Weierstrass", ("Maths.Exercices.Probabilités",))

Démonstration probabiliste du théorème de Weierstrass.

#answer

Soit $f in C^0 ([0, 1], RR)$, pour $n in NN$
$
  B_n = sum_(k = 0)^n vec(n, k) f(k / n) X^k (1 - X)^(n - k)
$
Montrons que $(B_n)_n$ CVU vers $f$ sur $[0, 1]$.

Soit $x in [0, 1]$, $(X_n)_(n in NN^*)$ vaiid tel que $X_k ~ cal(B)(x)$. Et $S_n = sum_(k = 1)^n X_k ~ cal(B)(n, x)$. On remarque que
$
  B_n (x) &= sum_(k = 0)^n f(k / n) PP(S_n = k) \ &= EE(f(S_n / n))
$

Soit $epsilon > 0$, par uniforme continuité de $f$ sur $[0,1]$, on dispose de $delta > 0$ associé.

$
  abs(B_n (x) - f(x)) = abs(EE(f(S_n / n) - f(x))) \
$
$
  = abs(EE[ &underbrace((f(S_n / n) - f(x)), <= 2 norm(f)_oo) bb(1)_(abs(S_n / n - x) >= delta) \
  + &underbrace((f(S_n / n) - f(x)), < epsilon) bb(1)_(abs(S_n / n - x) < delta) ]) \
  <= & 2norm(f)_oo PP(abs(S_n / n - x) >= delta) + epsilon \
  <= & 2norm(f)_oo (x(1 - x)) / (n delta^2) + epsilon
$

#card("exinegconc1", "Exercice : première inégalité de concentration", ("Maths.Exercice.Probabilités",))

Première inégalité de concentration (Exercice 57) :

Soit $(X_k)_(1 <= k <= n)$ vad réelles centrées indépendantes tel que pour tout $k in [|1, n|]$, $abs(X_k) < 1$.

On pose $S_n = sum_(k = 1)^n X_k$, montrer que
$
  PP(S_n / n >= epsilon) <= e^(-(epsilon^2 n) / 2) \
  "puis" \
  PP(abs(S_n / n) >= epsilon) <= 2 e^(-(epsilon^2 n) / 2)
$

#answer

+ Pour tout $x in [-1, 1]$, $t in RR$, #h(1fr)
  $
    s = (1 - x) / 2 in [0, 1] \
    t x = s (-t) + (1 - s) t 
  $
  D'où
  $
    e^(t x) &= e^(s (-t) + (1 - s) t) \
    &<= s e^(-t) + (1 - s) e^t \
    &= (1 - x) / 2 e^(-t) + (1 + x) / 2 e^t
  $

+ Soit $t in RR^+$, $X$ vad réelle centrée à valeur dans $[-1, 1]$
  $
    EE(e^(t X)) &<= EE((1 - X) / 2 e^(-t) + (1 + X) / 2 e^t) \
    &= (1 - EE(X)) / 2 e^(-t) + (1 + EE(X)) / 2 e^t \
    &= ch(t)
  $
  Donc
  $
    EE(e^(t S_n)) &= EE(product_(k = 1)^n e^(t X_k)) \
    (tack.t.double) quad &= product_(k = 1) EE(e^(t X_k)) \
    &<= ch(t)^n
  $

  Or pour tout $t in RR^+$
  $
    ch(t) = sum_(n = 0)^(+oo) t^(2 n) / (2 n)! quad e^(t^2 / 2) = sum_(n = 0)^(+oo) t^(2 n) / (2^n n!) \
    (2 n)! / (2^n n!) = product_(k = 0)^(n - 1) (2 k + 1) >= 1 \
  $
  Donc $ch(t) <= e^(t^2 / 2)$

  Et ainsi
  $
    EE(e^(t S_n)) <= e^((t^2 n) / 2)
  $

+ Soit $a > 0$
  $
    PP(abs(S_n) >= a) = PP(S_n >= a) + PP(-S_n >= a)
  $
  Soit $t in RR^+$
  $
    PP(S_n >= a) &= PP(e^(t S_n) >= e^(t a)) \
    ("Markov") space &<= EE(e^(t S_n)) / e^(t a) \
    &<= e^((t^2 n) / 2 - t a)
  $
  Pour $t = a / n$
  $
    PP(S_n >= a) <= e^(- a^2 /( 2 n))
  $
  Et comme les $(-X_k)_k$ verifient les mêmes hypothèses
  $ 
    PP(-S_n >= a) <= e^(- a^2 / (2 n)) 
  $
  Ainsi
  $
    PP(abs(S_n) >= a) <= 2 e^(- a^2 / (2 n)) 
  $

+ Avec $a = n epsilon$
  $
    PP(abs(S_n / n) >= epsilon) &= PP(abs(S_n) >= n epsilon) \
    &<= 2 e^(- (n  epsilon^2) / 2)
  $

*Remarque*

$
  PP(abs(S_n / n - 0) >= epsilon ) &= PP(abs(S_n - EE(S_n)) >= n epsilon) \
  &<= (sum_(k = 1)^n VV(X_k)) / (n^2 epsilon^2) <= 1 / (n epsilon^2)
$

#card("exinegconc2", "Exercice : quelques inégalités", ("Maths.Exercice.Probabilités",))

+ Exercice 62.1 : #h(1fr)

  Soit $X$ une vad réelle positive de $LL^2$ tel que $EE(X^2) > 0$, montrer que
  $
    PP(X > 0) >= EE(X)^2 / EE(X^2)
  $

+ Exercice 56 :

  Soit $X$ une vad réelle positive de $LL^2$ tel que $PP(X > 0) > 0$, et $theta in Ioo(0, 1)$, montrer que
  $
    PP(X >= theta EE(X)) >= ((1 - theta)^2 EE(X)^2) / (EE(X^2))
  $

#answer

+ Par Cauchy-Schwartz #h(1fr)
  $
    EE(X)^2 &= EE(X bb(1)_(X > 0))^2 \
    &<= EE(X^2) EE(bb(1)_(X > 0)) \
    &= EE(X^2) PP(X > 0)
  $

+ Similairement
  $
    EE(X bb(1)_(X >= theta EE(X)))^2 <= EE(X^2) PP(X >= theta EE(X))
  $
  Et
  $
    X bb(1)_(X >= theta EE(X)) = X - underbrace(X bb(1)_(X < theta EE(X)), <= theta EE(X)) \
    EE(X bb(1)_(X >= theta EE(X))) >= (1 - theta) EE(X)
  $
  Ainsi
  $
  (1 - theta)^2 EE(X)^2 <= EE(X^2) PP(X >= theta EE(X))
  $

#card("expilepile", "Exercice : probabilité de pile pile, calcul d'espérance par récurrence", ("Maths.Exercice.Probabilités",))

Exercice 14 :

Soit $(X_n)_(n in NN^*)$ vaiid tel que $X_k ~ cal(B)(1/2)$. On note
$
  T &= min Set(k >= 2, X_k = 1 "et" X_(k-1) = 1) \ &in NN union {+oo}
$

+ Montrer que $T$ est une vad.

+ Montrer que $T$ est ps fini.

+ Calculer $EE(T)$.

#answer

+ On sait que $T(Omega) subset.eq NN union {+oo}$ qui est fini ou dénombrable.

  Pour tout $n in NN$
  $
    (T > n) &= inter.big_(k = 2)^(n)  overline((X_k = X_(k - 1) = 1)) in cal(T) \

    (T = n) &= (T > n - 1) \\ (T > n) in cal(T) \ \
    
    (T = +oo) &= inter.big_(n = 1)^(+oo) (T > n) in cal(T)
  $

+ Calculons la loi de $T$ (on note $p_n = PP(T = n)$) :
  $
    p_1 = 0 quad quad p_2 = 1 /4
  $
  Soit $n >= 3$
  $
    p_n = &PP(T = n, X_1 = 1) \ +  &PP(T = n, X_1 = 0)
  $
  On pose $(tilde(X)_k)_(k >= 1) = (X_(k + 1))_k$ et $tilde(T)$ associé aux $(tilde(X)_k)_k$.

  Ainsi pour tout $m >= 2$ (Par le lemme des coalitions)
  $
    (tilde(T) = m) tack.t.double (X_1 = 0)
  $
  D'où
  $
   & PP(T = n, X_1 = 0) \ =& PP(tilde(T) = n - 1, X_1 = 0) \
   =& PP(tilde(T) = n - 1) PP(X_1 = 0)
  $
  Or $tilde(T) ~ T$, d'où
  $
    p_n = p_(n - 1) PP(X_1 = 0)
  $

  De même, on pose $(tilde(tilde(X))_k)_(k >= 1) = (X_(k + 2))_k$ et $tilde(tilde(T))$ associé.
  $
    & PP(T = n, X_1 = 1) \
    =& PP(T = n, X_1 = 1, X_2 = 0) \
    =& PP(tilde(tilde(T)) = n - 2) PP(X_1 = 1) PP(X_2 = 0) \
    =& p_(n - 2) PP(X_1 = 1) PP(X_2 = 0)
  $

  D'où pour $n >= 3$
  $
    p_n = 1/2 p_(n - 1) + 1/4 p_(n - 2) \
    2^n p_n = 2^(n - 1) p_(n - 1) + 2^(n - 2) p_(n - 2)
  $
  Et $(2^n) p_n$ suit la relation de récurrence de Fibonnaci.

  Posons maintenant
  $
    s &= sum_(n = 2)^(+oo) p_n = 1 - PP(T = +oo) \
    &= p_2 + sum_(n = 3)^(+oo) (1/2 p_(n - 1) + 1/4 p_(n - 2)) \
    &= 1/4 + 1/2 s + 1/4 s
  $
  D'où $1/4 s = 1/4$ et $s = 1$, $PP(T = +oo) = 0$.

+ De même
  $
    EE(T) &= sum_(n = 2)^(+oo) n p_n \
    &= 2 p_2 + sum_(n = 3)^(+oo) n(1/2 p_(n - 1) + 1/4 p_(n - 2)) \
    &= 1/2 + 1/2 sum_(n = 3)^(+oo) (n - 1) p_(n - 1) \
    &+ 1/2 sum_(n = 3)^(+oo) p_(n - 1) + 1/4 sum_(n = 3)^(+oo) (n - 2) p_(n - 2) \
    &+ 1/4 sum_(n = 3)^(+oo) 2 p_(n - 2) \
    &= 3/2 + 3/4 EE(T) \
    &= 6
  $

#card("foncgen", "Fonction génératrice d'une variable aléatoire entière naturelle", ("Maths.Probabilités",))

Fonction génératrice d'une variable aléatoire entière naturelle.

#answer

Si $X$ est une vad à valeur dans $NN$, alors $R_"cv" (sum PP(X=n) t^n) >= 1$ et la série entière converge normalement sur $overline(DD(0,1))$
$
  G_X : func([0,1], RR, t, sum_(n = 0)^(+oo) PP(X = n) t^n)
$
Est appelée fonction génératrice de $X$, et les valeurs de $G_X$ sur un $[0, delta]$ avec $delta > 0$ detérminent de manière unique la loi de $X$.

On a de plus

- $G_X (1) = 1$.

- $G_X$ est $C^oo$ sur $Ico(0,1)$ et pour tout $n in NN$
  $
    G_X^((n)) >= 0
  $

- $X$ est d'ésperance finie ssi $G_X$ est dérivable en $1$ et dans ce cas #h(1fr)
  $
    G'_X (1) = EE(X)
  $

- $X^2$ est d'ésperance finie ssi $G_X$ est dérivable deux fois en $1$ et dans ce cas
  $
    G''_X (1) &= EE(X(X-1)) = EE(X^2) - EE(X) \
    VV(X) &= G''_X (1) + G'_X (1) - G'_X (1)^2
  $

- Pour $X, Y$ vad entières naturelles indépendantes sur le même ep
  $
    G_(X+Y) = G_X G_Y
  $

*Démonstration*

Pour la pluspart : les écrires.

- On suppose que $EE(X) < +oo$ #h(1fr)

  On considère $G_X$ comme une série de fonctions, on montre que $sum f'_n$ CVN sur $[0, 1]$ et on applique le théorème de dérivation des séries de fonctions.

- On suppose que $EE(X) = +oo$ (contraposée)

  On exprime le taux d'accroissement en $1$, on le developpe et on montre qu'il diverge.

- Même shéma de preuve pour $X^2$.

- Par le lemme de transfer
  $
    G_X (t) = EE(t^X)
  $
  D'où
  $
    G_(X+Y) (t) &= EE(t^(X + Y)) = EE(t^X t^Y) \
    &= EE(t^X) EE(t^Y) = G_X (t) G_Y (t)
  $

#card("exnbcyclper", "Exercie : nombre de cycles d'une permutation aléatoire", ("Maths.Probabilités",))

Soit $sigma_n ~ cal(U) (frak(S)_n)$ et $X_n$ le nombre de cycle de $sigma_n$.

+ Calculer $G_X_n$.

+ En déduire $EE(X_n)$, $VV(X_n)$.

#answer

+ Soit $k in [|1, n|]$

  $
    X^(-1)_(n+1) {k} &= Set(sigma in frak(S)_n, cases(delim: #none, script(sigma(n+1) = n+1), script(sigma|_([|1,n|]) "a" k - 1 "cycles"))) \
    &union.plus union.plus.big_(l = 1)^n underbrace(Set(sigma in frak(S)_(n+1), cases(delim: #none, script(sigma^(-1)(n+1) = l), script(sigma "a" k "cycles"))), Gamma_l) \
  $
  Avec $Gamma_l tilde.eq X^(-1)_n {k}$ par la bijection
  $
    func(Gamma_l, X^(-1)_n {k}, sigma, func([|1,n |], [|1,n|], j != l, sigma(j), l, sigma(n+1)))
  $

  Ainsi
  $
    abs(X^(-1)_(n+1) {k}) = abs(X^(-1)_n {k - 1}) + n abs(X^(-1)_n {k}) \
  $
  $
    PP(X_(n+1) = k) &= 1/(n+1) PP(X_n = k - 1) \ &+ n / (n+1) PP(X_n = k)
  $
  Qui est aussi vrai pour $k = n+1$.

  Ainsi pour tout $t in [0, 1]$
  $
    G_X_(n+1) (t) &= sum_(n = 1)^(n+1) PP(X_(n+1) = k) t^k \
    &= 1/(n+1) (sum_(k = 1)^(n+1) PP(X_n = k - 1) t^k \ &+ n sum_(k = 1)^(n+1) PP(X_n = k) t^k) \
    &= 1/(n+1) (sum_(k = 1)^(n) PP(X_n = k) t^(k+1) \ &+ n sum_(k = 1)^(n+1) PP(X_n = k) t^k) \
    &= (t + n) / (n+1) G_X_n (t) \
    G_X_1 (t) &= t
  $

  D'où
  $
    G_X_n (t) = 1 / n! product_(k=0)^(n-1) (t + k)
  $

+ On calcul
  $
    G'_X (t) &= 1/n! sum_(j = 0)^(n - 1) (product_(k = 0)^(n-1) (t + k)) / (t + j) \
    G'_X (1) &= 1/n! sum_(j = 0)^(n - 1) n! / (1 + j) = H_n
    
  $
  D'où $EE(X_n) = H_n eqv(n -> oo) ln(n)$.

  Et
  $
    G''_n (t) &= 1/n! sum_(0 <= i, j <= n - 1 \ i != j) (product_(k = 0)^(n-1) (t + k)) / ((t+j)(t+i)) \
    G''_n (1) &= sum_(1 <= i, j <= n - 1 \ i != j) 1 / (i j) = H_n^2 - underbrace(sum_(k = 1)^n 1/k^2, K_n)
  $
  D'où $VV(X_n) = H_n - K_n eqv(n -> oo) ln(n)$.

// NOTE: Dés pipés M304 

#card("loisomvar", "Loi d'une somme de variables aléatoires paramétrée par une variable aléatoire", ("Maths.Probabilités",))

Loi d'une somme de variables aléatoires paramétrée par une variable aléatoire :
$
  sum_(k = 1)^T X_k
$
Avec $(X_k)_(k >= 1)$ et $T$ des variables aléatoires.

#answer

Soient $(X_k)_(k >= 1)$ vaiid à valeur dans $NN$ et $T$ une vad à valeur dans $NN$ indépendante des $X_k$. On pose
$
  S_T = sum_(k = 1)^T X_k quad quad S_n = sum_(k = 1)^n X_k
$

Alors

+ $S_T$ est une vad.

+ $G_S_T = G_T compose G_X_1$

*Démonstration*

+ $S_T (Omega) subset.eq NN$ qui est dénombrable, et pour tout $k in NN$
  $
    S^(-1)_T {k} &= union.plus.big_(j = 0)^(+oo) S^(-1)_T {k} inter (T = j) \
    &= union.plus.big_(j = 0)^(+oo) (S_j = k) inter (T = j) in cal(T) \
  $

+ Pour tout $t in [0,1]$

  $
    G_S_T (t) &= sum_(k = 0)^(+oo) PP(S_T = k) t^k \
    &= sum_(k = 0)^(+oo) (sum_(n = 0)^(+oo) PP(T = n, S_n = k))t^k \
    ("LdC") &= sum_(k = 0)^(+oo) sum_(n = 0)^(+oo) PP(T = n)PP(S_n = k) t^k \
    (>=0) &= sum_(n = 0)^(+oo) PP(T = n) sum_(k = 0)^(+oo) PP(S_n = k) t^k \
    &= sum_(n = 0)^(+oo) PP(T = n) G_S_n (t) \
    (tack.t.double) &= sum_(n = 0)^(+oo) PP(T = n) G_X_1 (t)^n \
    &= G_T (G_X_1 (t))
  $

// NOTE: Galton Watson M306

// TODO: Peut être découper ? Il y a beaucoup sur les marches aléatoires

#card("marchal", "Marches aléatoires sur les entiers relatifs", ("Maths.Probabilités",))

Marches aléatoires sur les entiers relatifs.

#answer

Soit $(X_k)_(k >= 1)$ vaiid et $S_n = sum_(k = 1)^n X_k$ tel que
$
  PP(X_k = 1) = PP(X_1 = 1) = p \
  PP(X_k = -1) = PP(X_1 = -1) = 1 - p \
$

+ On remarque tout d'abord #h(1fr)
  $
    Y_k = (X_k + 1) / 2 quad quad Y_k ~ cal(B)(p)
  $
  Et
  $
    X_k eq.triple 1 space [2] quad quad S_n eq.triple n space [2]
  $
  D'où
  $
    PP(S_(2 n) = 2k + 1) = 0 \
    PP(S_(2 n + 1) = 2k) = 0 \
  $

+ On peut calculer $PP(S_(2 n) = 0)$
  $
    S_(2 n) &= sum_(k = 1)^(2 n) X_k \
    &= 2 sum_(k = 1)^(2 n) Y_k - 2 n
  $
  D'où
  $
    PP(S_(2 n) = 0) &= PP(sum_(k = 1)^(2n) Y_k = n) \
    &= vec(2n, n) p^n (1 - p)^n
  $

+ Temps de retour en $0$ :

  On étudie
  $
    T_0 = min Set(n in NN^*, S_n (omega) = 0)
  $
  On note
  $
    S^((k))_n = sum_(i = k + 1)^(k + n) X_i ~ S_n \
    forall a <= b, n in NN, space ("LdC")\ 
    (T_0 = a) tack.t.double (S^((b))_n = 0)
  $

  Pour $n in NN^*$
  $
    &PP(S_(2 n) = 0)  \
    =& PP(S_(2 n) = 0, T_0 <= 2 n) \
    =& sum_(k = 1)^n  PP(S_(2n) = 0, T_0 = 2k) \
    =& sum_(k = 1)^n  PP(T_0 = 2k, S^((2k))_(2(n - k)) = 0) \
    =& sum_(k = 1)^n  PP(T_0 = 2k) PP(S^((2k))_(2(n - k)) = 0) \
    =& sum_(k = 1)^n  PP(T_0 = 2k) PP(S_(2(n - k)) = 0) \
  $
  On introduit
  $
    F : t |-> sum_(n = 0)^(+oo) PP(S_n = 0) t^n \
    tilde(F) : t |-> sum_(n = 0)^(+oo) PP(S_(2n) = 0) t^n \ 
    F(t) = tilde(F) (t^2) \
    G : t |-> sum_(n = 0)^(+oo) PP(T_0 = n) t^n \
    tilde(G) : t |-> sum_(n = 0)^(+oo) PP(T_0 = 2n) t^n \ 
    G(t) = tilde(G) (t^2)
  $
  Ainsi
  $
    tilde(F) (t) &= sum_(n = 0)^(+oo) vec(2n,n) p^n (underbrace(1 - p, q))^n t^n \
    &= sum_(n = 0)^(+oo) (2n)! / n!^2 (p q t)^n \
    &= sum_(n = 0)^(+oo) (2n)! / (2^n n!)^2 (4 p q t)^n \
    &= 1 / sqrt(1  - 4 p q t)
  $
  Avec $R_"cv" (tilde(F)) = 1 / (4 p q t)$ donc $1$ si $p = 1/2$ et $>1$ sinon.

  Or
  $
    0 <= PP(T_0 = 2 n) <= PP(S_(2n) = 0)
  $
  D'où $R_"cv" (tilde(G)) >= R_"cv" (tilde(F))$. Ainsi pour tout $t in Ioo(-1/(4 p q), 1 / (4 p q)) = I$
  $
    & tilde(F)(t) tilde(G)(t) 
    = sum_(n = 0)^(+oo) u_n t^n \
    =& sum_(n = 0)^(+oo) sum_(k = 0)^n PP(T_0 = 2k) PP(S_(2(n - k)) = 0) t^n \
    =& sum_(n = 0)^(+oo) PP(S_(2n) = 0) bb(1)_(n >= 1) t^n 
    = tilde(F)(t) - 1
  $
  D'où
  $
    tilde(G)(t) &= 1 - 1 / (tilde(F)(t)) \
    &= 1 - sqrt(1 - 4 p q t)
  $
  On a alors
  $
    PP(T_0 < +oo) &= sum_(k = 0)^(+oo) PP(T_0 = 2n) \
    &= tilde(G)(1) \ 
    &= 1 - sqrt(1 - 4 p q) \
    &= cases(space 1 "si" p = 1/2, space < 1 "si" p != 1/2)
  $

  Dans le cas $p = 1/2$
  $
    G(t) = G_T_0 (t) = 1 - sqrt(1 - t^2)
  $

+ On peut alors determiner $EE(T_0)$

  Si $p != 1/2$, $PP(T_0 = +oo) > 0$ et $EE(T_0) = +oo$.

  Sinon $p = 1/2$, or $G_T_0 (t) = 1 - sqrt(1 - t^2)$, qui n'est pas dérivable en $1$, donc $EE(T_0) = +oo$.

+ Temps du $k$-ème retour en $0$
  #let TR(j,k,a) = $attach(tl: #j, tr: #k, br: #a, T)$

  On note
  $
    TR(j,1,a) = min Set(n in NN^*, S^((j))_n = a) \
    TR(j,k,a) = min Set(n > TR(j,k-1,a), S^((j))_n = a) \
    TR(,k,a) = TR(0,k,a) quad quad TR(,,a) = TR(0,1,a)
  $
  Ainsi $TR(j,k,a)$ correspond au temps du $k$-ème retour en $a$ sur la marche decalée de $j$.
  $
    &PP(T^k_0 < +oo)\
    =& PP(T^k_0 < +oo, T^(k-1)_0 < +oo) \
    =& sum_(j = 1)^(+oo) PP(T^k_0 < +oo, T^(k - 1)_0 = j) \
    =& sum_(j = 1)^(+oo) PP(TR(j,1,0) < +oo, T^(k-1)_0 = j) \
    =& sum_(j = 1)^(+oo) PP(TR(j,1,0) < +oo) PP(T^(k-1)_0 = j) \
    =& PP(T_0 < +oo) sum_(j = 1)^(+oo) PP(T^(k-1)_0 = j) \
    =& PP(T_0 < +oo) PP(T^(k-1)_0 < +oo) \
    =& PP(T_0 < +oo)^k \
  $

+ On peut de plus dans le cas symétrique calculer $EE(abs(S_n))$.

  $
    abs(S_(N+1)) = &abs(S_N + 1) bb(1)_(X_(N+1) = 1) \ + &abs(S_N - 1) bb(1)_(X_(N+1) = -1) \
    EE(abs(S_(N+1))) = &EE(abs(S_N + 1)) PP(X_(N+1) = 1) \ + &EE(abs(S_N - 1)) PP(X_(N+1) = -1) \
    = &EE(1/2 (abs(S_N +1) + abs(S_N - 1))) \
    = &EE(abs(S_N) + bb(1)_(S_N = 0)) \
    = &EE(abs(S_N)) + PP(S_N = 0) \
  $
  Ainsi
  $
    EE(abs(S_n)) = sum_(k = 0)^(n - 1) PP(S_n = 0) \
    PP(S_(2 n) = 0) = (2 n)! / (2^n n!)^2 eqv(n -> oo) 1 / sqrt(pi n)
  $
  Qui est le terme général d'une série divergente
  $
    EE(abs(S_(2n))) &eqv(n -> oo) 1/sqrt(pi) sum_(k = 0)^(n - 1) 1/ sqrt(k) \
    &eqv(n -> oo) 2 sqrt(n) / sqrt(pi)
  $

// TODO: Plus de dimensions, cas uniforme, et temps de retour en a (M309-311)

#card("modeconvvad", "Modes de convergence des variables aléatoires", ("Maths.Probabilités",))

Modes de convergence des variables aléatoires.

#answer

On définit deux modes de convergence des variables aléatoires :

+ On dit que $(X_n)_(n in NN)$ converge en probabilité vers $X$ si #h(1fr)
  $
    forall delta > 0, PP(abs(X_n - X) >= delta) tends(n -> oo) 0
  $

+ On dit que $(X_n)_(n in NN)$ converge presque surement vers $X$ si
  $
    PP(X_n tends(n -> oo) X) = 1
  $
  Il s'agit bien d'un évenement : pour tout $omega in Omega$
  $
    &X_n (omega) tends(n -> oo) X(omega) \
    <=> & forall epsilon > 0, exists N in NN, forall n >= N, \ & abs(X_n (omega) - X(omega)) < epsilon \
    <=> & forall k in NN^*, exists N in NN, forall n >= N, \ & abs(X_n (omega) - X(omega)) < 1/k \
  $
  Ainsi
  $
    &(X_n tends(n -> oo) X) \ =& inter.big_(k in NN^*) union.big_(N in NN) inter.big_(n >= N) (abs(X_n - X) <= 1/k) \ in& cal(T)
  $

+ Si on se ramène à $X = 0$, notons pour tout $delta > 0$
  $
    A_(delta,n) = (abs(X_n) >= delta)
  $
  On veut
  $
    &PP(union.big_(N in NN) inter.big_(n >= N) abs(X_n) < delta) = 1 \
    <=>& PP(inter.big_(N in NN) union.big_(n >= N) A_(delta,n)) = 0
  $
  Donc par Borel-Cantelli faible, pour montrer $X_n tends("ps") X$, il suffit de montrer que
  $
    forall delta > 0, sum PP(A_(delta,n)) "converge"
  $

#card("chainmarko", "Chaînes de Markov", ("Maths.Probabilités",))

Chaînes de Markov.

#answer

On considère un ensemble fini d'état $E$, qu'on peut représenter par $[|1, N|]$.

Une chaîne de Markov sur $E$ est une suite $(X_n)_(n in NN)$ de variables aléatoires discrètes à valeur dans $E$ tel que si $n in NN$ et $i_0, dots, i_n in E^(n+1)$ tels que 
$
PP(X_0 = i_0, dots, X_n = i_n) > 0
$
Alors
$
  forall i_(n+1) in E, \
  PP(X_(n+1) = i_(n+1) | X_1 = i_1, dots, X_n = i_n) \
  = PP(X_(n+1) = i_(n+1) | X_n = i_n)
$
On dit de plus que la chaîne est homogène si
$
  forall i,j in E, n in NN, \
  PP(X_0 = j) > 0 \ => PP(X_(n+1) = i | X_n = j) = p_(i,j)
$
Ainsi par la formule des probabilités totales
$
  &PP(X_(n+1) = i) \ 
  =& sum_(j = 1)^N PP(X_(n+1) = i | X_n = j) PP(X_n = j) \
  =& sum_(j = 1)^N p_(i,j) PP(X_n = j)
$
Et donc en notant
$
  V_n = vec(PP(X_n = 1), dots.v, PP(X_n = N))
$
On a $V_(n+1) = P V_n$ avec
$
  P = (p_(i,j))_(i,j) in cal(M)_N (RR) \
$

*Propriétés*

On remarque que pour tout $j in [|1, N|]$
$
  sum_(i = 1)^N p_(i,j) &= sum_(i = 1)^N PP(X_1 = i | X_0 = j) \
  &= PP(X_1 in E | X_0 = j) = 1
$
Donc $P$ est une matrice stochastique, ainsi
$
  P^TT vec(1, dots.v, 1) = vec(1, dots.v, 1) \ 1 in "Sp"(P^TT) = "Sp"(P)
$
Et pour tout $lambda in "Sp"(P)$ et $vec(x_1, dots.v, x_N)$ vecteur propre non nul associé.
$
  P^TT vec(x_1, dots.v, x_N) = lambda vec(x_1, dots.v, x_N) quad abs(x_i_0) = max_(i in [|1, N|]) abs(x_i) \
  abs(lambda) dot abs(x_i_0) <= sum_(j = 1)^N abs(p_(j, i_0)) abs(x_i_0) = abs(x_i_0)
$
D'où $abs(lambda) <= 1$

// TODO: Exemple Markov M313

#card("jensenine", "Inégalité de Jensen pour les espérances", ("Maths.Probabilités",))

Inégalité de Jensen pour les espérances.

#answer

Soit $f : I -> RR$ convexe, et $X$ une vad à valeur dans $I$. Alors
$
  EE(f(X)) >= f(EE(X))
$
*Démonstration*

+ Cas $f$ $C^1$, pour tout $x in I$ #h(1fr)
  $
    f(x) >= f'(EE(X)) (x - EE(X)) + f(EE(X))
  $
  Ainsi, comme $X(Omega) subset.eq I$
  $
    f(X) >= f'(EE(X)) (X - EE(X)) + f(EE(X)) \
    EE(f(X)) >= f(EE(X))
  $

+ Dans le cas général, $f$ admet une droite d'appuis en tout points

  Pour tout $x in I$
  $
    f(x) >= f(EE(X)) + alpha(x - EE(X))
  $
  Avec $alpha in [f'_g (EE(X)), f'_d (EE(X))]$.

  Et on conclus de même.

#card("exingedf", "Exercice : troisième inégalité classique", ("Maths.Exercice.Probabilités",))

Soit $(X_k)_k in (LL^2)^NN^*$ indépendantes et centrées. 

On pose $S_n = sum_(k = 0)^n X_k$ et on suppose que
$
  sum_(k = 1)^(+oo) VV(X_k) = sum_(k = 1)^(+oo) EE(X_k^2) = sigma^2
$
Montrer que
$
  PP(max_(k in NN^*) abs(S_k) >= c) <= sigma^2 / c^2
$

#answer

Soit $(X_k)_k in (LL^2)^NN^*$ indépendantes et centrées.

On pose $S_n = sum_(k = 0)^n X_k$ et on suppose que
$
  sum_(k = 1)^(+oo) VV(X_k) = sum_(k = 1)^(+oo) EE(X_k^2) = sigma^2
$

On a déjà
$
  PP(abs(S_n) >= c) &= PP(S_n^2 >= c^2) <= EE(S_n^2) / c^2 \
  &= VV(S_n) / c^2 = sigma^2 / c^2
$

On pose
$
  A_k = (inter.big_(1 <= j <= k - 1) abs(S_j) <= c) inter (abs(S_k) > c) \
  B_n = (max_(1 <= k <= n) abs(S_n) > c) = union.plus.big_(k = 1)^n A_k
$
Ainsi
$
  bb(1)_B_n = sum_(k = 1)^n bb(1)_A_k \
  EE(S^2_n bb(1)_B_n) = sum_(k = 1)^n EE(S^2_n bb(1)_A_k)
$
Or
$
  S^2_n &= (S_k + sum_(j = k + 1)^n X_j)^2 \
  &= S_k^2 + 2 S_k (sum_(j = k + 1)^n X_j) + underbrace((sum_(j = k + 1)^n X_j)^2, >= 0)
$
D'où
$
  EE(S^2_n bb(1)_A_k) &>= EE(S^2_k bb(1)_A_k) \ 
  &+ 2 EE((S_k bb(1)_A_k) (sum_(j = k +1)^n X_j)) \
  &= EE(S^2_k bb(1)_A_k) \
  &+ 2 EE(S_k bb(1)_A_k) underbrace(EE(sum_(j = k +1)^n X_j), 0) \
  &= EE(S^2_k bb(1)_A_k)
  >= EE(c^2 bb(1)_A_k) \
  &>= c^2 PP(A_k)
$
Ainsi
$
  EE(S^2_n) &>= EE(S^2_n bb(1)_B_n) = sum_(k = 1)^n EE(S^2_n bb(1)_A_k) \
  &>= c^2 sum_(k = 1)^n PP(A_k) = c^2 PP(B_k)
$
D'où
$
  PP(B_k) <= EE(S_n^2) / c^2 = sigma^2 / c^2
$
Et par continuité croissante des probabilité on a le résultat.

#card("espsomein", "Espérance d'une série", ("Maths.Probabilités",))

Espérance d'une série.

#answer

Si $(A_k)_k in cal(T)^NN$ est une suite d'évenements, alors
$
  S = sum_(k = 0)^(+oo) bb(1)_A_k
$
Est une variable aléatoire discrète à valeur dans $NN union {+oo}$ et
$
  EE(sum_(k = 0)^(+oo) bb(1)_A_k) = EE(S) = sum_(k = 0)^(+oo) EE(bb(1)_A_k)
$

On peut généraliser ce résultat à $(X_k)_(k in NN)$ une suite de vad à valeur dans $NN$.

*Démonstration*

On pose
$
  S_n = sum_(k = 0)^n bb(1)_A_k
$

+ Montrons que $S$ est une variable aléatoire discrète. #h(1fr)
  $
    S(Omega) = underbrace(NN union {+oo}, "au plus dénombrable") \
    (S = k) = underbrace(union.big_(n >= k) (script(sum_(j = 0)^n bb(1)_A_j = k)) inter inter.big_(j >= n+1) overline(A_j), in cal(T)) \
    (S = +oo) = inter.big_(N in NN) union_(n >= N) A_n in cal(T)
  $

+ On remarque déjà que
  $
    sum_(k = 0)^n PP(A_k) = EE(S_n) <= EE(S)
  $
  Donc si $EE(S) < +oo$, $sum PP(A_n)$ converge.

  On suppose que $sum PP(A_n)$ converge.

  Par le lemme de Borel-Cantelli faible
  $
    PP(S = +oo) = PP(lim sup A_n) = 0
  $
  Or $EE(S) = sum_(n = 1)^(+oo) PP(S >= n)$, d'où par union croissante d'évenements
  $
    PP(S >= n) &= lim_(k -> oo) PP(S_k >= n) \
    sum_(n = 1)^N PP(S >= n) &= lim_(k -> oo) underbrace(sum_(n = 1)^N PP(S_k >= n), <= EE(S_k) = sum_(j = 0)^k PP(A_j)) \
    &<= sum_(k = 0)^(+oo) PP(A_k)
  $
  Donc $EE(S) <= sum_(n = 0)^(+oo) PP(A_n) < +oo$.

  On a ainsi l'équivalence de la convergence des deux sommes et leur égalité.

// NOTE: Correction marche aléatoires M316
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

Soit $f : Icc(a, b) -> E$, $C^n$ sur $Icc(a, b)$ et $D^(n+1)$ sur $Ioo(a,b)$

Il existe $c in Ioo(a, b)$ tel que
$
  f(b) = &sum_(k = 0)^(n) f^((k))(a) (b - a)^k / (k!) \ 
         &+ f^((n+1)) (c) (b - a)^(n+1) / ((n+1)!)
$


#card("anatlri", "Taylor reste intégrale", ("Maths.Analyse.Intégration", "Maths.Analyse.Taylor"))

Théorème de Taylor reste intégrale, et conditions d'application.

#answer

Soit $f : Icc(a, b) -> E$, $C^(n+1)$

#scale(90%, $
  f(b) = &sum_(k = 0)^(n) f^((k))(a) (b - a)^k / (k!)  \ &+ integral_a^b f^((n + 1)) (t) (b - t)^n / (n!) dif t \
  = &sum_(k = 0)^(n) f^((k))(a) (b - a)^k / (k!)  \ &+ (b - a)^(n+1) / n! integral_0^1 script((1 - s)^n f^((n + 1)) (a + s (b - a)) dif s) \
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

#card("bornes", "Théorème des bornes atteintes réel", ("Maths.Analyse.Continuité",))

Théorème des bornes atteintes et démonstration (Dans $RR$).

#answer

Si $f$ est $C^0 (Icc(a, b))$, alors $f$ est bornée et atteint ses bornes.

Preuve :

Notons $M = sup f$, quitte à avoir $M in overline(RR)$. $M in "adh"_overline(RR)(f(Icc(a, b)))$, donc il existe une suite $(x_n)$ à valeur dans $Icc(a, b)$ tel que $f(x_n) -> M$.

Par Bolzano-Weiestrass, il existe $phi$ tel que $x_(phi(n)) -> l$ avec $l in Icc(a, b)$ et donc nécéssairement $M in RR$.

#card("heine", "Théorème de Heine réel", ("Maths.Analyse.Continuité",))

Énoncé et démonstration du théorème de Heine (dans $RR$).

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
- Soit $x in G$, $macron(x)$ sa classe d'équivalence pour $re$. $macron(x) = H x = {h x, h in H}$.

  Par double inclusion :
  - $H x subset.eq macron(x)$ : Soit $y in H x$, $y = h x$ avec $h in H$, donc $y x^(-1) = h in H$ d'où $y re x$ et $y in macron(x)$.
  - $macron(x) subset.eq H x$ : Soit $y in macron(x)$, $y x^(-1) = h in H$, donc $y = h x in H x$.
- Donc $forall x in G, macron(x) = H x tilde.eq H$ d'où $abs(macron(x)) = abs(H)$.
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
- On remarque que pour $P in ZZ[X]$ et $k in ZZ$, $c(k P) = k c(P)$ et on étudie $tilde(P) = P / c(P)$ et $tilde(Q) = Q / c(Q)$.

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

- Notons $tilde(u) = u|_K^K$ l'endomorphisme induit par $u$ sur $K$.

  $
    tilde(u)^m (K) = u^m (K) = {0}
  $

  Donc $tilde(u)$ est nilpotent d'indice $m$.

- Notons $tilde(u) = u |_I^I$ l'endomorphisme induit par $u$ sur $I$.

  $
    tilde(u) (I) &= u (im u^m) = im u^(m+1) \
    &= im u^m = I
  $

  Donc $tilde(u)$ est inversible.

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
    det(A) = sum_(i = 1)^n (-1)^(i + j) a_(i j) det(tilde(A)_(i j))
  $

- pour tout $i in [|1, n|]$ : #h(1fr)

  $
    det(A) = sum_(j = 1)^n (-1)^(i + j) a_(i j) det(tilde(A)_(i j))
  $

Où $tilde(A)_(i j) in M_(n - 1) (KK)$ est la matrice $A$ privée de sa $i$#super[ème] ligne et $j$#super[ème] colonne.

On appelle $hat(A)_(i j) = (-1)^(i + j) det (tilde(A)_(i j))$ cofacteur.

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

- Si $"rg" A <= n - 2$, pour tout $i, j in [|1, n|]$ la matrice $tilde(A)_(i j)$ extraite de $A$ privée de sa $i$#super[ème] ligne et $j$#super[ème] colonne est de rang inférieur à $n - 2$ et n'est donc pas inversible, $"com" A = 0$ et $"rg" "com"(A) = 0$.

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
    A^((n + 1)) = mat(augment: #("hline": 1, "vline": 1), 1, *, dots.c, *; 0;dots.v,,tilde(A);0)
  $

On repète l'algorithme sur $tilde(A)$, on obtient alors

$
  tilde(tilde(A)) = mat(augment: #("hline": (4, 3), "vline": (4, 3)),
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
  tilde(tilde(tilde(A))) : quad C_j <- C_j - tilde(tilde(A))_(i j) / (tilde(tilde(A))_(i i)) C_i \
  tilde(tilde(tilde(A))) = mat(
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
      tilde(u) : func(H, im u, x, u(x)) \
      ker tilde(u) = ker u inter H = {0} \
      space dim H = "rg" u \
    $
    Donc $tilde(u)$ inversible.

    On peut donc écrire
    $
      w : func(F &= im u &plus.o& K, G, x &= y &+& z, v compose tilde(u)^(-1) (y))
    $

    Soit $x = y + z in E = ker u plus.o H$.

    $
     w compose u (x) &= v(tilde(u)^(-1) (u(z))) \
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
      tilde(u) : func(H, im u, x, u(x)) \
      w : func(G, E, x, tilde(u)^(-1) compose v (x))
    $
    On a bien pour $x in E$
    $
      u compose w(x) = tilde(u)(tilde(u)^(-1)(v(x))) = v(x)
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

- Soient $u in cal(L)(E)$, $F$ sev stable par $u$, $tilde(u)$ l'endomorphisme induit par $u$ sur $F$, on a toujours
  $
    chi_tilde(u) | chi_u
  $

*Démonstration*

- L'écrire.

- L'écrire.

- Soit $e = (e_1, dots, e_n)$ base de $F$ complété en base de $E$.

  $
  cal(M)_e (u) = mat(augment: #("hline": 1, "vline": 1), A, B; 0, C)
  $

  Avec $A = cal(M)_tilde(e) (tilde(u))$.

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

Si $F != {0}$ est un sev stable par $u$ et $u$ trigonalisable, alors $tilde(u)$ (induit par $u$ sur $F$) est trigonalisable (car $chi_tilde(u) | chi_u$ scindé).

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
  A = P mat(augment: #("vline": 1, "hline": 1), lambda, *, dots.c, *; 0; dots.v,,tilde(A);0) P^(-1)
$

Avec $tilde(A) in M_n (KK)$ et $chi_A = chi_tilde(A) (X - lambda)$ d'où $chi_tilde(A)$ scindé.

Par hypothèse de récurrence $tilde(A)$ est trigonalisable et on peut donc construire $P_0 in "GL"_(n+1) (KK)$ tel que

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

Notons $tilde(u)$ l'endomorphisme induit par $u$ sur $F$.

- $Pi_tilde(u) | Pi_u$

- Si $u$ diagonalisable, alors $tilde(u)$ aussi.

*Démonstration*

- $Pi_u (tilde(u)) = 0$ donc $Pi_tilde(u) | Pi_u$.

- Si $u$ diagonalisable, $Pi_u$ est SARS, donc $Pi_tilde(u)$ aussi (car divise) donc $tilde(u)$ est diagonalisable.

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

Soit $tilde(u)$ endomorphisme induit par $u$ sur $F_x_0$, qui est donc cyclique.

Soit $d in NN$ tel que 
$
e_0 = (x_0, u(x_0), dots, u^(d-1) (x_0))
$
Soit une base de $F_x_0$.
$
  cal(M)_e_0 (tilde(u)) = C_P = mat(augment: #3, 0,,,a_0;1,dots.down,,dots.v;,dots.down,0,a_(n-2);,,1,a_(n-1))
$
Où 
$
  tilde(u)^d (x_0) = u^d (x_0) = sum_(k = 0)^(d-1) a_k u^k (x_0) \
  P(X) = X^d - sum_(k = 0)^(d-1) a_k X^k \
  P(u)(x_0) = 0
$

Or $P = chi_C_P = chi_tilde(u) | chi_u$ donc
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

  Soit $tilde(u)$ l'induit par $u$ sur $ker u^q$.
  $
    cases(space tilde(u)^q = 0, space tilde(u)^(q - 1) != 0) " Donc " Pi_tilde(u) = X^q \
    X^q | Pi_tilde(u) | Pi_u = X^d Q \
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

+ Soit $tilde(u)$ induit par $u$ sur $G$ donc diagonalisable. #h(1fr)
  $
    G &= plus.o.big_(lambda in "Sp"(tilde(u))) E_lambda (tilde(u)) \
    &= plus.o.big_(k = 1)^N ker (tilde(u) - lambda_k id_G) \
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

  Soit $F$ sev stable par $u$ de dimension dans $[|1, n - 1|]$, et $tilde(u)$ l'endomorphisme induit.

  $
    chi_tilde(u) | chi_u
  $
  Avec $chi_tilde(u) = dim F != deg chi_u$ d'où $chi_u$ non irréductible.

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
  Soit $F$ sev stable par $u$, $tilde(u)$ induit par $u$ sur $F$. Par TDN 
  $
    F &= plus.o.big_(k = 1)^N ker P_k (tilde(u)) \
     &= plus.o.big_(k = 1)^N underbrace((ker P_k (tilde(u))) inter F, F_k)
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
  Est un sev stable, et admet donc $G$ comme supplémentaire stable. Notons $tilde(u)$ l'induit sur $G$ de $u$.
  $
    Pi_tilde(u) | Pi_u "scindé"
  $
  Donc $tilde(u)$ admet une valeur propre $lambda$ et un vecteur propre $x in F inter G = {0}$ qui est absurde. Donc $G = {0}$ et $F = E$ : $u$ est diagonalisable.

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
    underbrace((A - alpha I_n), tilde(A)) M - M B = 0
  $
  Avec $chi_tilde(A)$ scindé (pour toute valeur propre $lambda$ de $A$, $lambda - alpha$ est valeur propre de $tilde(A)$)

  Posons $phi' : N |-> tilde(A) N - N B$
  $
    phi' (M) = 0
  $
  Donc $phi'$ non injectif d'où $
  {mu} subset.eq "Sp"(tilde(A)) inter "Sp"(B) != emptyset
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

Soit $F$ sev stable par $u$. Soit $tilde(u)$ induit par $u$ sur $F$ qui est nilpotent car car $tilde(u)^n = 0$.

Or l'ordre de nilpotence de $tilde(u)$ est majoré par $d = dim F$ : $tilde(u)^d = 0$.

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

Notons $tilde(v)$ induit par $v$ sur $E_lambda (u)$, qui est encore trigonalisable, et admet donc un vecteur propre $e_1$.

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
Donc $F$ est stable par $v$, on peut donc y induire $tilde(v)$ qui est trigonalisable et admet donc $e_1$ vecteur propre commun aux $u_1, dots, u_(d+1)$.

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
  Donc $ker u$ est stable par $v$, posons $tilde(v)$ induit sur $ker u$. Or $tilde(v)$ admet un vecteur propre commun $x in ker u = E_0 (u)$.

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
  Pour tout $j in [|1, q|]$, on dispose de $tilde(M)_j$ et $mu_j$ tels que
  $
    mu_j^k = lambda_j \
    tilde(M)_j^k = I_m_j + 1/lambda_j N_j \
  $
  On définit alors
  $
    M_j &= mu_j tilde(M)_j \
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
#import "@preview/cetz:0.4.2"

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

+ Soit $A subset.eq E$ complet, fermé, avec $E$ evn) et $f : A -> A$. 

  Si $f$ est $k$-lipschitzienne avec $k < 1$, alors $f$ admet un unique point fixe.

+ Soit $K$ compact, convexe non vide, si $f : K -> K$ $1$-lipschitzienne, alors $f$ admet un point fixe.

// TODO: Points fixes linéaire (M205)

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

+ On pose $x_n = f^n ( x_0 )$ avec $x_0 in A$ quelconque. Ainsi
  $
    norm(x_(n+1) - x_n) <= k^n norm(x_1 - x_0)
  $
  D'où $sum (x_(n+1) - x_n)$ absolument convergente, donc convergente.

  Donc par continuité de $f$ et unicité de la limite $f(x_oo) = x_oo$.

  Soient $z, z'$ deux points fixes 
  $
    norm(f(z) - f(z')) &= norm(z - z) \
    &<= underbrace(k, <1) norm(z - z')
  $
  D'où $norm(z - z') = 0$.

+ Soit $x_0 in K$, pour $lambda in Ioo(0, 1)$ on considère
  $
    g_lambda : func(K, K, x, f(lambda x + (1 - lambda) x_0))
  $
  Soit $x, y in K$
  $
    norm(g_lambda (x) - g_lambda (y)) \
    = norm(f(script(lambda x + (1 - lambda) x_0)) - f(script(lambda y + (1 - lambda) x_0))) \
    <= norm(lambda x - lambda y) = lambda norm(x - y)
  $
  Donc $g_lambda$ est $lambda$-lipschitzienne, avec $lambda < 1$, donc $g_lambda$ admet un point fixe $x_lambda$.

  On considère $lambda_n = 1 - 1 / n$, comme $(x_lambda_n)_n in K^NN$, on dispose de $x_1$ valeur d'adhérance : 
  $
    (x_lambda_phi(n))_n -> x_1 in K
  $
  Or pour tout $lambda in Ioo(0, 1)$ :
  $
    norm(f(x_lambda) - x_lambda) 
    = norm(f(x_lambda) - g_lambda (x_lambda)) \
    = norm(f(x_lambda) - f(lambda x_lambda + (1 - lambda) x_0)) \
    <= (1 - lambda) underbrace(norm(x_lambda - x_0), "borné")
  $
  D'où
  $
    norm(f(x_lambda_phi(n)) - x_lambda_phi(n)) tends(n -> oo) 0
  $
  Et donc $f(x_1) = x_1$.

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

// TODO: Tout idéal stricte de C°(K, K) (K compacte) est inclus dans { f ∈ E | f(c) = 0 } pour un c ∈ K. (B-L ouvert, pabs).

#card("suitcauch", "Suites de Cauchy", ("Maths.Topologie",))

Définition, propriétés des suites de Cauchy.

#answer

Soit $(E, d)$ un espace métrique, $(u_n)_n in E^NN$ une suite.

On dit que $(u_n)_n$ est de Cauchy si
$
  forall epsilon > 0, exists N in NN, \ forall p, q >= N, d(u_p, u_q) < epsilon
$

Propriétés :

- Toute suite convergente est de Cauchy.

- Toute suite de Cauchy ayant une valeur d'adhérance converge.

- Toute suite de Cauchy est bornée.

- Si $E$ est un $KK$-evn de dimension finie, toute suite de cauchy converge.

On appelle espace complet un espace métrique où les suites de Cauchy converge, et espace de Banach un evn complet.

*Démonstration*

- L'écrire.

- Supposons $(u_n)_n$ de Cauchy et $(u_phi(n))_n -> l in E$. Soit $epsilon > 0$. #h(1fr)

  On dispose de $k in NN$ tel que $d(u_phi(k) - l) < epsilon / 2$.

  On dispose de $N in NN$ tel que pour tout $n >= N$
  $
    d(u_n, u_phi(k)) < epsilon
  $
  Ainsi
  $
    d(u_n, l) &<= d(u_n, u_phi(k)) + d(u_phi(k), l) \ &< epsilon
  $

- Supposons $(u_n)_n$ de Cauchy. Pour $epsilon = 1$ on dispose de $N in NN$ tel que pour tout $n >= N$
  $
    abs(u_n) <= d(u_n, u_0) + abs(u_0) < 1 + abs(u_0)
  $

- Supposons $(u_n)_n$ de Cauchy et $(E, norm(dot))$ un evn de dimension finie. Comme $(u_n)_n$ est de Cauchy, elle est bornée : $(u_n)_n in B(0, M)^NN$, qui est compacte, $(u_n)_n$ admet donc une valeur d'adhérance, et converge.

#card("seriesevn", "Séries dans un espace vectoriel normé", ("Maths.Topologie",))

Propriétés des séries dans une espace vectoriel normé.

#answer

Soit $(E, norm(dot))$ un $KK$-evn.

Toute séries absolument convergente est convergente ssi $E$ est un espace de Banach.

*Démonstration*

- En dimension finie (sans les suites de Cauchy) :

  Soit $u in E^NN$ tel que $sum norm(u_n)$ converge. #h(1fr)
  $
    norm(S_n) = norm(sum_(k = 0)^n u_n) <= S = sum_(k = 0)^(+oo) norm(u_k)
  $
  Donc $(S_n)_n$ est bornée et admet au moins une valeur d'adhérance.

  Soit $phi, psi$ tels que $(u_phi(n))_n -> l_1$, $(u_psi(n))_n -> l_2$.
  $
    norm(S_psi(n) - S_phi(n)) &<= sum_(k in [|psi(n), phi(n)|]) norm(u_k)  \
    &<= sum_(k = min(psi(n), phi(n)))^(+oo) norm(u_k) \ &tends(n -> +oo) 0
  $
  D'où $l_1 = l_2$.

- Soit $u in E^NN$, $E$ un espace de Banach, tel que $sum norm(u_n)$ converge.

  Pour tout $p >= q$
  $
    norm(S_p - S_q) &<= sum_(k = q + 1)^p norm(u_k) \
    &<= sum_(k = q + 1)^(+oo) norm(u_k) \
    &tends(q -> oo) 0
  $
  Donc $(S_n)$ est de Cauchy, et converge.

- Soit $(u_n)$ une suite de Cauchy. On construit $phi$ extractrice tel que $norm(u_phi(n+1) - u_phi(n)) <= 1 / n^2$ (qui est possible car $(u_n)$ est de Cauchy).

  Ainsi $sum (u_phi(n+1) - u_phi(n))$ est absolument convergente donc convergente et $(u_phi(n))_n$ converge, donc $(u_n)$ admet une valeur d'adhérance et converge.

#card("thmbaire", "Théorème de Baire", ("Maths.Topologie",))

Énoncé, démonstrations du théorème de Baire.

#answer

Dans $(E, norm(dot))$ espace de Banach, soit $A subset.eq E$ complet, et $(Omega_n)_(n in NN)$ une suite dénombrable d'ouverts denses dans $A$. Alors
$
  inter.big_(n in NN) Omega_n
$
Est dense dans $A$.

*Éléments de démonstration*

Suite de boules emboîtées, en alternant caractère ouvert et densité dans une récurrence bien construite pour trouver un point dans l'intersection à toute distance.

// TODO: Vraie démo

#card("conpararc", "Connexité par arcs", ("Maths.Topologie",))

Définition, propriétés de connexité par arcs.

#answer

Pour $X subset.eq E$ ($E$ espace métrique) et $a, b in X$, on appelle chemin continue reliant $a$ et $b$ une fonction
$
  gamma : func([0, 1], E, 0, a, 1, b, t, gamma(t) in X)
$

L'existence d'un chemin continue forme une relation d'équivalence.

- On appelle composentes connexes par arcs les classes d'équivalence pour cette relation.

- On dit que $X$ est connexe par arcs s'il n'y à qu'une seule classe d'équivalence pour cette relation.

- Si $f in C^0(X, F)$ et $X$ est connexe par arcs, alors $f(X)$ aussi.

*Démonstration*

- Soit $f(x) = a, f(y) = b in f(X)$, comme $X$ est connexe par arcs on dispose de $gamma$ chemin continue de $x$ à $y$.

  Posons $gamma' = f compose gamma$, continue par composition de fonctions qui le sont, et forme un chemin continue de $a$ à $b$.

  Donc $f(X)$ est connexe par arcs.

#card("condeglnc", "Connexité par arcs du groupe linéaire complexe", ("Maths.Topologie",))

Démonstrations de la connexité par arcs de $"GL"_n (CC)$.

#answer

+ Soit $A in "GL"_n (CC)$, pour tout $t in CC$ #h(1fr)
  $
    (1 - t) I_n + t A in.not "GL"_n (CC) \
    <=> A - (t - 1) / t in.not "GL"_n (CC) \
    <=> 1 - 1 / t in "Sp" (A)
  $
  Notons $D = { 1 / lambda - 1, lambda in "Sp"(A) }$ qui est fini, donc $CC^* \\ D$ est connexe par arcs, et on dispose de $gamma$ chemin continue de $0$ à $1$ dans $CC^*\\D$.
  $
    tilde(gamma) : t |-> (1 - gamma(t)) I_n + gamma(t) A
  $
  Convient.

+ En trigonalisant :
  $
    gamma : s -> P mat(gamma_1 (s),,(s t_(i j));,dots.down;,,gamma_n (s)) P^(-1)
  $
  Avec $gamma_i : [0, 1] -> CC^*$ chemin continue de $1$ à $gamma_i$.

+ On écrit $A$ comme produit de transvections et d'une dilatation, et on relie les termes. (Marche pour montrer la connexité par arcs de $"GL"_n^+ (RR)$ et $"GL"_n^-(RR)$).

#card("connexite", "Connexité", ("Maths.Topologie",))

Définition et propriétés de la connexité.

#answer

Une partie $X subset.eq E$ d'un espace métrique est dite connexe si les seules parties ouvertes et fermés de $X$ sont $emptyset$ et $X$.

- Si $X$ connexe par arcs, alors $X$ est connexe.

- $X$ est connexe ssi toute fonction $C^0(X, ZZ)$ est constante.

- Si $X$ est connexe, $overline(X)$ aussi.

Contre exemple de la reciproque de connexe par arcs implique connexe :

$
  X = { (x, sin(1/x)), x in Ioc(0, 1) } \
  overline(X) = X union {0} times [-1, 1]
$

- $X$ est connexe par arcs, donc connexe.
- $overline(X)$ est connexe car $X$ l'est.
- $overline(X)$ n'est pas connexe par arcs.

*Démonstration*

- + Supposons $X$ connexe par arcs, soit $A subset.eq X$ non vide ouverte et fermé.

    On dispose donc de $a in A$, supposons par l'absurde qu'on dispose de $b in X \\ A$.

    Comme $X$ est connexe par arcs, on dispose de $gamma$ chemin continue de $a$ à $b$.
    $
      t_0 = sup underbrace([0, 1] inter gamma^(-1) (A), Gamma)
    $
    Qui existe car $Gamma$ est non vide et majoré.

    On dispose donc de $(t_n)_n in Gamma^NN ->  t_0$
    $
      gamma(t_0) = lim_(n -> oo) underbrace(gamma(t_n), in A) in overline(A) = A
    $
    Or $A$ est ouvert, donc on dispose de $B_X (gamma(t_0), delta) subset.eq A$.

    Par continuité de $gamma$ on a $eta > 0$ tel que 
    $
    gamma(B(t_0, eta)) subset.eq B(gamma(t_0), delta) subset.eq A
    $
    Absurde.

  + Montrons que $bb(1)_A$ est continue.

    Soit $Omega subset RR$ ouvert
    $
      bb(1)^(-1)_A (Omega) \ = cases(
        space A &"si" 1 in Omega "et" 0 in.not Omega,
        space X\\A &"si" 1 in.not Omega "et" 0 in Omega,
        space emptyset &"si" 1 in.not Omega "et" 0 in.not Omega,
        space X &"si" 1 in Omega "et" 0 in.not Omega,
      )
    $
    Qui sont tous ouverts. Donc $bb(1)_A$ est continue, $bb(1)_A (X) subset.eq {0, 1}$ est connexe par arcs.

    Donc $bb(1)_A (X) = {0}$ ou $bb(1)_A (X) = {1}$

- ($arrow.double.l$) Soit $A subset.eq X$ ouvert et fermé, $bb(1)_A$ est continue (voir ci dessus) donc constante.

  ($=>$) Soit $f in C^0(X, ZZ)$, soit $k = f(x) in ZZ$,
  $
    f^(-1) {k} = f^(-1) Ioo(k - 1/2, k + 1/2)
  $
  Qui est ouvert et fermé.

- Supposons $X$ connexe, soit $f in C^0(overline(X), ZZ)$, et $tilde(f) = evaluated(f)_X$.

  Par connexité de $X$, $tilde(f)$ est constante et donc $f$ aussi sur $X$, et par continuité elle l'est sur $overline(X)$.

// TODO: Écrire cette fiche (M210 - M214)
#card("barycentres", "Barycentres", ("Maths.Topologie",))

Barycentres - revoir le cours / écrire la fiche.

#answer

Barycentres - revoir le cours / écrire la fiche.

Rapidement :

- À $(A_1, dots, A_n) in cal(E)^n$ (avec $E$ espace affine) et $lambda_1, dots, lambda_n in RR^n$ on associe $G in cal(E)$ l'unique point tel que #h(1fr)
  $
    sum_(k = 1)^n lambda_k va(G A_k) = va(0) \
    "i.e" sum_(k = 1)^n lambda_k (a_k - g) = 0
  $
  Qu'on appelle barycentre :
  $
    G = "Bar" { (A_k, lambda_k), k in [1, n] }
  $

- Les pondérations sont unique à facteur multiplicatif près, il en existe une unique tel que
  $
    sum_(k = 1)^n lambda_k = 1
  $

- Associativité du barycentre :

  Soit $(A_k)_k in cal(E)^(n + m)$ et $(lambda_k)_k in RR^(n + m)$ tel que 
  $
  alpha = sum_(k = 1)^n lambda_k != 0 != sum_(k = n + 1)^(n + m) lambda_k
  $
  Alors en posant
  $
    G_1 = "Bar" { (A_k, lambda_k), k in [|1, n|] } \
    G_2 = "Bar" { (A_k, lambda_k), k in [|n + 1, n + m|] } \
  $
  On a
  $
    G &= "Bar" { (A_k, lambda_k), k in [|1, n + m|] } \
    &= "Bar" { (G_1, alpha), (G_2, beta) }
  $

- $cal(F) subset.eq cal(E)$ est un sea ssi il est stable par barycentre.

- On dit que $d+1$ points sont en position général (dans un espace de dimension $d$) si $(va(A_0 A_k))_(k in [|1, d|])$ est libre.

- $cal(C) subset.eq cal(E)$ est convexe ssi pour tout $A_1, dots, A_n in cal(C)$ et $lambda_1, dots, lambda_n in RR_+$ tels que $sum_(k = 1)^n lambda_k != 0$
  $
    "Bar" { (A_k, lambda_k), k in [|1, n|] } in cal(C)
  $

- Pour $X subset.eq cal(E)$, il existe un plus petit convexe contenant $X$. On l'appelle enveloppe convexe de $X$ et
  $
    "Conv" (X) \ = Set( "Bar" { (A_k, lambda_k), k in [|1, n|] }\, n in NN\, \ (A_1, dots, A_n) in X^n\, (lambda_1, dots, lambda_n) in RR_+^n \ , sum_(k = 1)^n lambda_k != 0 ) = cal(C)
  $

- (Carathéoodory) Soit $d = dim cal(E)$, $X subset.eq cal(E)$
  $
    "Conv" (X) \ = Set( "Bar" { (A_k, lambda_k), k in [|1, d+1|] }\, \ (A_1, dots, A_(d+1)) in X^(d+1)\, \ (lambda_1\, dots, lambda_(d+1)) in RR_+^(d+1) \ , sum_(k = 1)^n lambda_k = 1)
  $

- Donc si $X$ est compact, $"Conv" X$ aussi.

#card("projconv", "Projection sur un convexe fermé", ("Maths.Topologie",))

Propriétés de projection sur un convexe fermé.

#answer

Soit $(E, scl(dot, dot))$ un espace euclidien, $C subset.eq E$ un convexe fermé.

$
  forall x in E, exists! p(x) in C, \ d(x, C) = d(x, p(x))
$

Et de plus pour tout $x in E$, et $z in C$, on a équivalence entre

+ $z = p(x)$

+ $forall y in C, scl(y - z, x - z) <= 0$

On a alors que $x |-> p(x)$ est $1$-lipschitzienne.

*Démonstration*

- Existence : la distance à un fermé est atteinte en dimension finie (ou dans un espace de Banach).

- Unicité : #h(1fr)

  #align(center, cetz.canvas({
    import cetz.draw: *

    let rad = _sizes.text * 20%
    let stroke = _sizes.text * 10%
    let col = _colors.text

    set-style(stroke: none, fill: col)
    circle((-1, 0), name: "z1", radius: rad)
    circle((1, 0), name: "z2", radius: rad)
    circle((0, -2), name: "x", radius: rad)

    set-style(stroke: col + stroke, fill: none)

    line("z1", "z2", "x", "z1")

    circle((0, 0), name: "c", radius: rad, fill: red, stroke: none)
    line("c", "x", stroke: red, fill: none)

    content((rel: (-0.3, 0), to: "z1"), $z_1$)
    content((rel: (0.3, 0), to: "z2"), $z_2$)
    content((rel: (0, -0.3), to: "x"), $x$)
  }))

  Soit $z_1, z_2 in C$ tels que $d(x, C) = d(x, z_1) = d(x, z_2)$.
  $
    d(x, C) &<= d(x, (z_1 + z_2) / 2) \
    &= 1/2 norm((x - z_1) + (x - z_2)) \
    &<= d(x, C)
  $
  On a égalité dans l'inégalité triangulaire pour une norme issue d'un produit scalaire : $(x - z_1)$ et $(x - z_2)$ sont positivement liés et de même norme (par hypothèse), d'où $z_1 = z_2$.

- Tangente :
  #align(center, cetz.canvas({
    import cetz.draw: *

    let rad = _sizes.text * 20%
    let stroke = _sizes.text * 10%
    let col = _colors.text

    set-style(stroke: col + stroke, fill: none)

    circle((0, 0), name: "C", radius: 1)

    circle((name: "C", anchor: 45deg), radius: rad, name: "z", fill: red, stroke: none)
    line((to: "z", rel: (-1, 1)), (to: "z", rel: (1, -1)), stroke: red + stroke)

    circle((0, 0.5), name: "y", radius: rad, fill: col, stroke: none)

    circle((1.5, 1.5), name: "x", radius: rad, fill: black, stroke: none)

    line("y", "z", "x")

    cetz.angle.angle("z", "x", "y", radius: 0.2)

    content((to: "z", rel: (0, 0.5)), $script(>= pi / 2)$)
    content((to: "z", rel: (0.6, 0)), text(fill: red)[$p(x)$])
    content((to: "x", rel: (0.3, 0)), $x$)
    content((to: "y", rel: (-0.3, 0)), $y$)
    content((to: "C.south", rel: (0, 0.5)), $C$)
  }))
  
  (i $=>$ ii) Soit $y in C$, on considère pour $t in [0, 1]$ :
  $
    y_t = (1 - t) z + t y \
  $
  $
    f(t) &= norm(x - y_t)^2  \
    &= norm((x - z) - t(y - z))^2 \
    &= norm(x - z)^2 - 2 t scl(x-z, y-z) \  &quad + t^2 norm(y - z)^2
  $
  Une fonction de $[0, 1] -> RR$ minimale en $0$ d'où
  $
    f'(0) >= 0 \
    -2 scl(x - z, y - z) >= 0
  $

  (ii $=>$ i) Pour $y = p(x)$ :
  $
    scl(p(x) - z, x - z) <= 0
  $
  Or par (i $=>$ ii) (avec $z' = p(x)$ et $y' = z$) on a
  $
    scl(z - p(x), x - p(x)) <= 0 \
    scl(p(x) - z, p(x) - x) <= 0 \
  $
  Donc par bilinéarité :
  $
    scl(z - p(x), z - p(x)) &= norm(z - p(x))^2 \ &<= 0
  $
  D'où $z = p(x)$.

- Soit $x, y in E$ :
  $
    scl(p(y) - p(x), x - p(x)) <= 0 \
    scl(p(x) - p(y), y - p(y)) <= 0 \ \
  $
  Donc
  $
    scl(p(y) - p(x), x - y + p(y) - p(x)) <= 0 \
    norm(p(y) - p(x))^2 \ + scl(p(y) - p(x), x - y) <= 0 \
    norm(p(y) - p(x))^2 <= scl(p(y) - p(x), y - x) \
    <= norm(p(y) - p(x)) dot norm(y - x) \
    norm(p(y) - p(x)) <= norm(y - x)
  $

#card("relcpct", "Relative compacité", ("Maths.Topologie",))

Définition de relative compacité.

#answer

Soit $E$ un $KK$-evn, $A subset.eq E$, on a équivalence entre

+ $overline(A)$ est compact.

+ Il existe $K$ compact tel que $A subset.eq K$.

+ $forall (x_n)_n in A^NN$, $exists phi "extractrice"$, $(x_phi(n))_n -> l in E$.

On dit dans ce cas que $A$ est relativement compact.

Si $A subset.eq E$ est relativement compacte, alors $A$ est précompacte.

*Démonstration*

- (i $=>$ ii) $A subset.eq overline(A)$ compact.

- (ii $=>$ i) $A subset.eq K$, donc $overline(A) subset.eq overline(K) = K$, $overline(A)$ est fermé dans un compact donc compact.

- (i $=>$ iii) Soit $(x_n)_n in A^NN subset.eq overline(A)^NN$, qu'on peut donc extraire par compacité.

- (iii $=>$ i) Soit $(y_n)_n in overline(A)^NN$, pour $n in NN$, $y_n in overline(A)$, on prend #h(1fr)
  $
    x_n in A inter B(y_n, 1 / 2^n)
  $
  Donc $(x_n)_n in A^NN$, par hypothèse $(x_phi(n)) -> l in overline(A)$.
  $
    norm(y_phi(n) - l) &<= underbrace(norm(y_phi(n) - x_phi(n)), < 1 / 2^n -> 0) \ &+ underbrace(norm(x_phi(n) - l), -> 0)
  $

- Soit $epsilon > 0$, $x_0 in A$, construisons par récurrence :
  $
    x_(n+1) in A \\ union.big_(k = 0)^n B(x_k, epsilon)
  $
  Comme une tel suite ne peut admètre de valeur d'adhérance, le procéssus doit se terminer.

  Ainsi on dispose de $x_0, dots, x_n$ tels que $A subset.eq union.big_(k = 0)^n B(x_k, epsilon)$ et $A$ est précompacte.

]
#[

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

#card("fbildege", "Formes bilinéaires non dégénérées", ("Maths.Algèbre.Euclidiens",))

Formes bilinéaires non dégénérées.

#answer

Soit $E$ un $RR$-ev. Pour $phi : E^2 -> RR$ une forme bilinéaire on considère
$
  psi : func(E, cal(L)(E, RR), x, phi_x : y |-> phi(x, y))
$
On dit que $phi$ est non dégénérée si $psi$ est unjective.

On a alors

- Si $phi$ bilinéaire symmétrique positive, $phi$ est un produit scalaire sur $E$ ssi $phi$ est non dégénérée.

*Démonstration*

- ($=>$) Si $phi$ est un produit scalaire, $x in ker psi$ #h(1fr)
  $
    psi(x) (x) = phi(x, x) = 0 => x = 0
  $

- ($arrow.l.double$) Supposons $phi$ non dégénérée, soit $x in E$ tel que $phi(x, x) = 0$. Soit $y in E$
  $
    0 <= psi(x)(y)^2 &= phi(x, y)^2 \ &<= underbrace(phi(x, x), 0) phi(y, y) \ &= 0
  $
  Donc $x in ker psi = {0}$ d'où $x = 0$.

#card("idpseucl", "Identités du produit scalaire", ("Maths.Algèbre.Euclidiens",))

Identités du produit scalaire (polarisation, parallèlogramme).

#answer

Soit $(E, scl(dot, dot))$ un $RR$-ev préhilbertien.

- (Polarisation) Pour $x, y in E$
  $
    scl(x, y) &= 1 / 2 (norm(x + y)^2 - norm(x)^2 - norm(y)^2) \
    &= 1/4 ( norm(x + y)^2 - norm(x - y)^2)
  $

- (Parallèlogramme) Pour $x, y in E$
  $
    norm(x + y)^2 + norm(x - y)^2 = 2 norm(x)^2 + 2 norm(y)^2
  $

#card("partieortho", "Orthogonal d'une partie", ("Maths.Algèbre.Euclidiens",))

Orthogonal d'une partie.

#answer

Soit $(E, scl(dot, dot))$ un $RR$-ev préhilbertien et $A subset.eq E$ une partie.

On définit 
$
A^perp &= Set(x in E, forall a in A\, scl(x, a) = 0) \
&= inter.big_(a in A) ker (x |-> scl(x, a))
$
Qui est donc un sev de $E$.

On a alors
- Pour $F$ sev de $E$, $F^perp inter F = {0}$.

- En dimension finie $F^perp plus.o F = E$

- Pour $F, G$ sevs de $E$, $(F + G)^perp = F^perp inter G^perp$.

*Démonstration*

- Par définie positivité.

- Projection.

- L'écrire.

#card("projecsev", "Projection orthogonale sur un sev de dimension finie", ("Maths.Algèbre.Euclidiens",))

Projection orthogonale sur un sev de dimension finie.

#answer

Soit $(E, scl(dot, dot))$ un $RR$-ev préhilbertien et $F$ sev de $E$.

Pour tout $x in E$, il existe un unique $z in F$ tel que $norm(x - z) = d(x, F)$, de plus si $(e_1, dots, e_d)$ est une bon de $F$
$
  z = sum_(j = 1)^d scl(x, e_j) e_j quad quad x - z in F^perp
$
Ainsi
$
  d(x, F)^2 &= norm(x - z)^2 \ &= norm(x)^2 - norm(z)^2 \
  &= norm(x)^2 - sum_(j = 1)^d scl(x, e_j)^2
$

// NOTE: M320 matrice d'une application bilinéaire

#card("exinegdetfam", "Exercice : Inégalité sur le determinant d'une famille de vecteurs", ("Maths.Algèbre.Euclidiens",))

Soit $(E, scl(dot, dot))$ euclidien de dimension $n$, $(x_1, dots, x_n) in E^n$ une famille de vecteurs et $e$ une BON. Montrer que $abs(det_e (x_1, dots, x_n))$ est indépendant de la BON $e$ choisie et que
$
  abs(det_e (x_1, dots, x_n)) <= product_(k = 1)^n norm(x_k)
$

#answer

+ Soit $e, e'$ deux BON de $E$ : #h(1fr)
  $
    abs(det_e (x_1, dots, x_n))  \ = abs(underbrace(det_e (e'), plus.minus 1) det_e' (x_1, dots, x_n)) \
  $

+ Si $(x_1, dots, x_n)$ n'est pas une base
  $
    0 &= abs(det_e (x_1, dots, x_n)) \
    &<= product_(k = 1)^n norm(x_k)
  $

+ Sinon, on pose $w = (w_1, dots, w_n)$ la BON obtenue par Gramm-Schmidt sur $x = (x_1, dots, x_n)$
  $
    forall i in [|1, n|], x_i &= sum_(k = 1)^n scl(x_i, w_k) w_k \ 
    &= sum_(k = i)^n scl(x_i, w_k) w_k \
  $
  $
    abs(det_e (x)) &= abs(det_w (x)) \ &= product_(k = 1)^n scl(x_k, w_k) \
    &<= product_(k = 1)^n norm(x_k)
  $
  Car $cal(M)_w (x) in T_n^+ (RR)$.

#card("thmrepr", "Théorème de représentation", ("Maths.Algèbre.Euclidiens",))

Théorème de représentation.

#answer

Pour $(E, scl(dot, dot))$ euclidien, soit $u in cal(L)(E, RR)$ une forme linéaire, on dispose d'un unique $w in E$ tel que
$
  forall x in E, u(x) = scl(x, w)
$

*Démonstration*

Comme $scl(dot, dot)$ est un produit scalaire
$
  psi : func(E, cal(L)(E, RR), x, y |-> scl(x, y))
$
Est injective et donc bijective par argument dimensionnel.

#card("adjendo", "Adjoint d'un endomorphisme", ("Maths.Algèbre.Euclidiens",))

Adjoint d'un endomorphisme.

#answer

Soit $(E, scl(dot, dot))$ et $u in cal(L)(E)$, pour tout $x in E$ il existe un unique $z_x in E$ tel que
$
  forall y in E, scl(u(y), x) = scl(y, z_x)
$
On pose alors
$
  u^* : func(E, E, x, z_x) in cal(L)(E)
$
Qui est l'unique adjoit de $u$. On le caractérise alors par
$
  forall x, y in E, scl(x, u(y)) = scl(u^* (x), y)
$

On a alors
- Pour tout $u in cal(L)(E), u^*^* = u$ #h(1fr)

- Pour toute BON $e$ de $E$
  $
    cal(M)_e (u^*) = cal(M)_e (u)^TT
  $

- Pour $u in cal(L)(E)$
  $
    ker (u^*) &= im (u)^perp \
    im (u^*) &= ker (u)^perp \
    "rg" u^* &= u
  $

- Pour $u in cal(L)(E)$
  $
    ker (u^* compose u) = ker u \
    "rg" (u^* compose u) = "rg" u
  $

- Pour tout $F$ sev de $E$ stable par $u$, $F^perp$ est stable par $u^*$

*Démonstration*

- Soit $x in E$, on pose #h(1fr)
  $
    phi_x : func(E, RR, y, scl(x, u (y)))
  $
  Par théorème de représentation on dispose d'un unique $z_x$ tel que
  $
    forall y in E, phi_x (y) = scl(z_x, y)
  $
  Soit $x, y, z in E$ et $alpha, beta in RR$
  $
    scl(alpha x + beta y, u(z)) \ = alpha scl(x, u(z)) + beta scl(y, u(z)) \
    = alpha scl(u^*(x), z) + beta scl(u^*(y), z) \
    = scl(alpha u^*(x) + beta u^*(y), z) \
    = scl(u^*(alpha x + beta y), z)
  $
  D'où par unicité 
  $
  u^*(alpha x + beta y) = alpha u^* (x) + beta u^* (y)
  $

- Les écrires

- On a $ker u subset.eq ker (u^* compose u)$. Soit $x in ker (u^* compose u)$.
  $
    scl(u^* (u(x)), x) &= 0 \
    &= scl(u(x), u(x)) \
    &= norm(u(x))^2
  $

#card("isomvec", "Isométries vectorielles", ("Maths.Algèbre.Euclidiens",))

Isométries vectorielles.

#answer

Soit $u in cal(L)(E)$, on dit que $u$ est une isométrie vectorielle (ou automorphisme orthogonal) si pour tout $x in E$
$
  norm(u(x)) = norm(x)
$

Ce qui est équivalent à
$
  forall x, y in E, scl(u(x), u(y)) = scl(x, y)
$

D'autre caractérisation équivalente des isométrie vectorielles :

- Il existe $e$ BON tel que $u(e)$ BON.
- Pour tout $e$ BON, $u(e)$ BON.
- $u^* compose u = u compose u^* = id$

On note $O(E)$ leur ensemble, qui forme un sous groupe compact de $"GL"(E)$.

On a alors

- Pour tout $u in O(E)$, $det(u) = plus.minus 1$.


*Démonstration*

- ($arrow.l.double$) Soit $x in E$ #h(1fr)
  $
    norm(u(x))^2 &= scl(u(x), u(x)) \ &= scl(x, x) = norm(x)^2
  $

- ($=>$) Soit $x, y in E$
  $
    scl(u(x), u(y)) \ = (norm(u(x + y))^2 - norm(u(x - y))^2) / 4 \
    (norm(x + y)^2 - norm(x - y)^2) / 4 \
    = scl(x, y)
  $

- Les écrires.

- $u in O(E)$
  $
    &<=> forall x, y in E, scl(u(x), u(y)) = scl(x, y) \
    &<=> forall x, y in E, scl(u^* compose u (x), y) = scl(x, y) \
    &<=> forall x, y in E, scl(u^* compose u (x) - x, y) = 0 \
    &<=> forall x in E, norm(u^* compose u(x) - x)^2 = 0
  $

- Écrire la démonstration pour $O(E)$ sous groupe de $"GL"(E)$.

- Pour tout $u in O(E)$, $norm(u)_"op" = 1$ donc $O(E)$ est borné et on montre facilement (par critère séquentiel) que $O(E)$ est fermé, donc compact.

#card("symprojortho", "Symétries et projecteurs ortogonaux", ("Maths.Algèbre.Euclidiens",))

Symétries et projecteurs ortogonaux.

#answer

Soit $(E, scl(dot, dot))$ euclidiens.

*Symmétries orthogonales*

Soit $s in cal(L)(E)$ tel que $s^2 = id$, on dit que $s$ est une symmétrie orthogonale si
$
  ker (s - id) perp ker (s + id) \ => E = ker (s - id) dperp ker(s + id)
$

Ou de manière équivalente, si $s$ est une isométrie vectorielle.

On appelle réflexion une symmétrie orthogonale par rapport à un hyperplan.

*Projecteurs orthogonaux*

Soit $p in cal(L)(E)$ tel que $p^2 = p$, on dit que $p$ est un projecteur orthogonale si
$
  ker (p - id) perp ker p \ => E = ker (p - id) dperp ker p
$

Ou de manière équivalente si $p$ est autoadjoint.

*Démonstration*

- ($=>$) Soit $s$ une symmétrie orthogonales, $x in E$, $F = ker (s - id)$
  $
    x = y + z quad quad y in F, z in F^perp \
  $
  $
    norm(s(x))^2 &= norm(s(y + z))^2 \ &= norm(y - z)^2 \
    &= norm(y)^2 + norm(-z)^2 \
    &= norm(x)^2
  $

- ($arrow.l.double$) Soit $s$ une symmétrie qui conserve la norme, et donc le produit scalaire. Soit $x in F = ker (s - id)$ et $y in G = ker (s + id)$.
  $
    scl(x, y) = scl(s(x), s(y)) = scl(x, -y) \
    scl(x, y) = 0
  $

#card("endosym", "Endomorphismes symmétriques ou autoadjoints", ("Maths.Algèbre.Euclidiens",))

Endomorphismes symmétriques ou autoadjoints.

#answer

Soit $(E, scl(dot, dot))$ euclidiens, on dit que $u in cal(L)(E)$ est autoadjoint (ou symmétrique) si $u^* = u$.

Pour toute BON $e$ (d'où symmétrique)
$
  cal(M)_e (u) = A = A^TT in S_n (RR)
$

On note $S(E)$ leur ensemble
$
  S = ker ((u |-> u^*) - id)
$
Qui est donc un sev de $cal(L)(E)$ et $dim S(E) = (n (n+1)) / 2$.

#card("thspectral", "Théorème spectrale", ("Maths.Algèbre.Euclidiens",))

Théorème spectrale.

#answer

Soit $A in M_n (RR)$, il y a équivalence entre

+ $A in S_n (RR)$.

+ $A$ est diagonalisable dans une BON.

+ $E$ s'écrit comme une somme directe orthogonale des sous espaces propres de $A$.

*Démonstration*

On suppose $A in S_n (RR)$

- Montrons d'abord que $"Sp"_CC (A) subset.eq RR$.

  Soit $lambda in "Sp"_CC (A), Z in CC^n \\ {0}$ vecteur propre associé. #h(1fr)
  $
    A Z &= lambda Z \
    overline(Z)^TT A Z &= lambda overline(Z)^TT Z = lambda sum_(k = 1)^n abs(z_k) in lambda RR^*_+ \
    overline(overline(Z)^T A Z) &= Z^TT overline(A) overline(Z) = Z^TT A overline(Z) in cal(M)_(11) (CC) \
    &= (Z^T A overline(Z))^TT = overline(Z)^TT A^TT Z \
    &= overline(Z)^TT A Z in RR
  $
  D'où $lambda in RR$ et $chi_A$ est scindé sur $RR$.

- Par recurrence sur $n$.

  Le cas $n = 1$ est évident.

  On suppose le résultat pour tout $k <= n in NN$, et $A in S_(n+1) (RR)$.

  Comme $chi_A$ est scindé sur $RR$, on dispose de $lambda_1 in RR in "Sp" (A)$.

  Ainsi $E_lambda_1 (A) = F$ est stable par $A$, donc $F^perp$ aussi.

  En considérent la bonne BON on a alors
  $
    P A P^T = mat(lambda_1 I_m, 0; 0, tilde(A)) = (P A P^T)^TT \
    tilde(A) = tilde(A)^TT in S_n (RR)
  $
  Et on conclus par hypothèse de récurrence.
]
#[

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/cetz:0.4.2"
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

#card("rayconv", "Rayon de convergence d'une séries entière", ("Maths.Analyse.Séries entières",))

Propriétés, définition du convergence d'une séries entière.

#answer

Soit $sum a_n z^n$ une série entière. On appelle $R = R_"cv" (sum a_n z^n)$ le rayon de convergence de $sum a_n z^n$
$
  R = sup space Set(r in RR_+, (a_n r^n) "bornée")
$

- (Lemme d'Abel) : Si $(a_n z_0^n)$ est bornée, alors pour tout $z in CC$ tel que $abs(z) < abs(z_0)$, $sum a_n z^n$ est ACV.

- Pour tout $z in CC$ (conséquence) : #h(1fr)
  $
    abs(z) < R quad quad sum a_n z^n "ACV" \
    abs(z) > R quad quad sum a_n z^n "DVG" \
  $

- Pour tout $alpha in CC^*$
  $
    R_"cv" (sum alpha a_n z^n) = R_"cv" (sum a_n z^n)
  $

- Pour tout $alpha in CC^*$
  $
    R_"cv" (sum a_n alpha^n z^n) = (R_"cv" (sum a_n z^n)) / abs(alpha)
  $

- Si pour tout $n in NN$, $abs(a_n) <= abs(b_n)$
  $
    R_"cv" (sum a_n z^n) >= R_"cv" (sum b_n z^n)
  $

- Si $a_n = O_(n -> oo)(b_n)$
  $
    R_"cv" (sum a_n z^n) >= R_"cv" (sum b_n z^n)
  $

- Si $a_n eqv(n -> oo) b_n$
  $
    R_"cv" (sum a_n z^n) = R_"cv" (sum b_n z^n)
  $

- Soient $(a_n)_n, (b_n)_n in CC^NN$
  $
    R_"cv" (sum (a_n + b_n) z^n) >= min(R_a, R_b)
  $
  Avec égalité si $R_a != R_b$.

- Soient $(a_n)_n, (b_n)_n in CC^NN$.
  $
      c_n = sum_(k = 0)^n a_k b_(n - k) \

      R_"cv"(sum c_n z^n) >= min (R_a, R_b) \

      forall z in DD(0, R_"cv"), \ sum_(n = 0)^(+oo) c_n z^n = (sum_(n = 0)^(+oo) a_n z^n) (sum_(n = 0)^(+oo) b_n z^n)
  $

#card("regse", "Régularité des séries entières", ("Maths.Analyse.Séries entières",))

Régularité des séries entières.

#answer

Soit $(a_n)_n in CC^NN$ et $R = R_"cv" (sum a_n z^n)$.

Pour tout $0 < r < R$
$
  f : func(DD(0, r), CC, z, sum_(n = 0)^(+oo) a_n z^n)
$
Est $C^0$ sur $DD(0, r)$,
$
  g : func(Ioo(-R, R), CC, x, sum_(n = 0)^(+oo) a_n x^n)
$
Est $C^oo$ sur $Ioo(-R, R)$. Et pour tout $k in NN$
$
  f^((k)) : x |-> sum_(n = 0)^(+oo) (n + k)! / n! a_(n + k) x^n
$

*Démonstration*

- Pour tout $r < R$ on a CVU de 
  $
    f : func(DD(0, r), CC, z, sum_(n = 0)^(+oo) a_n z^n)
  $
  Et donc par le théorème de continuité des séries de fonctions, $f$ est $C^0$ sur $DD(0, r)$.

- $R_"cv" (sum n a_n z^n) = R_"cv" (sum a_n z^n)$ :

  Soit $z in DD(0, R), r = abs(z)$, pour $r_0 in Ioo(r, R)$, $(a_n r_0^n)$ est bornée.
  $
    abs(n a_n z^n) = underbrace(abs(a_n r_0^n), "bornée") dot underbrace(n (r / r_0)^n, -> 0) \
    R_"cv" (sum n a_n z^n) >= R_"cv" (sum a_n z^n)
  $
  L'autre sens est évident :
  $
    R_"cv" (sum n a_n z^n) = R_"cv" (sum a_n z^n)
  $

- On applique le théorème $C^1$, qui donne la dérivée comme un série entière de même rayon de convergence (puis récurrence).

#card("regidse", "Rigidité des séries entières", ("Maths.Analyse.Séries entières",))

Rigidité des séries entières.

#answer

Soit $sum a_n z^n$ une série entière de rayon de convergence $R$.
$
  f : func(Ioo(-R, R), CC, x, sum_(n = 0)^(+oo) a_n x^n)
$
Pour tout $n in NN$
$
  a_n = (f^((n)) (0)) / n!
$
*Corolaire*

Si deux séries entières coincident sur un intervalle $Ico(0, delta)$ avec $delta > 0$, alors ce sont les mêmes.

*Démonstration*

- Pour tout $k in NN$ #h(1fr)
  $
    f^((k)) (x) = sum_(n = 0)^(+oo) (n + k)! / n! a_(n + k) x^n \
    f^((k)) (0) = k! a_k 
  $

- Soit 
  $
  g : func(Ioo(-R', R'), CC, x, sum_(n = 0)^(+oo) b_n x^n)
  $
  et $delta in Ioc(0, min(R, R'))$ tel que
  $
    forall x in Ico(0, delta), space f(x) = g(x)
  $
  Alors pour tout $k in NN$
  $
    f^((k)) = g^((k))
  $
  D'où (par continuité)
  $
    a_k = b_k
  $

#card("lemradabel", "Lemme radiale d'Abel", ("Maths.Analyse.Séries entières",))

Lemme radiale d'Abel.

#answer

Soit $sum a_n z^n$ une série entière de rayon de convergence $R > 0$.
$
  f : func(Ioo(-R, R), CC, x, sum_(n = 0)^(+oo) a_n x^n)
$
Si $sum a_n R^n$ converge alors $f$ CVU sur $[0, R]$. Ainsi
$
  lim_(x -> R) f(x) = sum_(n = 0)^(+oo) a_n R^n
$

*Démonstration*

- Cas $R = 1$ : #h(1fr)

  On a $sum a_n$ qui converge, et $x |-> sum a_n x^n$ CVS sur $[0, 1]$.

  $
  rho_n = sum_(k = n+1)^(+oo) a_k tends(n -> oo) 0 \
  $
  Soit $epsilon > 0$ et $N in NN$ tel que pour tout $n >= N$, $abs(rho_n) < epsilon$. Pour tout $x in Ico(0, 1)$
  $
  abs(R_n (x)) &= abs(sum_(k = n + 1)^(+oo) a_k x^k) \
  &= abs(rho_n x^(n+1) + sum_(k = n+1)^(+oo) rho_k (x^(k+1) - x^k) ) \
  &<= abs(rho_n) + sum_(k = n + 1)^(+oo) abs(rho_k) (x^k - x^(k+1)) \
  &< epsilon + epsilon sum_(k = n+1)^(+oo) (x^k - x^(k-1)) \
  &< epsilon + epsilon x^(n + 1) < 2 epsilon
  $
  Et
  $
    abs(R_n (1)) = abs(rho_n) < epsilon
  $
  D'où
  $
    sup_(x in [0, 1]) abs(R_n) < 2 epsilon
  $
  Donc CVN sur $[0, 1]$.

- Cas général :
  $
    b_n = a_n R^n quad quad R_"cv" (sum b_n x^n) = 1
  $
  Comme $sum b_n$ converge, le cas $R = 1$ s'applique et
  $
    sup_(x in [0, R]) abs(sum_(k = n + 1)^(+oo) a_n x^n) = sup_(t in [0, 1]) abs(sum_(k = n+1)^(+oo) underbrace(a_n R^n, b_n) x^n)
  $

// NOTE: M169 Fractions rationnelles (+ Exo)

#card("somosurlebord", "Sommation des petit o sur le bord", ("Maths.Analyse.Séries entières",))

Sommation des petit $o$ sur le bord (HP).

#answer

Pour
$
  f : func(Ioo(-1, -1), RR, x, sum_(n = 0)^(+oo) alpha_n x^n) \
  g : func(Ioo(-1, -1), RR, x, sum_(n = 0)^(+oo) a_n x^n) \
  forall n in NN, alpha_n >= 0 quad quad sum alpha_n "diverge" \
$
Alors
- Si $a_n = o_(n -> oo) (alpha_n)$ : #h(1fr)
  $
    g(x) = o_(x -> 1^-) (f(x))
  $
- Si $a_n eqv(n -> +oo) alpha_n$ : #h(1fr)
  $
    g(x) eqv(x -> 1^-) f(x)
  $

*Démonstration*

On montre que le cas du $o$ car il implique l'équivalent.

Soit $epsilon > 0$, on dispose de $N in NN$ tel que pour tout $n >= N$, 
$
  abs(a_n) <= epsilon alpha_n
$
Pour tout $x in Ico(0, 1)$
$
  abs(g(x)) &<= (sum_(n = 0)^(N - 1) abs(a_n)) + sum_(n = N)^(+oo) underbrace(abs(a_n), <= epsilon alpha_n) x^n \
  &<= C_N + epsilon f(x)
$
Comme $f(x) tends(x -> 1) +oo$, on dispose de $delta > 0$ tel que pour tout $x in Ioo(1 - delta, 1)$
$
  f(x) >= C_N / epsilon
$
Ainsi
$
  abs(g(x)) <= 2epsilon f(x) \
  g(x) = o_(x -> 1^-) (f(x))
$

#card("exabelcesaro", "Exercice : Lemme radiale d'Abel version Césaro", ("Maths.Exercice.Séries entières",))

Soit
$
  f : func(Ioo(-1, 1), RR, x, sum_(n = 0)^(+oo) a_n x^n) \
  forall k in NN, s_k = sum_(n = 0)^(k) a_k \
  forall N in NN, sigma_k = 1 / (N+1) sum_(k = 0)^(N) s_k
$
On suppose que $sigma_n tends(n -> oo) l$, montrer que $f(x) tends(x -> 1^-) l$

#answer

On pose
$
  g(x) &= sum_(n = 0)^(+oo) s_n x^n \
  &= sum_(n = 0)^(+oo) sum_(k = 0)^n a_k x^k x^(n - k) \
  &= f(x) / (1 - x)
$
Avec un rayon de convergence de $1$. Et
$
  h(x) &= sum_(n = 0)^(+oo) (n+1) sigma_n x^n \
  &= g(x) / (1 - x) = f(x) / (1 - x)^2
$
Or $sigma_n = l + o(1)$
$
  (n+1) sigma_n = (n+1) l + o(n + 1) \
  h(x) = sum_(n = 0)^(+oo) (n+1) l x^n + sum_(n = 0)^(+oo) c_n x^n
$
Avec $c_n = o(n + 1)$, or $sum_(n = 0)^(+oo) (n+1) x^n = 1 / (1 - x)^2$ et comme $sum (n+1)$ diverge, par sommation des petits $o$ sur le bord (à redémontrer)
$
  sum_(n = 0)^(+oo) c_n x^n = o_(x -> 1)( 1 /(1 - x)^2) \
$
$
  h(x) &= l / (1 - x)^2 + o (1 / (1 - x)^2) \
  &= f(x) / (1 - x)^2
$
Donc
$
  f(x) = l + o(1)
$

#card("premformcauch", "Première formule de Cauchy", ("Maths.Analyse.Séries entières",))

Première formule de Cauchy (HP).

#answer

Soit ($R in RR^*_+ union {+oo}$)
$
  f : func(DD(0, R), CC, z, sum_(n = 0)^(+oo) a_n z^n)
$
On a
$
  1 / (2 pi) integral_0^(2pi) f(r e^(i n theta)) dif theta = a_n r^n bb(1)_(n >= 0)
$

*Démonstration*

Montrons la CVN de la série
$
  sup_(theta i [0, 2pi]) abs(a_n r^n e^(i n theta)) = abs(a_n) r^n
$
Qui est le terme général d'une série convergente ($r < R$). Et
$
  integral_0^(2pi) abs(a_n r^n e^(i n theta)) dif theta = 2pi abs(a_n) r^n
$
Qui est aussi le terme général d'une série convergente.

Par le théorème d'intégration terme à terme (verifier les hypothèses) :

$
  space& 1 / (2pi) integral_0^(2pi) f(r e^(i n theta)) e^(- i n theta) dif theta \
  =& 1 / (2pi) integral_0^(2pi) sum_(k = 0)^(+oo) a_k r^k e^(i k theta) e^(- i n theta) dif theta \
  =& 1 / (2pi) sum_(k = 0)^(+oo) a_k r^k underbrace(integral_0^(2pi) e^(i(k - n) theta) dif theta, 2 pi delta_(k,n)) \
  =& a_n r^n bb(1)_(n >= 0)
$

#card("formparce", "Formule de Parseval", ("Maths.Analyse.Séries entières",))

Formule de Parseval.

#answer

Soit ($R in RR^*_+ union {+oo}$)
$
  f : func(DD(0, R), CC, z, sum_(n = 0)^(+oo) a_n z^n)
$
Pour tout $r in Ioo(0, R)$ on a
$
  1 / (2pi) integral_0^(2pi) abs(f(r e^(i theta)))^2 dif theta = sum_(n = 0)^(+oo) abs(a_n)^2 r^(2n)
$

*Démonstration*

Pour tout $r < R$ et $theta in RR$
$
  abs(f(r e^(i theta)))^2 &= f(r e^(i theta)) overline(f(r e^(i theta))) \
$
$
  &= (sum_(k = 0)^(+oo) a_k r^k e^(i k theta)) (sum_(k = 0)^(+oo) overline(a_k) r^k e^(- i k theta)) \
  &= sum_(k, n in NN) a_k overline(a_n) r^(k +n) e^(i (k - n) theta)
$
Puis on applique le théorème d'intégration terme à terme (par bijection de $NN^2$ dans $NN$)
$
  & 1 / (2 pi) integral_0^(2pi) abs(a_k overline(a_n) r^(k + n) e^(i (k - n) theta)) dif theta  \
  =& abs(a_k) abs(a_n) r^(k + n)
$
Et 
$
sum_(k, n in NN) abs(a_k) abs(a_n) r^(k + n) &= (sum_(k = 0)^(+oo) abs(a_k) r^k)^2 \  &< +oo
$
D'où
$
& 1 / (2pi) integral_0^(2pi) abs(f(r e^(i theta)))^2 dif theta \ 
=& sum_(k,n in NN) a_k overline(a_n) r^(k + n) 1 / (2pi) underbrace(integral_0^(2pi) e^(i (k - n) theta) dif theta, delta_(k,n)) \
=& sum_(n = 0)^(+oo) abs(a_n)^2 r^(2n)
$

#card("princmax", "Principe du maximum", ("Maths.Analyse.Séries entières",))

Principe du maximum.

#answer

Soit ($R in RR^*_+ union {+oo}$)
$
  f : func(DD(0, R), CC, z, sum_(n = 0)^(+oo) a_n z^n)
$

+ Si $abs(f)$ admet un maximum local en $0$, alors $f$ est constante sur $DD(0, R)$.

+ Si $abs(f)$ admet un maximum local en $z_0 in DD(0, R)$, alors $f$ est constante sur $DD(0, R)$.

+ Si $f$ est prolongeable par continuité sur $overline(DD(0, R))$, alors #h(1fr)
  $
    max_DD(0, R) abs(f) = max_(SS(0, R)) abs(f)
  $

*Démonstration*

+ On suppose (pour un $epsilon in Ioo(0, R)$) #h(1fr)
  $
  abs(a_0) = abs(f(0)) = max_(overline(DD(0, epsilon))) abs(f)
  $
  Pour tout $r in Ioc(0, epsilon)$
  $
    abs(a^0)^2 &= abs(f(0))^2  \ 
    &>= 1/(2pi) integral_0^(2pi) abs(f(r e^(i theta)))^2 dif theta \
    &= sum_(n = 0)^(+oo) abs(a_n)^2 r^(2n) >= abs(a_0)^2
  $
  Donc $forall n in NN^*, a_n = 0$, et $f$ est constante.

+ On suppose que $abs(f)$ admet un maximum local en $z_0 in DD(0, R)$.

  On redemontre que $f$ est DSE en $z_0$ :

  Pour tout $h in DD(0, delta)$ ou $delta = R - abs(z_0)$
  $
    f(z_0 + h) = sum_(n = 0)^(+oo) b_n h^n
  $
  Où $(b_n) in CC^n$, et $h |-> f(z_0 + h)$ vérifie 1. donc est constante sur $DD(0, delta)$, et tout point de $overline(DD(0, delta))$ est un maximum local. On peut dont repéter ce raisonnement pour atteindre $0$ puis appliquer 1.

  #align(center, cetz.canvas(length: 4em, {
    import cetz.draw: *

    let r = 0.8
    let i = 0
    let a = 45deg

    circle((0, 0), radius: 1, stroke: _colors.text)

    while r >= 0.25 {
      circle((angle: a, radius: r), radius: 0.02, fill: _colors.text)
      content((), anchor: "north-west", $z_#i$)
      circle((angle: a, radius: r), radius: 1.0 - r, stroke: red)
      
      r = (3 * r - 1) / 2
      r = calc.floor(r * 1024) / 1024.0
      i = i + 1
    }

    circle((0, 0), radius: 0.02, fill: _colors.text)
    content((), anchor: "north-west", $O$)

  }))

+ Par disjonction de cas :
  - Si le $max_(overline(DD(0, R))) abs(f)$ est atteint dans $DD(0, R)$, alors par 2., $f$ est constante, donc il est aussi atteint sur $SS(0, R)$
  - Sinon il ne peut être atteint que sur $SS(0, R)$.

#card("deuxformca", "Deuxième formule de Cauchy", ("Maths.Analyse.Séries entières",))

Deuxième formule de Cauchy.

#answer

Soit $f in C^0(DD(0, R), CC)$, $r < R$, $z in DD(0, r)$.
$
  g(z) = 1/(2pi) integral_0^(2pi) (f(r e^(i theta))) / (r e ^(i theta) - z) r e^(i theta) dif theta
$

Alors $g : DD(0, r) -> CC$ est DSE et si $f$ est DSE sur $DD(0, R)$, alors $g(z) = f(z)$ sur $DD(0, r)$.

On en déduit que si pour $n in NN$ on a
$
  f_n : func(DD(0, R), CC, z, sum_(k = 0)^(+oo) a_(n,k) x^k)
$
Et $r < R$, $(f_n)$ CVU sur $overline(DD(0, R))$ vers $f$, alors $f$ est DSE sur $DD(0, r)$.

*Démonstration*

Soit $z in DD(0, r)$, comme $abs(z) / abs(r e^(i theta)) < 1$
$
  r e^(i theta) / (r e^(i theta) - z) = 1 / (1 - z / (r e^(i theta))) = sum_(n = 0)^(+oo) z^n / r^n e^(-i n theta)
$
On pose $f_n : theta |-> z^n / r^n e^(-i n theta) f(r e^(i theta))$
$
theta |-> sum_(n = 0)^(+oo) f_n (theta) = f(r e^(i theta)) / (r e^(i theta) - z) r e^(i theta)
$
Qui est continue sur $[0, 2pi]$
$
  integral_0^(2pi) abs(f_n (theta)) dif theta <= 2 pi norm(f)_(oo, overline(DD(0, R))) dot abs(z / r)^n 
$
Qui est le terme général d'une série convergente, donc par intégration terme à terme :
$
g(z) = sum_(n = 0)^(+oo) ( 1 / (2pi r^n) integral_0^(2pi) f(r e^(i theta)) e^(- i n theta) dif theta) z^n
$
Et $g$ est bien DSE sur $DD(0, r)$

On suppose de plus que
$
  f : func(DD(0, R), CC, z, sum_(n = 0)^(+oo) a_n z^n)
$
Alors par la première formule de cauchy, $f(z) = g(z)$ pour $z in DD(0, r)$.

Ainsi pour
$
  f_n : func(DD(0, R), CC, z, sum_(k = 0)^(+oo) a_(n,k) x^k)
$
avec $r < R$ et $(f_n)$ CVU vers $f$ sur $overline(DD(0, R))$, on a pour tout $n in NN, z in DD(0, r)$
$
  f_n (z) = 1 / (2pi) integral_0^(2pi) (f_n (r e^(i theta))) / (r e^(i theta) - z) r e^(i theta) dif theta
$
Donc par CVU sur $[0, 2pi]$ quand $n$ tends vers $+oo$
$
 f(z) = 1 / (2pi) integral_0^(2pi) (f(r e^(i theta)) / (r e^(i theta) - z)) r e^(i theta) dif theta
$
Et par 1. $f$ est DSE.

#card("exprodcauch", "Exercice : Produit de cauchy par les séries entières", ("Maths.Exercice.Séries entières",))

Soient $(a_n)_n, (b_n)_n in CC^NN$ et
$
  forall n in NN, c_n = sum_(k = 0)^n a_n b_(n - k)
$
On suppose que $sum a_n$, $sum b_n$ et $sum c_n$ convergent, montrer que
$
  sum_(n = 0)^(+oo) c_n = (sum_(n = 0)^(+oo) a_n)(sum_(n = 0)^(+oo) b_n)
$

#answer

Par hypothèse, pour $u in {a, b, c}$ :
$
  R_u = R_"cv" (sum u_n z^n) >= 1 \
  f_u : func(DD(0, 1), CC, z, sum_(n = 0)^(+oo) u_n z^n)
$
Et par produit de Cauchy :
$
  forall z in DD(0,1), quad f_c (z) = f_a (z) f_b (z)
$
Or par le lemme radiale d'Abel, pour $u in {a, b, c}$
$
  sum_(n = 0)^(+oo) u_n = lim_(z -> 1^-) f_u (z)
$
Ainsi
$
  sum_(n = 0)^(+oo) c_n &= lim_(z -> 1^-) f_c (z) \
  &= lim_(z -> 1^-) f_a (z) f_b (z) \
  &= (sum_(n = 0)^(+oo) a_n) (sum_(n = 0)^(+oo) b_n) \
$

#card("exsederang", "Exercice : nombre de dérangements par les séries entières", ("Maths.Exercice.Séries entières",))

On pose 
$
  D_n = Set(sigma in frak(S)_n, "Fix" (sigma) = emptyset) \
  d_n = abs(D_n)
$
Donner une formule pour $d_n$ en utilisant les séries entières.

#answer

On cherche une relation sur $d_k$ :

+ On peut écrire #h(1fr)
  $
    frak(S)_n = union.big.plus_(k = 0)^(n) union.big.plus_(A subset.eq [|1, n|] \ abs(A) = k) Set(sigma in frak(S)_n, "Fix" (sigma) = A) \
    n! = sum_(k = 0)^n vec(n, k) d_(n - k) = sum_(k = 0)^n vec(n, k) d_k \
    1 = sum_(k = 0)^n 1 / (n - k)! dot d_k / k!
  $
  Ainsi en posant
  $
    f : func(Ioo(-1, 1), RR, x, sum_(n = 0)^(+oo) d_n / n! x^n)
  $
  On trouve, pour $x in Ioo(-1, 1)$
  $
    1 / (1 - x) &= sum_(n = 0)^(+oo) 1 dot x^n \
    &= sum_(n = 0)^(+oo) (sum_(k = 0)^n 1 / (n - k)! d_k / k!) x^n \
    &= (sum_(n = 0)^(+oo) x^n / n!) (sum_(n = 0)^(+oo) d_n / n! x^n) \
    &= f(x) e^x
  $
  Ainsi
  $
    f(x) &= e^(-x) / (1 - x) \ 
    &= (sum_(n = 0)^(+oo) (-1)^n / n! x^n) (sum_(n = 0)^(+oo) x^n) \
    d_n / n! &= sum_(k = 0)^(n) (-1)^k / k!
    
  $

+ On construit une bijection 
  $
  theta : D_(n+1) -> [|1, n|] times (d_(n-1) union.plus d_n)
  $

  Soit $sigma in D_(n+1)$, on pose $k = sigma(n+1)$.

  - Si $sigma(k) = n+1$ : on pose #h(1fr)
    $
      tilde(sigma) = sigma|_([|1, n|]\\{k}) in D_(n-1)
    $
  - Sinon, $j = sigma^(-1) (n+1)$ : on pose
    $
      tilde(sigma) = func([|1, n|], [|1,n|], i != j, sigma(i), j, k) in D_n
    $
  Ainsi
  $
    theta(sigma) = (k, tilde(sigma))
  $

  On montre que c'est une bijection (l'écrire).

  Ainsi
  $
  d_(n+1) = n (d_n + d_(n-1))
  $

  On en déduit
  $
    (1 - x)f'(x) = x f(x) 
  $
  D'où
  $
    f(x) = e^(-x) / (1 - x)
  $
  Et on conclut de même.

#card("excatalan", "Exercice : nombres de Catalan avec les séries entières", ("Maths.Exercice.Séries entières",))

On définit le $n$-ème nombre de Catalan
$
  C_0 = 1, forall n in NN^*, C_n = sum_(k = 0)^(n - 1) C_k C_(n - k) \
  f : func(Ioo(-R, R), RR, x, sum_(n = 0)^(+oo) C_n x^n)
$
Donner une forme explicite de $f$ et son rayon de convergence, en déduire une expression de $C_n$.

#answer

*Analyse*

On suppose que $R > 0$, pour tout $x in Ioo(-R, R)$
$
  f(x) &= 1 + x sum_(n = 0)^(+oo) C_(n+1)x^n \
  &= 1 + x sum_(n = 0)^(+oo) (sum_(k = 0)^n C_n C_(n - k)) x^n \
  &= 1 + x f(x)^2
$
D'où pour $x in Ioo(-1/4, 1/4)$
$
  f(x) = (1 - sqrt(1 - 4x)) / (2 x)
$

*Synthèse*

On considère
$
  f : x |-> (1 - sqrt(1 - 4x)) / (2 x)
$
On sait que $x |-> sqrt(1 - 4x)$ est DSE sur $Ioo(-1/4, 1/4)$ :
$
  sqrt(1 - 4x) = 1 + sum_(n = 1)^(+oo) b_n x^n
$
D'où
$
f(x) = - sum_(n = 1)^(+oo) b_n / 2 x^(n-1) = sum_(n = 0)^(+oo) c_n x^n
$
Or $x f(x)^2 - f(x) + 1 = 0$, donc par unicité du DSE
$
  c_n = sum_(k = 0)^(n-1) c_k c_(n - k) \
  c_0 = 1
$
Donc $c_n = C_n$ et $R = 1/4$.

On peut ensuite calculer $c_n$ à partire du DSE de $sqrt(1 + x)$.

#card("compdse", "Composée du développement en série entière", ("Maths.Analyse.Séries entières",))

Composée du développement en série entière.

#answer

Soient
$
  f : func(DD(0, R), CC, z, sum_(n = 0)^(+oo) a_n z^n) \
  g : func(DD(0, R'), CC, z, sum_(n = 0)^(+oo) b_n z^n) \
  g(0) = 0
$
Alors $f compose g$ est DSE en $0$ pour un rayon de convergence $r > 0$.

*Démonstration*

Pour tout $z in DD(0, R)$, $sum abs(b_n z^n)$ converge et
$
  g_0 : func(Ico(0, R'), RR, x, sum_(n = 0)^(+oo) abs(b_n) x^n)
$
Est continue et $g_0 (0) = 0$. 

Donc on dispose de $r > 0$ tel que $g_0 ([0, r]) subset.eq Ico(0,R)$.

Ainsi pour tout $z in DD(0, r)$, $g(z) in DD(0, R)$ et
$
  f(g(z)) = sum_(n = 0)^(+oo) a_n (sum_(k = 0)^(+oo) b_k z^k)^n
$
Par produit de Cauchy
$
  (sum_(k = 0)^(+oo) b_k z^k)^n = sum_(k = 0)^(+oo) c_(k,n) z^k \
  c_(k,n) = sum_(i_1, dots, i_n \ sum_(j = 1)^n i_j = k) product_(j = 1)^n b_i_j
$
Or
$
  abs(c_(k,n)) <= sum_(i_1, dots, i_n \ sum_(j = 1)^n i_j = k) product_(j = 1)^n abs(b_i_j)
$
Donc
$
  sum_(k = 0)^(+oo) abs(c_(k,n)) dot abs(z^k) <= (underbrace(sum_(k = 0)^(+oo) abs(b_k) dot abs(z^k), alpha in Ico(0, R)))^n
$
Et donc pour tout $z in DD(0, r)$
$
  & sum_(n = 0)^(+oo) sum_(k = 0)^(+oo) abs(a_n c_(k,n)) dot abs(z^k) \
  =& sum_(n = 0)^(+oo) abs(a_n) (sum_(k = 0)^(+oo) abs(c_(k,n)) dot abs(z^k)) \
  =& sum_(n = 0)^(+oo) abs(a_n) alpha^n
$
Qui converge, et donc par Fubini
$
  f(g(z)) &= sum_(n = 0)^(+oo) a_n sum(k = 0)^(+oo) c_(k,n) z^k \
  &= sum_(k = 0)^(+oo) (sum_(n = 0)^(+oo) a_n c_(k,n)) z^k
$
Donc $f compose g$ est bien DSE.

#card("fekete", "Suites sous-additive et lemme de Fekète", ("Maths.Analyse.Suites Réelles",))

Soit $(a_n)_n in RR^NN$ sous-additive :
$
  forall n, m in NN, a_(n + m) <= a_n + a_m
$
Montrer que 
$
lim_(n -> oo) a_n / n &= inf {a_k / k, k in NN^*} \ &= alpha in RR union {-oo}
$

#answer

Soit $epsilon > 0$, on pose
$
  A = cases(space 0 "si" alpha = -oo, space alpha + epsilon "sinon")
$
Par caractérisation de la borne inférieur, on dispose de $q in NN^*$ tel que
$
  a_q / q < A - epsilon / 2
$
Pour $n >= q$ on fait la division euclidienne de $n$ par $q$ : 
$
n = k_n q + r_n
$
Et ainsi
$
  a_n <= a_(k_n q) + a_r_n <= k_n a_q + a_r_n \
$
$
  a_n / n &<= k_n / n a_q +  a_r_n / n \
  &= a_q / q + underbrace((-(r_n a_q) / q + a_r_n), "bornée par" M "car" r_n in [|0, q-1|]) 1 / n
$
Donc pour $n >= N$ avec $N$ assez grand
$
  M / n <= epsilon / 2 \
  alpha <= a_n / n <= A - epsilon / 2 + epsilon / 2 = A
$

#card("exinttnpol", "Exercice : integrale nulle sur un ségment du produit d'une fonction continue avec une puissance", ("Maths.Exercice.Intégration",))

Deux exercices à ne pas confondre :

Soit $f in C^0 ([a, b], RR)$

+ Pour tout $n in NN$ #h(1fr)
  $
    integral_a^b f(t) t^n dif t = 0
  $
  Montrer que $f = 0$

+ Pour tout $n in [|0, d|]$
  $
    integral_a^b f(t) t^n dif t = 0
  $
  Montrer que $f$ s'annule en $d+1$ points.

#answer

Par linéarité de l'intégrale on a

+ Pour tout $P in RR[X]$ #h(1fr)
  $
    integral_a^b f(t) P(t) dif t = 0
  $

  On dispose de $(P_n)_n in RR[X]^NN$ tel que
  $
    norm(f - P_n)_(oo,[a,b]) tends(n -> oo) 0
  $
  Or pour tout $t in [a, b]$
  $
    &abs(f^2(t) - P_n (t) f(t)) \ =& abs(f(t)) abs(P_n(t) - f(t)) \
    <=& norm(f)_oo norm(f - P_n)_oo
  $
  D'où
  $
    norm(f^2 - P_n f)_oo tends(n -> oo) 0
  $
  Et par CVU sur $[a, b]$
  $
    integral_a^b f^2(t) dif t = lim_(n -> oo) integral_a^b P_n (t) dif t = 0
  $
  Donc $f^2 = 0 = f$.

+ Pour tout $P in RR_d [X]$
  $
    integral_a^b f(t) P(t) dif t = 0
  $

  Par l'aburde supposons que
  $
    abs(f^(-1) {0}) <= d
  $
  Soient $a_1 < dots.c < a_q$ les points où $f$ s'annule en changeant de signe ($0 <= q <= d$).
  $
    P(X) = product_(j = 1)^q (X - a_j) in RR_d [X]
  $
  Et $t |-> f(t)P(t)$ s'annule en au plus $d$ points et ne change pas de signe. Or
  $
    integral_a^b f(t) P(t) dif t = 0
  $
  Donc $f P = 0$ et $f$ est presque nulle, absurde.

#card("ex63dse", "Exercice : CNS de DSE en bornant les dérivées successives", ("Maths.Exercice.Séries entières",))

Soit $f in C^oo (Ioo(-delta, delta), RR)$, montrer que $f$ est DSE en $0$ ssi
$
  exists a, M in RR^*_+, V in cal(V)(0), \ forall x in V, n in NN, \
  abs(f^(n) (x)) <= M a^n n!
$

#answer

*Sens indirecte*

On dispose de $a, M$ et $V$ comme énoncé, pour tout $x in V$ on a
$
  & abs(f(x) - sum_(k = 0)^n f^((k)) (0) / k! x^k) \ <=& sup_V abs(f^((n+1))) dot abs(x^(n+1)) / (n+1)! \ 
  <=& M abs(a x)^(n+1)
$
Soit $eta > 0$ tel que $a eta < 1$ et $Ioo(-eta, eta) subset.eq V$.

Pour tout $x in Ioo(-eta, eta)$
$
  abs(f(x) - sum_(k = 0)^n f^((k)) (0) / k! x^k) &<= M abs(a eta)^n+1 \
  &tends(n -> oo) 0
$
D'où
$
  f(x) = sum_(k = 0)^(+oo) f^((k)) (0) / k! x^k
$
Avec convergence de la série.

*Sens directe*

On suppose que pour tout $x in Ioo(-eta, eta)$
$
  f(x) = sum_(k = 0)^(+oo) b_k x^k \
  f^((n)) (x) = sum_(k = n)^(+oo) b_k k! / (k - n)! x^(k - n)
$

Or la suite $(b_k (eta / 2)^k)_(k in NN)$ est bornée par $M$.

Ainsi pour tout $k in NN$, $abs(b_k) <= M (2 / eta)^k$.
$
  abs(f^((k))(x)) &<= M sum_(k = n)^(+oo) k! (k - n)! (2 / eta)^k abs(x)^(k - n) \
  &<= M (2 / eta)^n sum_(k = n)^(+oo) k! / (k - n)! abs((2 x) / eta)^(k - n)
$
Or pour $y in Ioo(-1, 1)$
$
  sum_(k = n)^(+oo) k! (k - n)! y^(k - n) = g^((n))(y) \
  g(y) = 1 / (1 - y) \
  g^((n)) (y) = n! / (1 - y)^(n + 1)
$
D'où pour tout $n in NN$, $x in Ioo(-eta / 2, eta/2)$
$
  abs(f^((n))(x)) <= M (2 / eta)^n n! / (1 - (2 abs(x)) / eta)^(n+1)
$
Ainsi pour tout $x in Ioo(-eta / 4, eta / 4)$
$ 
  (2 abs(x)) / eta < 1/2
$
Donc pour tout $n in NN$
$
  abs(f^((n))(x)) <= (2 M) n! (4 / eta)^n
$
]
