#import "../cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/cetz:0.4.2"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

#card("derselvec", "Derivée selon un vecteur", ("Maths.Analyse.Calcul différentiel",))

Derivée selon un vecteur.

#answer

Soit $f in cal(F)(Omega, F)$ où $Omega subset.eq E$ ouvert dans un $RR$-ev de dimension finie.

Soit $a in Omega$ et $u in E$, on dispose de $delta > 0$ tel que pour tout $t in Ioo(-delta, delta)$, $a + t v in Omega$.

On dit que $f$ admet une dérivée selon un vecteur $v$ en $a$ si
$
  phi_(v,a) : func(Ioo(-delta, delta), F, t, f(a + t v))
$
Est dérivable en $0$. Dans ce cas on note
$
  D_v f (a) &= phi'_(v, a) (0)  \
  &= lim_(t -> 0) (f(a + t v) - f(a)) /t
$

#card("derpart", "Dérivées partielles", ("Maths.Analyse.Calcul différentiel",))

Dérivées partielles.

#answer

On se fixe $e = (e_1, dots, e_n)$ une base de $E$ ($RR$-ev de dimension finie). On prend la base canonique si $E = RR^n$.

Si elle existe, on appelle la $j^e$ dérivée partielle de $f$ en $a in E$ la dérivée selon $e_j$ de $f : Omega -> F$ où $Omega subset.eq E$ ouvert.

$
  pdv(f, x_j) (a) &= partial_j f (a) = D_(e_j) f (a) \
  &= lim_(t -> 0) (f(a + t e_j) - f(a))/ t
$

Dans le cas où $E = RR^n$
$
  f(x) = f(x_1, dots, x_n) \
  phi_(a, e_j) : t |-> f(a + t e_j) \
  g_j : x_j |-> f(a_1, dots, x_j, dots, a_n)
$
La $j^e$ dérivée partielle existe si $phi_(a, e_j)$ est dérivable en $0$, ou si $g_j$ est dérivable en $a_j$, et dans ce cas
$
  diff_j (f) = pdv(f, x_j) (a) = phi'_(a, e_j) (a) = g'_j (a_j)
$

*Cela ne suffit pas à généraliser la dérivabilité*

On considère
$
  f : func(RR^2, RR, (x, y) != (0, 0), (x y) / (x^2 + y^2), (0, 0), 0)
$
Sur $RR^2 \\ {(0, 0)}$, $f$ admet évidemment des dérivées partielles.

En $(0, 0)$
$
x |-> f(x, 0) = 0 \
y |-> f(0, y) = 0 \
$
D'où $pdv(f, x) (0, 0)$ existe et est nulle. De même en $y$.

Mais $f$ n'est même pas $C^0$ en $(0, 0)$
$
  f(t, t) = t^2 / (2 t^2) = 1/2 tendsnot(t -> 0) 0
$

#card("différentiabilité", "Différentiabilité", ("Maths.Analyse.Calcul différentiel",))

Différentiabilité.

#answer

Soit $f : Omega -> F$ où $Omega subset.eq E$ ouvert.
Soit $a in Omega$ et $r > 0$ tel que $B(a, r) subset.eq Omega$.

On dit que $f$ est différentiable en $a$ si il existe $phi in cal(L)(E, F)$ et $epsilon : B(0, r) -> F$ tel que
$
  forall h in B_E (0, r), \
  f(a + h) = f(a) + phi(h) + norm(h) epsilon(h) \
  epsilon(h) tends(h -> 0) 0
$

Dans le cas où $E = RR$ et $Omega = I$, $f$ est différentiable en $a$ ssi $f$ est dérivable en $a$ et $phi : h |-> f'(a) h$.

*Propriétés*

- Si $f$ est différentiable en $a$, alors $f$ est continue en $a$

- Si $f$ est différentiable en $a$, alors $f$ admet une dérivée selon tout vecteur en $a$.

  Et pour tout $v in E$, $D_v f (a) = phi(v)$.

- L'application $phi$ est unique, est appelée différentiel de $f$ en $a$ et est notée $dif f (a)$.
  
  On note de plus alternativement $dif f (a) (h) = dif f (a). h$.

- Si $f$ est constante sur $Omega$, alors $f$ est différentiable sur $Omega$ et pour tout $a in Omega$, $dif f (a) = 0$.

- Si $f = phi|_Omega$ pour $phi in cal(L)(E, F)$, alors $f$ est différentiable sur $Omega$ et pour tout $a in Omega$, $dif f (a) = phi$.

*Démonstration*

- On suppose que $f$ est différentiable en $a$
  $
    lim_(h -> 0) f(a + h) =& f(a) + underbrace(lim(h -> 0) phi(h), 0) \ +& underbrace(lim_(h - > 0) norm(h) epsilon(h), 0) \
    =& f(a)
  $

- Calcul de limite.

#card("derlelongdunchemin", "Dérivée le long d'un chemin", ("Maths.Analyse.Calcul différentiel",))

Dérivée le long d'un chemin.

#answer

Soit $f : Omega -> F$ où $Omega subset.eq E$ ouvert. Soit $gamma : I -> E$ où $I$ est un intervalle et $gamma(I) subset.eq Omega$.

On suppose que $gamma$ est dérivable en $t_0 in I$ et $f$ est différentiable en $a = gamma(t_0)$.

Alors $f compose gamma$ est dérivable en $t_0$ et
$
  (f compose gamma)' (t_0) = dif f (gamma (t_0)) compose gamma' (t_0)
$

*Intégrale*

Si de plus $f$ et $gamma$ sont $C^1$ (sur $Omega$ et $[0, 1]$ respectivement), alors $f compose gamma$ est $C^1$ et

$
  f(gamma(1)) - f(gamma(0)) &= integral_0^1 (f compose gamma)' (t) dif t \
  &= integral_0^1 dif f (gamma(t)).gamma'(t) dif t
$

On en déduit que si $f in C^1 (Omega, F)$ où $Omega$ est un ouvert connexe par arcs, $f$ est constante ssi pour tout $a in Omega, dif f (a) = 0$.

*Démonstration*

Par continuité de $gamma$ en $t_0$, on dispose de $V$ voisinage de $t_0$ tel que $gamma(V) subset.eq B(a, r)$.

Soit $h > 0$

$
  &f(gamma(t_0 + h)) - f(gamma(t_0)) \
  =& f(a + gamma(t_0 + h) - gamma(t_0)) - f(a) \
  =& dif f (a).(gamma(t_0 + h) - gamma(t_0)) \ 
  +& norm(gamma(t_0 + h) - gamma(t_0)) epsilon(gamma(t_0 + h) - gamma(t_0))
$
Ainsi pour tout $h > 0$
$
  &(f(gamma(t_0 + h)) - f(gamma(t_0))) / h \
  =& dif f (a).((gamma(t_0 + h) - gamma(t_0)) / h) \
  +& underbrace(norm((gamma(t_0 + h) - gamma(t_0)) / h), tends(h -> 0) norm(gamma'(t_0))) epsilon(underbrace(gamma(t_0 + h) - gamma(t_0), tends(h -> 0) 0))
$
Donc à la limite
$
  (f compose gamma)' (t_0) = dif f (a). gamma'(t_0)
$

Pour le lien entre $f$ constante et $dif f = 0$, on ne peut pas simplement considérer un chemin $gamma$ $C^1$, car la connexité par arcs ne nous assure pas son existence (ici il en existe bien un car $Omega$ est ouvert).

On considère plutot, pour un $b in Omega$ quelconque
$
  Gamma = f^(-1) {f(b)}
$
Qui est fermé dans $Omega$.

On montre (par les boules) que $Gamma$ est ouvert dans $Omega$.

Or comme connexe par arcs implique connexe, $Gamma in {Omega, emptyset}$, or $b in Gamma$, donc $Gamma = Omega$.

#card("diffeetbases", "Différentiabilité et bases", ("Maths.Analyse.Calcul différentiel",))

Différentiabilité et bases.

#answer

Soit $f : Omega -> F$, où $Omega subset.eq E$ ouvert $(e_1, dots, e_n)$ base de $E$ et $(omega_1, dots, omega_p)$ base de $F$.

Quelques propriétés :

- Notation : si $f$ est différentiable en $a in Omega$

  On pose
  $
    forall k in [|1, n|], \ dif x_k : func(E, RR, h = sum_(j = 1)^n h_j e_j, h_k)
  $
  Et ainsi
  $
    dif f (a) = sum_(k = 1)^n pdv(f, x_k) dif x_k
  $

- Si on décompose $f$
  $
    f : x |-> sum_(k = 1)^p f_k (x) omega_k
  $

  Alors $f$ est différentiable en $a in Omega$ ssi pour tout $k in [|1, p|]$, $f_k$ est différentiable en $a$.

  Et dans ce cas
  $
    dif f (a) : h |-> sum_(k = 1)^p (dif f_k (a).h) omega_k
  $

#card("matrjaco", "Matrice Jacobienne", ("Maths.Analyse.Calcul différentiel",))

Matrice Jacobienne.

#answer

Soit $f : Omega -> RR^n$ où $Omega subset.eq RR^p$ ouvert.

Si $f$ est différentiable en $a in Omega$, on définit la matrice Jacobienne de $f$ en $a$ comme

$
  f : vec(x_1, dots.v, x_p) |-> vec(f_1(x_1, dots, x_p), dots.v, f_n (x_1, dots, x_p)) \ \

  J(f) (a) = mat(pdv(f_1, x_1), dots.c, pdv(f_1, x_n); dots.v, dots.down, dots.v; pdv(f_n, x_1), dots.c, pdv(f_n, x_n)) (a) in M_(n p) (RR)
$

#card("gradicd", "Gradient", ("Maths.Analyse.Calcul différentiel",))

Gradient.

#answer

Soit $f : Omega -> RR$ où $Omega subset.eq E$ ouvert dans un espace euclidien.

On suppose $f$ différentiable en $a in Omega$.

Par théorème de représentation, on dispose d'un unique vecteur $omega in E$ tel que pour tout $h in E$
$
  dif f (a).h = scl(omega, h)
$

On appelle $omega$ le gradient de $f$ en $a$ et on le note
$
  omega = grad f (a)
$

- Si $E = RR^p$ muni du produit scalaire canonique #h(1fr)
  $
    grad f(a) = vec(pdv(f, x_1) (a), dots.v, pdv(f, x_p) (a)) = J(f) (a)^TT
  $

- Si $dif f(a) != 0$
  $
    func(SS_E (0, 1), RR, u, dif f(a).u)
  $
  Est maximale en
  $
    (grad f (a)) / norm(grad f (a))
  $
  (Démonstration par Cauchy-Schwarz).

#card("opdif", "Opération sur les différentielles", ("Maths.Analyse.Calcul différentiel",))

Opération sur les différentielles.

#answer

- Si $f, g in cal(F)(Omega, F)$ et $f, g$ sont différentiables en $a in Omega$, alors pour tout $alpha, beta in RR$, $alpha f + beta g$ est différentiable en $a$ et #h(1fr)
  $
    dif (alpha f + beta g) (a) = alpha dif f (a) + beta dif g (b)
  $

- Soient $(f_1, dots, f_d) in product_(i = 1)^d cal(F)(Omega, F_i)$ et $M : F_1 times dots.c, F_d -> G$ est $d$-linéaire.

  Si $f_1, dots, f_d$ sont différentiables en $a in Omega$, alors
  $
    g : func(Omega, G, x, M(f_1 (x), dots, f_d (x)))
  $
  Est différentiable en $a$ et
  $
    dif g (a) : h |-> sum_(i = 1)^d script(M(f_1 (a), dots, dif f_i (a).h, dots, f_d (a)))
  $

- Soit $g : Omega -> F, f : W -> G$ où $Omega subset.eq E$ ouvert, $W subset.eq F$ ouvert, $g(Omega) subset.eq W$.

  Si $g$ est différentiable en $a in Omega$ et $f$ est différentiable en $b = g(a)$, alors $f compose g$ est différentiable en $a$ et 
  $
    dif (f compose g) (a) = dif f (g(a)) compose dif g (a)
  $

//NOTE: M384 Différentiabilité et normes

#card("formchaine", "Formule de la chaîne", ("Maths.Analyse.Calcul différentiel",))

Formule de la chaîne.

#answer

Soit $g : Omega -> F, f : W -> G$ où $Omega subset.eq E$ ouvert, $W subset.eq F$ ouvert, $g(Omega) subset.eq W$.

On fixe des bases de $E$, $F$ et $G$, et on se ramène au cas $E = RR^p, F = RR^n, G = RR^q$.

Si $g$ est différentiable en $a$ et $f$ est différentiable en $b = g(a)$, alors $f compose g$ est différentiable en $a$ et pour tout $j in [|1, p|]$ et $i in [|1, q|]$
$
  pdv(f compose g, x_j) = sum_(k = 1)^n pdv(f_i, u_k) (g(a)) pdv(g, x_j) (a)
$

*Exemple : changement polaire*

On considère
$
  phi : func(RR^2, RR^2, (r, theta), (r cos theta, r sin theta))
$

Et $f : W -> RR$ différentiable. On prend $Omega subset.eq RR^2$ tel que $phi(Omega) subset.eq W$ et on note $tilde(f) = f compose phi$.

Comme $f$ est $phi$ sont différentiables, $tilde(f)$ l'est aussi sur $Omega$ et
$
  pdv(tilde(f), r) (r, theta) &= pdv(f, x) (r cos theta, r sin theta) pdv(x, r) (r, theta) \
  &+ pdv(f, y) (r cos theta, r sin theta) pdv(y, r) (r, theta) \
  &= cos theta pdv(f, x) (r cos theta, r sin theta) \
  &+ sin theta pdv(f, y) (r cos theta, r sin theta)
$

De même
$
  pdv(tilde(f), theta) (r, theta) &= -r sin theta pdv(f, x) (r cos theta, r sin theta) \
  &+ r cos theta pdv(f, y) (r cos theta, r sin theta)
$

Si de plus $phi : Omega -> W$ est une bijection
$
  phi^(-1) : func(W, Omega, (x, y), vec(sqrt(x^2 + y^2), 2 arctan(y / (x + sqrt(x^2 + y^2)))))
$

On peut écrire $f = tilde(f) compose phi^(-1)$, mais on a aucune envie de calculer $pdv(theta, x)$ et $pdv(theta, y)$.

D'après ci dessus
$
  vec(pdv(tilde(f), r) (r, theta), pdv(tilde(f), theta) (r, theta)) \ = underbrace(mat(cos theta, sin theta; -r sin theta, r cos theta), J(phi)(r, theta)^TT) vec(pdv(f, x)(script(r cos theta\, r sin theta)), pdv(f, y)(script(r cos theta\, r sin theta)))
$

Or $det J(phi)(r, theta) = r != 0$, d'où
$
    vec(pdv(f, x)(script(r cos theta\, r sin theta)), pdv(f, y)(script(r cos theta\, r sin theta)))\ = underbrace(1/r mat(r cos theta, -sin theta; r sin theta, cos theta), (J(phi)(r, theta)^TT)^(-1)) vec(pdv(tilde(f), r) (r, theta), pdv(tilde(f), theta) (r, theta))
$

Et ainsi
$
  pdv(f, x) (r cos theta, r sin theta) &= cos theta pdv(tilde(f), r) (r, theta) \ &- (sin theta) / r pdv(tilde(f), theta) (r, theta) \
  pdv(f, y) (r cos theta, r sin theta) &= sin theta pdv(tilde(f), r) (r, theta) \ &+ (cos theta) / r pdv(tilde(f), theta) (r, theta) \
$

// NOTE: M385 ???

#card("clasdiff", "Classe de différentiabilité", ("Maths.Analyse.Calcul différentiel",))

Classe de différentiabilité ($C^1$). 

#answer

Soit $f : Omega -> F$. On dit que $f$ est $C^1$ sur $Omega$ si $f$ est différentiable sur $Omega$ et
$
  func(Omega, cal(L)(E, F), a, dif f (a))
$
Est continue.

*Propriétés*

Comme $cal(L)(E, F)$ est de dimension finie, donc $dif f$ est continue sur toute ses coordonnées.

- Soit $(e_1, dots, e_p)$ base de $E$ et $(w_1, dots, w_n)$ base de $F$.

  Alors $f$ est $C^1$ sur $Omega$ ssi $f$ est différentiable sur $Omega$ et pour tout $i in [|1, n|], j in [|1, p|]$, $pdv(f_i, x_j)$ est continue sur $Omega$.

- On peut d'ailleurs montrer que $f$ est $C^1$ ssi toutes ses dérivées partielles existent et sont $C^1$ sur $Omega$.

*Opérations*

- Toutes combinaison linéaire de fonctions $C^1$ est $C^1$.

- Toute forme $d$-linéaire évalué en $d$ fonctions $C^1$ est $C^1$.

- Toute composée de fonctions $C^1$ est $C^1$.

- Toute application linéaire est $C^1$.

- Toute application polynomiale en les coordonnées est $C^1$.

*Démonstration*

On découpe le chemin sur les coordonnées, puis on fait du calcul pas très beau avec l'EAF.

// NOTE: Démonstration M387-388, j'ai pas le courage là

#card("exediffclas", "Exercice : différentiel du determinant et de l'inverse", ("Maths.Exercice.Calcul différentiel",))

Montrer que $det$ est $C^1$, puis donner sa différentielle.

En déduire que l'inverse est $C^1$ et donner sa différentielle en $I_n$.

#answer

Comme
$
  det : func(M_n (RR), RR, A, det A)
$
Est polynomiale en les coordonnées, $det$ est $C^1$.

On fixe $(E_(i j))_(i j)$ la base canonique de $M_n (RR)$. On veut calculer $pdv(det, x_(i j)) (A)$.

Soit $l in [|1, n|]$, on developpe selon la $l$-ème colonne
$
  det A = sum_(i = 1)^n (-1)^(i + l) a_(i l) det(A_(i l))
$
Où $A_(i l)$ est la matrice $A$ privée de sa $i$-ème ligne et $l$-ème colonne.

Soit $k in [|1, n|]$, les $det(A_(i l))$ sont tous indépendants de 
$
pdv(det, x_(k l)) (A) &= (-1)^(k + l) det(A_(k l)) \ &= ("Com"(A))_(k l)
$

Or pour tout $H in M_n (RR)$
$
  dif (det) (A). H &= sum_(k, l) pdv(det, x_(k l)) (A) H_(k l) \
  &= sum_(k, l) ("Com" (A))_(k l) H_(k l) \
  &= tr("Com" (A)^TT H)
$
Enfin
$
  dif (det) : func(M_n (RR), RR, H, tr("Com"(A)^TT H), H, scl("Com"(A), H))
$

Ainsi
$
  theta : func("GL"_n (RR), "GL"_n (RR), A, A^(-1))
$
Est $C^1$ (par la formule de l'inverse avec la commatrice) : chaque coefficient de la commatrice est $C^1$ car polynomiale en les coordonnées.

Or pour tout $A in "GL"_n (RR)$
$
  A theta(A) = I_n \
$
Donc en différentient
$
  forall H in B(0, r), space A(dif theta(A). H) + H theta(A) = 0 \
  dif theta (A). H = A^(-1) H A^(-1)
$

#card("esptange", "Espace tangent", ("Maths.Analyse.Calcul différentiel",))

Espace tangent.

#answer

Soit $E$ un $RR$-ev, $Gamma subset.eq E$, on définit l'espace tangent à $Gamma$ au point $a in Gamma$
$
  T_a Gamma = Set(v in E, cases(delim: #none, exists epsilon > 0\, gamma in D^1 (Ioo(-epsilon, epsilon)), space space gamma(0) = a quad gamma' (0) = v))
$

*Exemples*

- $E = RR^n$, $Gamma = SS(0, r)$, pour tout $x in Gamma$ #h(1fr)
  $
    T_x Gamma = x^perp
  $

- $E = RR^n$, $Gamma = overline(B(0, 1))$

  - Pour tout $x in B(0, 1)$, $T_x Gamma = RR^n$

  - Pour tout $x in SS(0, 1)$, $T_x Gamma = x^perp$

- Si $Gamma = Omega$ ouvert, alors pour tout $x in Gamma$, $T_x Gamma = E$.

- Si $Gamma = cal(H) = x_0 + H$ est un espace affine de direction $H$, alors pour tout $a in cal(H)$, $T_a cal(H) = H$.

*Démonstration*

- Soit $v in T_x (SS(0, r))$, soit $gamma$ associé.
  $
    forall t in Ioo(-epsilon, epsilon), norm(gamma(t))^2 = r^2 \
    scl(gamma(t), gamma(t)) = r^2 \
    2scl(gamma'(t), gamma(t)) = 0
  $
  Donc en $t = 0$, $scl(x, v) = 0$.

  Soit $v in x^perp \\ {0}$ (cas nulle évident).

  On construit bien le chemin et ça marche.

- La même.

- Logique.

- Soit $a in cal(H), v in T_a cal(H)$, et $gamma$ associé, pour tout $t in I = Ioo(-epsilon, epsilon)$
  $
    gamma(t) - gamma(0) = gamma(t) - a in H \
    (gamma(t) - gamma(0))/t in H
  $
  Or $H$ est fermé comme sev de dimension finie, d'où à la limite
  $
    gamma'(0) = v in H
  $

  Soit $v in H$ et $a in cal(H)$
  $
    gamma : t |-> a + t v
  $
  Convient.

#card("exesptangonsln", "Exercice : espaces tangents du groupe orthogonale et du groupe special linéaire", ("Maths.Analyse.Calcul différentiel",))

Donner

+ $T_I_n O_n (RR)$

+ $T_I_n "SL"_n (RR)$

#answer

+ Soit $A in T_I_n (RR)$, et $gamma$ associé.

  Pour tout $t in Ioo(-epsilon, epsilon)$ #h(1fr)
  $
    gamma(t)^TT gamma(t) = I_n \
    gamma'(t)^TT gamma(t) + gamma(t)^TT gamma'(t) = 0
  $
  D'où en $t = 0$
  $
    A + A^TT = 0 quad quad A in A_n (RR)
  $

  Et réciproquement pour tout $A in A_n (RR)$
  $
    gamma : func(RR, O_n (RR), t, e^(t A))
  $
  Convient.

+ Soit $A in T_I_n "SL"_n (RR)$, $gamma$ associé.

  Ainsi pour tout $t in Ioo(-epsilon, epsilon)$
  $
    (det compose gamma)'(t) = 0 \
    dif (det) (gamma (t)). gamma'(t) = 0 \
    tr("Com"(gamma(t))^TT gamma'(t)) = 0
  $
  D'où en $t = 0$
  $
    tr(A) = 0
  $
  D'où $T_I_n "SL"_n (RR) subset.eq ker tr$.

  Réciproquement, soit $A in ker tr$
  $
    gamma : func(RR, O_n (RR), t, e^(t A))
  $
  Convient.

// TODO: Exo M393 

#card("esptanggraphfun", "Espace tangent du graphe d'une fonction", ("Maths.Analyse.Calcul différentiel",))

Espace tangent du graphe d'une fonction.

#answer

Soit $Omega subset.eq RR^2$ et $f in C^1 (Omega, RR)$. On pose
$
  Gamma = { (x, y, f(x, y)), (x, y) in Omega }
$

Soit $m = (a, b, f(a, b)) in Gamma$ et $v in T_m Gamma$.

Ainsi on dispose de $gamma$ associé.

Pour tout $t in I = Ioo(-epsilon, epsilon)$
$
  gamma(t) = vec(gamma_1 (t), gamma_2 (t), gamma_3 (t)) \
  gamma_3 (t) = f(gamma_1 (t), gamma_2 (t)) \
$
$
  gamma'_3 (t) &= dif f(gamma_1 (t), gamma_2 (t)). (gamma'_1 (t), gamma'_2 (t)) \
  &= pdv(f, x) (gamma_1 (t), gamma_2 (t)) gamma'_1 (t) \
  &+ pdv(f, y) (gamma_1 (t), gamma_2 (t)) gamma'_2 (t)
$
Donc en $t = 0$
$
  v = vec(v_1, v_2, v_3) \
  v_3 = gamma'_3 (0) \
  (E) quad v_3 = pdv(f, x) (a ,b) v_1 + pdv(f, y) (a, b) v_2
$

Ainsi $T_m Gamma subset.eq H$ hyperplan d'équation $(E)$.

Réciproquement, soit $vec(v_1, v_2, v_3) in H$. Comme $Omega$ est ouvert, on dispose de $r > 0$ tel que $B_oo ((a, b), r) subset.eq Omega$.

Soit $delta > 0$ tel que $delta norm(v_2) < r$ et $delta norm(v_1) < r$

On pose
$
  gamma : func(Ioo(-delta, delta), RR^3, t, vec(a + t v_1, b + t v_2, f(a + t v_1, b + t v_2)))
$
Qui convient.

#card("lignesdeniveau", "Lignes de niveau", ("Maths.Analyse.Calcul différentiel",))

Lignes de niveau.

#answer

Soit $Omega$ ouvert de $E$, $f in C^1 (Omega, F)$ et $alpha in f(Omega)$

On note la ligne de niveau
$
  Gamma = f^(-1) {alpha}
$
Pour tout $a in Gamma$, si $dif f(a) != 0$, alors 
$
T_a Gamma = ker dif f (A)
$

// TODO: Démonstration M394-395

#card("rechextr", "Recherche d'extremum au première ordre", ("Maths.Analyse.Calcul différentiel",))

Recherche d'extremum au première ordre.

#answer

Soit $f : Omega -> RR$, où $Omega subset.eq E$ ouvert.

Si $f$ admet un extremum local en $a in Omega$ et $f$ est différentiable en $a$, alors
$
  dif f(a) = 0
$

*Pour une restriction*

Soit $f: Omega -> RR$ différentiable en $a in Omega$.

Soit $Gamma subset.eq Omega$, si $f|_Gamma$ admet un extremum en $a$ alors pour tout $v in T_a Gamma$
$
  dif f (a).v = 0
$

*Optimisation sous contrainte*

Soient $f, g in C^1 (Omega, RR)$. On note $Gamma = g^(-1) { alpha }$ pour $alpha in g(Omega)$.

On suppose que $f|_Gamma$ admet un extremum en $a in Gamma$ et $dif g (a) != 0$.

Alors on dispose de $lambda in RR$
$
  dif f(a) = lambda dif g(a)
$

*Démonstration*

- On a le resultat pour les dérivée selon tout les vecteurs.

- Soit $v in T_a Gamma$ et $gamma$ associé. Ainsi $f compose gamma$ admet un extremum en $t = 0$. #h(1fr)

  Ainsi
  $
    (f compose gamma)'(0) = 0 =dif f(gamma(0)).gamma'(0) \
    dif f (a).v = 0
  $

- Comme $T_a Gamma = ker dif g (a)$ et $f|_Gamma$ admet un extremum en $a$
  $
    ker dif g (a) subset.eq ker dif f (a)
  $
  Qui sont deux formes linéaires, et sont donc liées.

// NOTE: Autre démonstration du théorème spectrale M397 et le truc du début M398

#card("exsurjparinjdedif", "Exercice : surjectivité d'une fonction dont la différentielle est injective", ("Maths.Exercice.Calcul différentiel",))

Soit $f : RR^n -> RR^n$ différentiable tel que pour tout $x in RR^n$, $dif f (x)$ est injective et $norm(f(x)) tends(norm(x) -> oo) oo$.

Montrer que $f$ est surjective.

#answer

Soit $a in RR^n$, on pose
$
  g : func(RR^n, RR^n, x, norm(f(x) - a)^2)
$

Pour tout $x in RR^n$
$
  norm(f(x) - a) >= norm(f(x)) - norm(a) tends(norm(x) -> oo) oo
$
D'où $g(x) tends(norm(x) -> oo) oo$.

Soit $R > 0$ tel que pour tout $norm(x) > R$
$
  g(x) >= g(0)
$

Ainsi
$
  inf_(x in RR^n) g(x) = inf_(x in B(0, R)) g(x)
$

Or $g$ est continue sur le compact $overline(B(0, R))$, donc cet $inf$ est atteint en $x_0$ et $dif g(x_0) = 0$.

Or pour tout $h in RR^n$
$
  0 &= dif g (x_0).h \ &= 2 scl(dif f (x_0).h, f(x_0) - a)
$
Donc pour tout $v in RR^n$, avec $h = dif f (x_0)^(-1) (v)$
$
  0 = scl(v, f(x_0) - a)
$
Donc $f(x_0) - a = 0$ et $f$ est surjective.

#card("derpartordsup", "Dérivées partielles d'ordres supérieurs", ("Maths.Analyse.Calcul différentiel",))

Dérivées partielles d'ordres supérieurs.

#answer

On ne définit (pas dans le cadre du programme) pas les différentielles d'ordres supérieurs.

On dit que $f in C^1 (Omega, F)$ est de classe $C^k$ si toutes les dérivées partielles d'ordre $k$ existent et sont $C^0$.

Il faut la continuité selon toute les variables : pour montrer l'éxistence on fixe les variables, mais pour montrer la continuité elles ne peuvent rester fixes.

*Théorème de Schwarz*

Pour une fonction $C^k$, l'ordre des dérivée partielles n'importe pas.

On le montre pour intervertir deux dérivée partielles (qui suffit pour toute les permutations), et pour les fonctions à valeur dans $RR$ car on peut decomposer $f$ sur une base.

On calcul la dérivée de deux manières en passant par des chemin différents ($h_1$ puis $h_2$, et $h_2$ puis $h_1$) + EAF.

#card("hessienne", "Matrice Hessienne", ("Maths.Analyse.Calcul différentiel",))

Matrice Hessienne.

#answer

Soit $f in C^2(Omega, RR)$ et $e = (e_1, dots, e_n)$ base de $E$.

On définit pour $a in Omega$ la matrice Hessienne de $f$ en $a$ comme
$
  H(f)(a) &= (pdv(f, x_i, x_j) (a))_(i, j in [|1, n|]) \
  &in M_n (RR) \
  &in S_n (RR) quad "(Par Schwarz)" \ 
$

Et ainsi si $r > 0$ tel que $B(a, r) subset.eq Omega$.

Pour tout $h in B(0,r)$
$
  f(a + h) - f(a) \
  = dif f (a).h + 1/2 h^TT H(f)(a) h + o(norm(h)^2) \
$
Et si $E$ est euclidien
$
  f(a + h) - f(a) &= scl(grad f (a), h) \ &+ 1/2 scl(H(f)(a) h, h) \ &+ o(norm(h)^2)
$

*Démonstration*

On note $H(a) = H(f)(a)$.

On utilise Taylor reste intégrale :

Pour tout $h in B(0, r)$, on pose
$
  gamma_h : func([0, 1], Omega, t, a + t h)
$
Ainsi
$
  &f(a + h) - f(a) \
  =& f compose gamma_h (1) - f compose gamma_h (0) \
  =& (f compose gamma_h)' (0) + integral_0^1 (1 - t) (f compose gamma_h)''(t) dif t \
$
Or
$
  (f compose gamma_h)' : t |->& dif f(gamma_h (t)).gamma'_h(t) \
  =& dif f(a + t h).h \
  =& sum_(j = 1)^n pdv(f, x_j) (a + t h) h_j
$
Ainsi
$
  (f compose gamma_h)'' : t |->& sum_(j = 1)^n sum_(k = 1)^n pdv(f, x_k, x_j) (a + t h) h_k h_j
$

On peut maintenant écrire
$
  f(a + h) - f(a) \
  = dif f(a).h + integral_0^1 (1 - t) h^TT H(a + t h) h dif t \
$
Ainsi
$
  &Delta (h) \
  =& f(a + h) -(script(f(a) + dif f(a).h + 1/2 h^TT H(a) h)) \
  =& integral_0^1 (1 - t) h^TT [H(a + t h) - H(a)] h dif t
$
Soit $epsilon > 0$ et $delta > 0$ tel que pour tout $norm(x) < delta$, qui existe par continuité.
$
  norm(H(a + x) - H(a))_"op" < epsilon
$

D'où pour $norm(h) < delta$
$
  norm(Delta(h)) \
  <= integral_0^t (1 - t) norm(h) norm((H(a + t h) - H(a)) h) dif t \
  <= integral_0^t (1 - t) norm(h)^2 norm(H(a + t h) - H(a))_"op" dif t \
  <= epsilon / 2 norm(h)^2
$

#card("rechextr2", "Recherche d'extremum au deuxième ordre", ("Maths.Analyse.Calcul différentiel",))

Recherche d'extremum au deuxième ordre.

#answer

Soit $f in C^2 (Omega, RR)$.

*Condition nécéssaire*

Si $f$ admet un minimum en $a in Omega$, alors
$
  dif f (a) = 0 \
  H(f) (a) in S_n^+ (RR)
$
Et comme $laplace f (a) = tr H(f)(a)$
$
  dif f (a) = 0 \
  laplace f (a) >= 0
$

*Condition suffisante*

Si $f$ admet un point critique en $a in Omega$ et $H(f)(a) in S_n^(++) (RR)$, alors $f$ admet un minmum local strict en $a$.

*Application*

Pour $Omega subset.eq RR^2$, soit $a in Omega$ tel que $dif f (a) = 0$.

On considère
$
  H(f)(a) = mat(pdv(f, x, 2) (a), pdv(f, x, y) (a); pdv(f, x, y) (a), pdv(f, y, 2) (a))
$

On note $lambda_1 <= lambda_2$ les valeurs propres de $H(f)(a)$ réelles.

- Si $det H(f)(a) > 0$, alors $lambda_1 lambda_2 > 0$ :

  Si $pdv(f, x, 2) (a) > 0$, alors comme $det > 0$, $lambda_1, lambda_2 > 0$.

  Ainsi $H(f)(a) in S_n^(++) (RR)$ et $a$ est un minimum local strict (et inversement si $pdv(f, x, 2) < 0$).

- Si $det H(f)(a) < 0$, alors $lambda_1 < 0 < lambda_2$.

  Comme $H(f)(a) in.not S_n^+ (RR)$ et $H(f)(a) in.not S_n^- (RR)$, $a$ n'est ni un maximum ni un minimum.

  C'est un point selle.

  Si $(e_1, e_2)$ BON de vecteurs propres de $H(f)(a)$ ($h = h_1 e_1 + h_2 e_2$),
  $
    f(a + h) - f(a) \ = underbrace(lambda_1, < 0) h_1^2 + underbrace(lambda_2, > 0) h_2^2 + o(h_1^2 + h_2^2)
  $

- Si $det H(f)(a) = 0$ on ne peut rien dire.

*Démonstration*

- On pose pour $h in RR^n$ #h(1fr)
  $
    g = f compose gamma : func(Ioo(-delta, delta), RR, t, f(a + t h))
  $
  Qui admet un minimum en $0$, d'où $g''(0) >= 0$, et en calculant $(f compose gamma)''$, on relie cela à $h^TT H(f)(a) h$.

- On suppose $dif f (a) = 0$ et $H(f)(a) in S_n^(++) (RR)$.

  On note $lambda_1 <= dots.c <= lambda_n$ le spectre ordonné de $H(f)(a)$.

  Pour tout $h in B(0, r)$
  $
    f(a + h) - f(a) \ 
    = 1/2 h^TT H(f)(a) h + norm(h)^2 epsilon(h) \
    >= (lambda_1 / 2 + epsilon (h)) norm(h)^2
  $
  On peut alors trouver $delta > 0$ tel que pour tout $h in B(0, delta)$
  $
    f(a + h) - f(a) >= lambda / 4 norm(h)^2
  $

#card("eqderpart", "Équations au dérivées partielles", ("Maths.Analyse.Calcul différentiel",))

Équations au dérivées partielles.

#answer

On pose $Omega = I times W subset.eq RR^n$ où $W subset.eq RR^(n - 1)$

On considère
$
  (E) quad pdv(f, x_1) = 0
$

Une fonction $f in C^1 (Omega, RR)$ est solution de $(E)$ ssi il existe $g in C^1 (W, RR)$ tel que
$
  f : func(Omega, RR, (x_1, dots, x_n), g(x_2, dots, x_n))
$

*Démonstration*

Soit $(x_2, dots, x_n) in W$
$
  func(I, RR, x_1, f(x_1, dots, x_n))
$
Est $C^1$ de dérivée nulle sur $I$ donc constante.

On note $g(x_2, dots, x_n)$ cette constante.

Soit $a in I$
$
  g : func(W, RR, (x_2, dots, x_n), f(a, dots, x_n))
$
Est $C^1$.

Réciproquement ces fonctions marchent.

// TODO: M404 Exemple

#card("laplaciencd", "Laplacien", ("Maths.Analyse.Calcul différentiel",))

Laplacien.

#answer

Soit $Omega subset.eq RR^n$ et $f in C^2(Omega, RR)$.

On définit le laplacien de $f$
$
  laplace f = sum_(j = 1)^n pdv(f, x_j, 2)
$

On dit que $f$ est harmonique sur $Omega$ si $laplace f = 0$.

*Laplacien polaire*

Pour $n = 2$, par exemple $Omega = RR^2 \\ {(0, 0)}$ et $W = R_+^* times RR$, on pose
$
  phi : func(W, Omega, (r, theta), (r cos theta, r sin theta))
$
Et $f in C^2 (Omega, RR), tilde(f) = f compose phi$.

Alors
$
  laplace f (r cos theta, r sin theta) \
  = pdv(tilde(f), r, 2) (r, theta) + 1 /r pdv(tilde(f), theta, r) (r, theta) + 1/r^2 pdv(tilde(f), theta, 2) (r, theta)
$

*Démonstration*

Calcul moche, penser à utiliser la matrice Jacobienne (voir changement polaire).

#card("exfunharm", "Exercice : fonctions harmoniques invariantes par rotation", ("Maths.Analyse.Calcul différentiel",))

Trouver les fonctions harmoniques sur $RR^2$ tel qu'on dispose de $phi in C^2(RR, RR)$ tel que
$
  f(x, y) = phi(x^2 + y^2)
$

#answer

Pour $(r, theta) in RR_+^* times RR$
$
  0 &= laplace f (r cos theta, r sin theta) \
  &= pdv(tilde(f), r, 2) (r, theta) + 1/r pdv(tilde(f), r) (r, theta) \
  &= 1 / r pdv(,r) (r pdv(tilde(f), r)(r, theta))
$
$
  <=> forall r in RR_+^*, (r |-> r h'(r))' = 0 \
  <=> exists alpha in RR, forall r in RR_+^*, r h'(r) = alpha \
  <=> exists alpha in RR, forall r in RR_+^*, h'(r) = alpha / r \
  <=> exists alpha in RR, forall r in RR_+^*, h(r) = alpha ln(r) + beta \
$

#card("exfunharmpol", "Exercice : Intégrale sur un cercle d'une fonction harmonique", ("Maths.Analyse.Calcul différentiel",))

Soit $f in C^2(Omega, RR)$ qui est harmonique sur $Omega$ et où $0 in Omega subset.eq RR^2$, et $R > 0$ tel que $B(0, R) subset.eq Omega$.

Pour tout $r in Ico(0, R)$ exprimer 
$
  h(r) = 1/ (2 pi) integral_0^(2 pi) f(r cos theta, r sin theta) dif theta
$

#answer

On pose 
$
  tilde(f) : (r, theta) |-> f(r cos theta ,r sin theta)
$

On montre par le théorème $C^2$ des intégrales à paramètres que $h$ est $C^2$.

Ainsi pour tout $r in Ioo(0, r)$
$
  h''(r) + 1/r h'(r) \ = 1 /(2pi) integral_0^(2 pi) [pdv(tilde(f), r, 2) (r, theta) + 1 / r pdv(tilde(f), r) (r, theta)] dif theta \
  = - 1 / (2 pi r^2) integral_0^(2 pi) pdv(tilde(f), theta, 2) (r, theta) dif theta
$ 

Qui est nulle par $2pi$-périodicité de $theta |-> tilde(f) (theta, r)$.

Ainsi
$
  h : r |-> alpha ln(r) + beta
$
Et par continuité de $h$ en $0$, $alpha = beta = 0$.

#card("fonctionconv", "Fonctions convexes", ("Maths.Analyse.Calcul différentiel",))

Fonctions convexes (Calcul différentiel).

#answer

Soit $Omega$ un ouvert convexe de $E$, et $f : Omega -> RR$. On dit que $f$ est convexe si pour tout $x, y in Omega$ et $t in [0, 1]$
$
  f(underbrace((1 - t) x + t y, in Omega)) <= (1 - t) f(x) + t f(y)
$

*Conditions nécéssaires / suffisantes*

- $f$ est convexe ssi pour tout $x, y in Omega$ #h(1fr)
  $
    phi_(x, y) : func([0, 1], RR, t, f((1 - t) x + t y))
  $
  Est convexe sur $[0, 1]$.

- Si $f$ est convexe alors pour tout $x, y in Omega$
  $
    f(y) >= f(x) + dif f (x) . (y - x)
  $

Et si $E$ est euclidien et $f$ $C^1$, on a équivalence entre

- $f$ convexe. #h(1fr)

- Pour tout $x, y in Omega$
  $
    f(y) >= f(x) + scl(grad f (x), y - x)
  $

- Pour tout $x, y in Omega$
  $
    scl(grad f (y) - grad f(x), y - x) >= 0
  $

*Démonstration*

- Un sens évident.

  On suppose $f$ convexe, $x , y in Omega$ et $t_1, t_2, s in [0, 1]$.
  $
    &phi_(x, y) (underbrace((1 - s) t_1 + s t_2, s')) \
    =& f((1 - s') x + s' y) \
    =& f(script((1 - s) ((1 - t_1) x + t_1 y) + s ((1 - t_2) x + t_2 y))) \
    <=& (1 - s) phi_(x, y) (t_1) + s phi_(x, y) (t_2)
  $

- Comme $f$ est convexe, $phi_(x, y)$ l'est sur $[0, 1]$.

  $
    phi_(x, y) (1) &>= phi_(x, y) (0) + phi'_(x, y) (0) (1 - 0) \
    f(y) &>= f(x) + dif f (x).(y - x)
  $

- On suppose $f$ convexe, par ci-dessus, pour tout $x, y in Omega$
  $
    f(y) >= f(x) + scl(grad f (x), y - x)
  $
  Ainsi
  $
    cases(space f(y) >= f(x) + scl(grad f (x), y -x), space f(x) >= f(y) + scl(grad f (y), x - y)) \
    0 >= scl(grad f (x) - grad f (y), y - x)
  $

- On suppose la croissance des gradients.

  Soit $x, y in Omega$, montrons que $phi_(x, y)$ est convexe.

  Soit $t in [0, 1]$
  $
    phi'_(x, y) (t) &= dif f (x + t( y -x)).(y - x) \
    &= scl(grad f (x + t(y - x)), y - x)
  $
  Donc pour tout $t >= s$, on pose
  $
    x_t = x + t (y - x) \
    x_s = x + s (y - x)
  $
  D'où
  $
    &phi'_(x, y) (t) - phi'_(x, y) (s) \
    =& scl(grad f (x_t) - grad f (x_s), y - x) \
    =& 1 / (t - s) scl(grad f (x_t) - grad f(x_s), x_t - x_s) \
    >=& 0
  $
  Donc $phi_(x, y)$ convexe et $f$ aussi.

#card("propconvcd", "Propriétés supplémentaires de convexité", ("Maths.Analyse.Calcul différentiel",))

Propriétés supplémentaires de convexité.

#answer

- Si $f in C^1(Omega, RR)$ est convexe et admet un extremum local, alors c'est un minimum global.

- Si $f in C^2 (Omega, RR)$, on a équivalence entre

  + $f$ est convexe sur $Omega$.

  + Pour tout $x in Omega$, $H(f)(x) in S_n^+ (RR)$.

*Démonstration*

- Avec la condition de convexité sur $dif f$.

- On reprend la démonstration du DL à l'ordre 2 pour la Hessienne.

  Pour tout $a, b in Omega$
  $
    f(b) = f(a) + dif f (a).(b - a) \ + integral_0^1 script((1 - t) (b - a)^TT H(f)(a + t (b - a)) (b - a) dif t)
  $

#card("exmethnewt", "Exercice : contexte de la descente du gradient", ("Maths.Analyse.Calcul différentiel",))

Soit $u in S_n^(++) (RR)$ et $phi in cal(L)(E, RR)$, on pose
$
  f &: func(E, RR, x, 1/2 scl(x, u(x)) + phi(x)) \ &in C^1(E, RR)
$

+ Calculer $dif f (x)$ et $grad f(x)$ pour tout $x in EE$.

+ Montrer que $f(x) tends(norm(x) -> +oo) +oo$.

+ Montrer que $f$ admet un unique minimum local, puis qu'il est global.

+ Montrer que $f$ est strictement convexe.

#answer

+ Par simple calcul (et par théorème de représentation) on obtient  #h(1fr)
  $
    dif f (x) : func(E, RR, h, scl(h, u(x)) + scl(h, v))
  $
  Pour un $v in E$ qui dépend de $phi$.

  D'où
  $
    grad f(x) = u(x) + v
  $

+ On note $0 < lambda_1 <= dots.c, <= lambda_n$ le spectre ordonné de $u$.

  Pour tout $x in E$
  $
    f(x) &>= lambda_1 norm(x)^2 - norm(v) norm(x) \ &tends(norm(x) -> +oo) +oo
  $

+ Si $f$ admet un minimum local en $x_0 in E$
  $
    dif f(x_0) = 0
  $
  D'où pour tout $h in E$
  $
    scl(grad f(x_0), h) = 0 \
    u(x) + v = 0
  $
  Or comme $u in "GL"(E)$, le seul point critique est
  $
    x_0 = - u^(-1) (v)
  $

  Or comme $f tends(+oo) +oo$, on dispose de $R > 0$ tel que
  $
    min_(x in E) f(x) = min_(x in B(0, R)) f(x)
  $
  Qui est atteint (par compacité), d'où $x_0$ est un minimum global.

+ Pour tout $x, y in Omega$
  $
    scl(grad f(x) - grad f(y), x - y) \
    = scl(u(x) - u(y), x - y) >= 0
  $

#card("excondjacob", "Exercice : determination d'une fonction dont la Jacobienne est antisymetrique ou orthogonale", ("Maths.Analyse.Calcul différentiel",))

Soit $f in C^2 (RR^n, RR^n)$

Déterminer $f$ si

+ $forall x in RR^n, J(f)(x) in A_n (RR)$.
+ $forall x in RR^n, J(f)(x) in O_n (RR)$.

#answer

On commence par montrer deux lemmes.

*Lemme 1*

Soit $f in C^1 (RR^n, RR^n)$, on a équivalence entre

- $exists A in M_n (RR), forall x in RR^n, J(f)(x) = A$.

- $exists A in M_n (RR), b in RR^n$
  $
    f : x |-> A x + b
  $

*Démonstration*

Un sens évident.

Soit $x in RR^n$, on pose
$
  gamma : func([0, 1], RR^n, t, t x)
$
Ainsi
$
  f(x) - underbrace(f(0), b) &= integral_0^1 dif f (gamma(t)).gamma'(t) dif t \
  &= integral_0^1 J(f)(gamma(t)) gamma'(t) dif t \
  &= integral_0^1 A x dif t \
  &= A x
$

*Lemme 2*

Soit $X$ des ensembles et $phi : X^3 -> RR$.

On suppose que pour tout $i, j, k in X$
$
  phi(i, j, k) &= phi(j, i, k) \
  &= -phi(k, j, i)
$

Alors $phi = 0$.

*Démonstration*

Ça se voit.

*Exercice*

+ On en déduit que pour tout $i, j in [|1, n|]$
  $
    pdv(f_i, x_j) = - pdv(f_j, x_i)
  $

  Donc pour tout $i, j, k in [|1, n|]$
  $
    pdv(f_i, x_k, x_i) = -pdv(f_j, x_k, x_j)
  $
  
  Et par Schwarz et le lemme 2,
  $
    pdv(f_i, x_k, x_j) = 0
  $

  Ainsi par convexité de $RR^n$
  $
    pdv(f_i, x_j) : x |-> a_(i j)
  $
  Et
  $
    x |-> J(f)(x) = A
  $
  Et on conclut par le lemme 1.

+ Pour tout $i, j in [|1, n|]$
  $
    x |-> scl(pdv(f, x_i) (x), pdv(f, x_j) (x)) = delta_(i j)
  $
  Ainsi pour tout $i, j, k in [|1, n|], x in RR^n$
  $
    overbrace(scl(pdv(f, x_k, x_i) (x), pdv(f, x_j) (x)), phi(i, j, k)) \
    + scl(pdv(f, x_i) (x), pdv(f, x_k, x_j)) = 0
  $
  Donc par Schwarz et le lemme 1
  $
    scl(pdv(f, x_k, x_i) (x), pdv(f, x_j) (x)) = 0
  $
  Or par hypothèse $(pdv(f, x_j) (x))_j$ forme une BON, donc
  $
    forall i, k in [|1,n|], space pdv(f, x_k, x_i) = 0
  $

  Et on conclut comme ci dessus.

#card("fonctionhomogènes", "Fonctions homogènes", ("Maths.Analyse.Calcul différentiel",))

Fonctions homogènes.

#answer

Soit $f in C^1 (RR^n, RR)$ et $alpha in RR$

On dit que $f$ est $alpha$-homogène si (de manière équivalente)

+ $forall x in RR^n, forall mu > 0, f(mu x) = mu^alpha f(x)$

+ $forall x in RR^n, dif f (x) = alpha f(x)$

+ $forall x n RR^n, sum_(i = 1)^n x_i pdv(f, x_i) (x) = alpha f(x)$

*Application*

On considère
$
  (E) quad x pdv(f, x) + y pdv(f, y) = underbrace(sqrt(x^3 + y^3), h(x, y))
$

Comme $h$ est $3 / 2$-homogène, $f_p = 2 /3 h$ est solution particulière.

On se ramène à resoudre l'équation homogène
$
  (E_0) quad x pdv(f, x) + y pdv(f ,y) = 0
$
Qui est $0$-homogène, puis par continuité en $0$ on conclut que $f_h$ est constante et nulle.

*Démonstration*

- (ii $<=>$ iii) Par définition.

- (i $=>$ ii) Soit $x in RR^n$, on pose #h(1fr)
  $
    phi : func(RR_+^*, RR, mu, f(mu x)) in C^1(RR_+^*, RR)
  $
  $
    phi' : mu |->& dif f(mu x).x \
    =& (mu |-> mu^alpha f(x))'(mu) \
    =& alpha mu^(alpha - 1) f(x) \
  $
  Et on conclut en évaluant en $1$.

- (ii $=>$ i) Soit $x in RR^n$, on pose le même $phi$.
  $
    phi' : mu |->& 1 / mu dif f (mu x).mu x \
    =& alpha / mu phi(mu)
  $
  Ainsi (avec les conditions initiales)
  $
    phi : mu |-> mu^alpha f(x)
  $

#card("exprinmacafunharm", "Exercice : Principe du maximum pour les fonctions harmoniques", ("Maths.Analyse.Calcul différentiel",))

Soit $f in C^0 (overline(Omega), RR)$ et $C^2(Omega, RR)$ où $Omega subset.eq E$ ouvert et $overline(Omega)$ compact.

On suppose que $forall a in Omega, laplace f (a) >= 0$

Montrer que
$
  max_(overline(Omega)) f = max_(partial Omega) f
$

#answer

Comme $f$ est $C^0$ sur un compact, ce maximum est bien définit.

- On traite le cas où $laplace f > 0$ d'abord. #h(1fr)

  Supposons par l'absurde que $f$ atteint son maximum en $x in Omega$, alors
  $
    laplace f (x) = tr (H (f) (x)) <= 0
  $
  Absurde.

- Pour le cas général.

  On pose pour tout $k in NN^*$
  $
    f_k : x |-> f(x) + 1/k norm(x)^2
  $
  Pour tout $x in Omega$
  $
    laplace f_k (x) = laplace f (x) + 1/k (sum_(k = 1)^n 2) = (2 n) /k > 0
  $
  Ainsi $f_k$ atteint son maximum en $x_k in partial Omega$.

  Or par compacité 
  $
  x_phi(k) tends(k -> +oo) y in partial Omega
  $

  Donc pour $x in overline(Omega)$
  $
    f(x) &= f_phi(k) - 1/phi(k) norm(x)^2 \
    &<= f_phi(k) (x_phi(k)) \
    &= f(x_phi(k)) + 1/phi(k) norm(x_phi(k))^2 \
    &<= f(x_phi(k)) + R^2 / phi(k) \
    &tends(k -> +oo) f(y)
  $
  Où $overline(Omega) subset.eq B(0, R)$.

  Ainsi pour tout $x in overline(Omega)$
  $
    f(x) <= f(underbrace(y, in partial Omega)) = max_overline(Omega) f
  $

#card("fonctionsholomorphes", "Fonctions holomorphes", ("Maths.Analyse.Calcul différentiel",))

Fonctions holomorphes.

#answer

Soit $Omega$ un ouvert de $CC$ et $f : Omega -> CC$.

On dit que $f$ est dérivable par rapport à la variable complexe en $z_0 in Omega$ si
$
  z in Omega\\{z_0} |-> (f(z) - f(z_0)) / (z - z_0)
$
Admet une limite finie en $z_0$.

*Méthode*

On pose l'homéomorphisme
$
  theta : func(RR^2, CC, (x, y), x + i y)
$

Et $Omega_0 = theta^(-1) (Omega)$ qui est un ouvert de $RR^2$.
$
  f_0 : func(Omega_0, CC, (x, y), script(f(x + i y) = f_1 (x, y) + i f_2 (x, y)))
$

Avec $f_1, f_2 : Omega_0 -> RR$.

*Propriétés*

Si de plus $f_0 in C^1(Omega_0 CC)$ ($CC$ vus comme un $RR$-ev de dimension $2$).

On montre l'équivalence suivante

+ $f$ est $CC$-dérivable en $z_0$.

+ $J(f_0) (x_0, y_0)$ est un similitude directe.

+ On a
  $
  cases(space pdv(f_1, x) (x_0, y_0) = pdv(f_2, y) (x_0, y_0), space pdv(f_2, x) (x_0, y_0) = - pdv(f_2, y) (x_0, y_0))
  $

*Conséquence*

Si $f$ est $CC$-dérivable sur $Omega$ et $f_0 in C^2 (Omega_0, CC)$, alors $f_1$ et $f_2$ sont harmoniques.

*Démonstration*

- (ii $<=>$ iii) Par définition.

- (iii $=>$ i) Soit $h = h_1 + i h_2 in CC$ suffisament petit. #h(1fr)
  $
    f_0 (x_0 + h_1, y_0 + h_2) = f_0 (x_0, y_0) quad quad (*) \
    + pdv(f_0, x) (x_0, y_0) h_1 + pdv(f_0, y) (x_0, y_0) h_2 + o(abs(h))
  $

  Or par (iii)
  $
    pdv(f_0, y) (x_0, y_0) = i pdv(f_0, x) (x_0, y_0)
  $
  Et $(*)$  devient
  $
    f(z_0 + h) \ = f(z_0) + pdv(f_0, x) (x_0, y_0) (h_1 + i h_2) + o(abs(h)) \
  $
  Et donc
  $
    (f(z_0 + h) - f(z_0)) / h &= pdv(f_0, x) (x_0, y_0) + 1/h o(abs(h)) \
    &tends(h -> 0 \ h != 0) pdv(f_0, x) (x_0, y_0)
  $

- (i $=>$ iii) On suppose que
  $
    (f(z_0 + h) - f(z_0)) / h tends(h -> 0 \ h != 0) f'(z_0) in CC \
    f(z_0 + h) - f(z_0) = f'(z_0) h + o(abs(h))
  $
  On pose $a_0 = (x_0, y_0)$.

  Ainsi $(h = h_1 + i h_2)$
  $
    f_0 (x_0 + h_1, y_0 + h_2) \
    = f(a_0) + (h_1 + i h_2) f'(z_0) + o(abs(h))
  $
  Donc
  $
    dif f_0 (a_0) : vec(h_1, h_2) |-> (h_1 + i h_2) f'(z_0)
  $
  Et
  $
    pdv(f_0, x) (a_0) = dif f_0 (a_0) vec(0, 1) = f'(z_0) \
    pdv(f_0, y) (a_0) = dif f_0 (a_0) vec(1, 0) = i f'(z_0) \
  $

- Pour $laplace f_1$
  $
    laplace f_1 &= pdv(f_1, x, 2) + pdv(f_1, y, 2) \
    &= pdv(,x) (pdv(f_2, y)) + pdv(,y) (- pdv(f_2, x)) = 0
  $
  Par Schwarz.

  Et de même pour $laplace f_2$.

#card("foncharmholom", "Fonctions harmoniques, holomorphes et séries entières", ("Maths.Analyse.Calcul différentiel",))

Fonctions harmoniques, holomorphes et séries entières.

#answer

Soit $R > 0$ et $g in C^2(DD(0, R), RR)$ tel que $laplace g = 0$.

On cherche à montrer que $g$ s'écrit comme la partie réelle d'une fonction developpable en série entière.

- On va developper en série de Fourier. On pose #h(1fr)
  $
    tilde(g) (r, theta) = g(r cos theta, r sin theta) \
    g_r : theta |-> tilde(g)(r, theta) \
  $

- Dans le cas $C^2$, la série de Fourier converge normalement et la fonction est égale à la somme de sa série de Fourier (à redémontrer).

On pose pour $n in ZZ$
$
  h_n : r |->& c_n (g_r) \ 
  =& 1/(2pi) integral_0^(2pi) e^(- i n theta) tilde(g)(r, theta) dif theta
$

Comme dans le cas $n = 0$ (voir intégrale sur un cercle d'une fonction harmonique), on cherche une EDL d'ordre $2$ pour $h_n$.

Par le théorème $C^2$ des intégrales à paramètres (vérifier les hypothèses), $h_n$ est $C^2$ sur $Ico(0, R)$.

Or comme $g$ est harmonique, pour tout $r in Ioo(0, R)$ et $theta in RR$
$
  pdv(tilde(g), r, 2) (r, theta) + 1 / r pdv(tilde(g), r) (r, theta) + 1/ r^2 pdv(tilde(g), theta, 2) (r, theta) = 0
$

Ainsi pour tout $r in Ioo(0, R)$
$
  h''_n (r) + 1/r h'_n (r) \ 
  = 1/(2 pi r^2) integral_0^(2pi) e^(i n theta) pdv(tilde(g), theta^2) (r, theta) dif theta \
$
Puis on montre par 2 IPP et par $2pi$-périodicité du crochet, que
$
  h''_n (r) + 1/r h'_n (r) = n^2 / r^2 h_n (r)
$
Donc $h_n$ est solution de
$
  (E_n) quad y'' + 1/r y_' - n^2 / r^2 y = 0
$
On remarque que $y_n : r |-> r^n$ est solution et $y_(-n)$ aussi.

D'où $h_n in "Vect"(y_n, y_(-n))$ et par continuité en $0$
$
  h_n : r |-> alpha_n r^abs(n)
$

Or comme $g$ est $C^2$ (somme de la série de Fourier)
$
  tilde(g)(r, theta) &= g_r (theta) = sum_(n in ZZ) C_n (g_r) e^(i n theta) \
  &= sum_(n = in ZZ) alpha_n r^abs(n) e^(i n theta)
$

Or $g$ est à valeurs réelles, donc par liberté des $(theta |-> e^(i n theta))$, $overline(alpha_n) = alpha_(- n)$.

Ainsi
$
  tilde(g)(r, theta) &= alpha_0 + sum_(n = 1)^(+oo) r^n (alpha_n e^(i n theta) + alpha_(-n) e^(- i n theta)) \
  &= Re (alpha_0 + sum_(n = 1)^(+oo) (2 alpha_n) (r e^(i theta))^n)
$

*Pour une fonction holomorphe*

Soit $f in C^1 (DD_CC (0, RR), CC)$ holomorphe.

On lui associe (voir fonctions holomorphes)
$
  f_0 : func(DD_RR(0, R), CC, (x, y), f_1 (x, y) + i f_2 (x, y))
$

On a que $laplace f_1 = laplace f_2 = 0$ donc $laplace f_0 = 0$.

On note 
$
tilde(f_0) : (r, theta) |-> f_0 (r cos theta, r sin theta)
$

Et comme avant on pose
$
  h_n (r) = 1/(2pi) integral_0^(2pi) e^(-i n theta) tilde(f_0) (r, theta) dif theta
$

Comme $laplace f_0 = 0$, on a la même EDL et
$
  h_n : r |-> alpha_n r^abs(n)
$

Ainsi
$
  f(r e^(i theta)) = alpha_0 + sum_(n = 1)^(+oo) (alpha_n r^n e^(i n theta) + alpha_(-n) r^n e^(-i n theta))
$

On veut montrer que $alpha_(-n) = 0$ pour tout $n in NN^*$ (pour avoir $f$ developpable en série entière).

Deux méthodes

+ On peut exploiter l'égalité entre les dérivée partielles pour les fonctions holomorphes (voir fiche) pour trouver une autre EDL vérifié par les $(h_n)$.

+ On regarde #h(1fr)
  $
    sum_(n = 1)^(+oo) (alpha_n r^n e^(i n theta) + alpha_(-n) r^n e^(- i n theta)) \
    = g(z) + h(z)
  $
  Où
  $
    g : z |-> sum_(n = 1)^(+oo) alpha_n z^n \
    h : z |-> sum_(n = 1)^(+oo) alpha_(-n) z^n \
  $
  $f$ et $g$ sont holomorphes, donc $h$ est holomorphe.
