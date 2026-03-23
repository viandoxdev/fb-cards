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

