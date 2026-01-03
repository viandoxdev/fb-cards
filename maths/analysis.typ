#import "/cards.typ": *

#show: setup

//![FLASHBANG HEADER]

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

