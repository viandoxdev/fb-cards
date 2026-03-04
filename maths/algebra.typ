#import "/cards.typ": *

#show: setup

//![FLASHBANG HEADER]

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

#card("invmat", "Théorème de caractérisation des matrices inversibles", ("Maths.Algèbre.Algèbre linéaire",))

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

#card("axesp", "Axiomes d'un espace vectoriel", ("Maths.Algèbre.Algèbre lineaire",))

Axiomes d'un espace vectoriel.

#answer

Sois $KK$ un corps, $E$ muni de la somme interne $+$ et du produit externe $dot$ est un $KK$-ev si
+ $(E, +)$ est un groupe abélien.
+ $forall x in E, 1 dot x = x$.
+ $forall lambda in KK, forall x, y in E, lambda (x + y) = lambda x + lambda y$.
+ $forall lambda, mu in KK, forall x in E, (lambda + mu) x = lambda x + mu x$.
+ $forall lambda, mu in KK, forall x in E, lambda (mu x) = (lambda mu) x$

#card("ran", "Théorème de caractérisation du rang", ("Maths.Algèbre.Algèbre lineaire",))

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

#card("forml", "Formes lineaires et hyperplans", ("Maths.Algèbre.Algèbre lineaire",))

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

#card("semb", "Matrices sembables", ("Maths.Algèbre.Algèbre linéaire",))

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

#card("irean", "Irréductibles d'un anneau", ("Maths.Algèbre.Anneaux et corps",))

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

- Soient $P, Q in ZZ[X]$ tels que $c(P) = c(Q) = 1$, alors $c(P Q) = 1$.
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

