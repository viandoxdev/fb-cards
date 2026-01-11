#import "/cards.typ": *

#show: setup

//![FLASHBANG HEADER]

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
