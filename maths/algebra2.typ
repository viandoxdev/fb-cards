#import "/cards.typ": *

#show: setup

//![FLASHBANG HEADER]

#import "/utils.typ": *
#import "@preview/tiptoe:0.3.1"
#import "@preview/lilaq:0.4.0" as lq
#import "@preview/fletcher:0.5.8" as fletcher: diagram, node, edge
#import "@preview/physica:0.9.7": *

#card("expendom", "Exponentielle d'un endomorphisme", ("Maths.Algèbre.Algèbre linéaire.Exponentielle d'endomorphismes",))

Exponentielle d'un endomorphisme.

#answer

Soit $u in cal(L)(E)$ avec $E$ un $RR$ ou $CC$-ev de dimension finie.

La série $sum u^n / n!$ est absolument convergente et on note
$
  exp(u) = e^u = sum_(n = 0)^(+oo) u^n / n!
$

On a

- $exp$ est continue.

- Pour tout $u in cal(L)(E)$ #h(1fr)
  $
    f : func(RR, cal(L)(E), t, e^(t u))
  $
  Est $C^1$ et
  $
    f' : t |-> u compose e^(t u) = e^(t u) compose u
  $
  Donc $f$ est $C^oo$.

- Pour tout $D = diag(a_1, dots, a_n) in D_n (KK)$
  $
    e^D = diag(e^(a_1), dots, e^(a_n))
  $

- Pour tout $T in T_n^+ (KK)$
  $
    T = mat(a_1,,(*);,dots.down;,,a_n) \
    e^T = mat(e^(a_1),,(*);,dots.down;,,e^(a_n))
  $

- Pour tout $A in M_n (KK), P in "GL"_n (KK)$
  $
    exp(P^(-1) A P) = P^(-1) exp(A) P
  $

- Pour tout $A in M_n (KK)$
  $
    det(e^A) = e^(tr A) > 0
  $

- Pour tout $A, B in M_n(KK)$ qui commutent.
  $
    e^A e^B = e^B e^A = e^(A + B)
  $

- Pour tout $A in M_n (KK)$
  $
    (e^A)^(-1) = e^(- A)
  $

- Pour tout $A in M_n (KK), e^A in KK[A]$.

*Démonstration*

Comme toutes les normes sont équivalentes, on choisit la norme $norm(dot)_"op"$ associée à une norme $norm(dot)$ sur $KK^n$.

Ainsi pour tout $k in NN$
$
  norm(u^k)_"op" <= norm(u)^k_"op" \
  norm(u^k / k!)_"op" <= norm(u)_"op"^k / k!
$
Qui est le terme général d'une série convergente.

De plus

- Pour tout $R > 0$, la série converge normalement sur $overline(B(0, R))$, donc uniformément.

- Théorème $C^1$ des séries de fonctions.

- Sommes partielles puis limite.

- Sommes partielles puis limite.

- Sommes partielles puis continuité.

- On dispose de $T in T_n^+ (CC)$ et $P in "GL"_n (CC)$
  $
    A &= P^(-1) T P \
    det(e^A) &= det(P^(-1) e^T P) \ &= det(e^T) \ &= e^(tr A)
  $

- On pose
  $
    theta : t |-> e^(t (A + B)) e^(- t A) e^(- t B)
  $
  Qui est $C^1$. Or si $A B = B A$, pour tout $P, Q in KK[X]$
  $
    P(A) Q(B) = Q(B) P(A)
  $
  Donc à la limite, $e^A e^B = e^B e^A$.

  En dérivant on trouve $theta' = 0$. Donc pour tout $t in RR$
  $
    theta(t) = theta(0) = I_n \
    e^(t A + B) e^(-t A) e^(-t B) = I_n \
    e^(t A + B) = e^(t A) e^(t B)
  $
  Qui tient pour $t = 1$.

- Avec $B = -A$
  $
    e^(A - A) = I_n = e^A e^(-A)
  $

- Limite dans un $KK$-evn de dimension finie, qui est donc fermé.

#card("exexpaneqson", "Exercice : exponentielle des matrices antisymétriques", ("Maths.Algèbre.Algèbre linéaire.Exponentielle d'endomorphismes",))

+ Montrer que #h(1fr)
  $
    exp(A_n (RR)) = "SO"_n (RR)
  $

+ Montrer que si $A in M_n (RR)$ est tel que pour tout $t in RR$
  $
    e^(t A) in O_n (RR)
  $
  Alors $A in A_n (RR)$.

#answer

+ - Soit $A in A_n (RR)$, on montre que #h(1fr)
    $
      (e^A)^TT = e^(A^TT)
    $
    En passant à la limite les sommes partielles, ainsi
    $
      (e^A)^TT = e^(-A) = e^(A)^(-1)
    $
    Donc $e^A in O_n (RR)$, or $det e^A > 0$, donc $e^A in "SO"_n (RR)$.

  - Soit $A in "SO"_n (RR)$.
    $
      A = P dmat(I_p, R_theta_1, dots.down, R_theta_r) P^T
    $
    Avec $P in O_n (RR)$.

    On pose
    $
    Omega^0 &=& I_2 quad quad Omega^1 &=& mat(0, -1;1, 0) \
    Omega^2 &=& -I_2 quad quad Omega^3 &=& mat(0, 1; -1, 0)
    $
    $
      Omega^4 = I_2
    $
    Ainsi
    $
      I_p = e^(0_p) \
    $
    $
      R_theta &= mat(cos theta, -sin theta; sin theta, cos theta) \
      &= e^(Omega theta)
    $
    D'où
    $
      A = exp(underbrace(dmat(0_p, theta_1 Omega, dots.down, theta_r Omega), in A_n (RR)))
    $

+ On pose
  $
    f: t |-> e^(t A) (e^(t A))^TT = I_n \
    f': t |-> e^(t A) A (e^(t A))^TT + e^(t A) A^TT (e^(t A))^TT = 0
  $
  En $t = 0$
  $
    A + A^TT = 0
  $

#card("expnilpot", "Exponentielle et nilpotents", ("Maths.Algèbre.Algèbre linéaire.Exponentielle d'endomorphismes",))

Exponentielle et nilpotents, surjectivité de l'exponentielle dans le groupe linéaire.

#answer

Si $N in M_n (CC)$ est nilpotent
$
  e^N &= sum_(k = 0)^(n - 1) N^k / k! \
  &= I_n + underbrace(sum_(k = 1)^(n - 1) N^k / k!, "nilpotent")
$

Et pour toute matrice unipotente : $M = I_n + N$, on dispose de $A$ nilpotent tel que
$
  e^A = I_n + N = M
$

On en déduit que pour tout
$
  M = lambda I_n + N = lambda (I_n + 1/lambda N)
$
On dispose de $A$ nilpotente tel que $M = e^A$.

Ainsi pour tout $M in "GL"_n (CC)$, comme on dispose de $P in "GL"_n (CC)$ tel que
$
  M = P dmat(lambda_1 I_m_1 + N_1, dots.down, lambda_p I_m_p + N_p) P^(-1)
$
On dispose de $A in M_n (CC)$ tel que $M = e^A$.

On peut montrer de plus que $A in KK[M]$ (revoir Dunford).

*Démonstration 1*

Candidat : (logarithme)
$
  A = sum_(k = 1)^(n - 1) (-1)^(k - 1) N^k / k
$

On pose
$
  P(X) &= sum_(k = 0)^(n - 1) X^k / k! \
  Q(X) &= sum_(k = 1)^(n - 1) (-1)^(k - 1) X^k /k
$
Ainsi
$
  e^x &= P(x) + o_(x -> 0) (x^(n - 1)) \
  ln(1 + x) &= Q(x) + o_(x -> 0) (x^(n - 1))
$
Par composée de DL
$
  1 + x = e^(ln (1 + x)) = R(x) + o_(x -> 0) (x^(n - 1))
$
Où $R$ est $P compose Q$ tronqué à l'ordre $n - 1$.
$
  P(Q(X)) = R(X) + X^n R_0 (X)
$
Par unicité de la partie principale
$
  1 + X = R(X) = P(Q(X)) - X^n R_0 (X)
$
Ainsi
$
  M = I_n + N = P(Q(N)) - underbrace(N^n R_0 (N), 0)
$
Or $Q(N)$ est nilpotent, donc
$
  M = I_n + N =P(Q(N)) = e^(Q (N))
$

*Démonstration 2*

On pose
$
  f : t |-> sum_(k = 1)^(n - 1) ((-1)^(k - 1) t^k N^k) / k \
  g : t |-> e^f(t) = sum_(k = 0)^(n - 1) f(t)^n / k!
$
Car $f(t)$ est nilpotent.

Comme toutes nos fonctions sont à valeur dans $KK[N]$ qui est une algèbre commutative
$
  g'(t) &= sum_(k = 1)^(n - 1) (k f'(t) f(t)^(k - 1)) / k! = f'(t) g(t) \
  f'(t) &= sum_(k = 1)^(n - 1) (-1)^k N^k t^(k - 1) = N (I_n + N)^(-1)
$
Or $t |-> I_n + t N$ et $g$ sont solution de
$
  cases(space y(0) = I_n, space y' (t) = N (I_n + N)^(-1) y(t))
$
D'où par le théorème de Cauchy-Lipschitz
$
  g(t) = I_n + t N
$
Et en $t = 1$
$
  I_n + N = exp(f(1))
$

// NOTE: Exo M348

#card("limexpendom", "Autre expression de l'exponentielle", ("Maths.Algèbre.Algèbre linéaire.Exponentielle d'endomorphismes",))

Autre expression de l'exponentielle.

#answer

On pose
$
  f_k : func(M_n (KK), M_n (KK), A, (1 + A / k)^k)
$
La suite $(f_k)_k$ converge uniformément sur tout compact vers $exp$.

*Démonstration*

On pose
$
  S_k : func(M_n (KK), M_n (KK), A, sum_(j = 0)^k A^j / j!)
$
On sait que $(S_k)_k$ converge uniformément vers $exp$ sur tout compact.

Soit $k in NN^*$
$
  f_k : A |-> sum_(j = 0)^k vec(k, j) A^j / k^j \
$
$
  &S_k (A) - f_k (A)  \
  =& sum_(j = 0)^k A^j / j! (1 - underbrace((product_(m = 0)^(j - 1) (k - m)) /k^j, = product_(m = 0)^(j - 1) (k - m) / k <= 1))
$
Donc pour tout $A in overline(B(0, R))$
$
  &norm(S_k (A) - f_k (A)) \
  <=& sum_(j = 0)^k norm(A)^j / j! (1 - (product_(m = 0)^(j - 1) (k - m)) / k^j) \
  <=& sum_(j = 0)^k R^j / j! (1 - (product_(m = 0)^(j - 1) (k - m)) / k^j) \
  =& (sum_(j = 0)^k R^j / j!) - (1 + R / k)^k \
  tends(k -> oo)& e^R - e^R = 0
$
Ainsi $norm(S_k - f_k)_oo tends(k -> oo) 0$ et $norm(S_k - exp)_oo tends(k -> oo) 0$ d'où le résultat.

#card("sevtangent", "Exercice : caractérisation de l'espace tangent à l'identité d'un groupe de Lie", ("Maths.Exercice.Exponentielle d'endomorphismes",))

Soit $G subset.eq "GL"_n (RR)$ un sous groupe fermé, on note 
$
frak(G) = Set(M in M_n (RR), forall r in RR, e^(t M) in G)
$
Montrer que $frak(G)$ est un sev de $M_n (RR)$.

#answer

- Soit $M in frak(G), lambda in RR$ et $t in RR$ #h(1fr)
  $
    e^(t (lambda M)) = e^((t lambda) M) in G
  $

- Montrons d'abord le lemme suivant : pour tout $A, B in M_n (RR)$
  $
    e^(A + B) = lim_(k -> oo) (e^(A / k) e^(B / k))^k
  $

  On a
  $
    e^(A / k) = sum_(j = 0)^(+oo) A^k / (j! k^j) = I_n + A / k + R_k \
    R_k = O_(k -> oo) (1 / k^2)
  $
  Car
  $
    R_k = 1 / k^2 (sum_(j = 2)^(+oo) underbrace(1 / j! A^(j - 2)/k^(j - 2),  norm(dot) <= norm(A)^(j - 2) / j!))
  $
  Ainsi
  $
    &(e^(A / k) e^(B / k))^k  \
    =& (I_n + (A + B) / k + O_(k -> oo) (1/k^2))^k \
    =& (I_n + (A + B + epsilon_k) / k)^k quad epsilon tends(k -> oo) 0 \
    =& f_k (A + B + epsilon_k)
  $
  Comme $A + B + epsilon_k tends(k -> oo) A + B$ et $f_k$ converge uniformément vers $exp$ sur $overline(B(0, norm(A) + norm(B) + 1))$, par les résultats sur les suites et séries de fonctions (découpage)
  $
    f_k (A + B + epsilon_k) tends(k -> oo) exp(A + B)
  $

- Soit $A, B in frak(G)$, pour tout $k in NN^*$ et $t in RR$
  $
    e^((t A) / k) in G quad quad e^((t B) / k) in G \

    (e^((t A) / k) e^((t B) / k))^k in G \
    lim_(k -> oo) (e^((t A) / k) e^((t B) / k))^k = e^(t (A + B)) in G
  $
  Car $G$ est fermé.

- Et $0 in frak(G)$ car $I_n in G$.

#card("calcpratiexp", "Calcul d'exponentielle d'endomorphismes", ("Maths.Algèbre.Algèbre linéaire.Exponentielle d'endomorphismes", "Maths.Calculs"))

Méthodes de calcul d'exponentielle d'endomorphismes.

#answer

Plusieurs cas :

+ Si $A = lambda I_n + N$ #h(1fr)
  $
    e^A = e^(lambda I_n) e^N = e^lambda (sum_(k = 1)^(n - 1) N^k / k!)
  $

+ Si $A$ est diagonalisable

  On note $"Sp" A = {lambda_1, dots, lambda_d}$
  $
    Pi_A = product_(k = 1)^d (X - lambda_k) \
    chi_A = product_(k = 1)^d (X - lambda_k)^m_k \
    A = P dmat(lambda_1 I_m_1, dots.down, lambda_d I_m_d) P^(-1)
  $
  Ainsi
  $
    e^A = P dmat(e^(lambda_1) I_m_1, dots.down, e^(lambda_d) I_m_d) P^(-1) = Q(A)
  $
  Avec $Q in KK_(d - 1) [X]$ tel que $Q_(lambda_k) = e^(lambda_k)$.
  $
    Q = sum_(k = 1)^d e^lambda_k product_(j != k) (X - lambda_j) / (lambda_k - lambda_j)
  $

+ Si on connaît un polynôme annulateur de $A$

  On suppose que $R(A) = 0$ avec $R in KK[X]$.

  + Si $R$ SARS, $A$ est diagonalisable, voir 2.

  + Si $R = (X - lambda)^d$ alors $A - lambda I_n = N$ nilpotent, voir 1.

  + Si $R = X^d (X - lambda)$ alors $A^(d + 1) = lambda A^d$ et pour tout $k >= d$
    $
      A^k = lambda^(k - d) A^d \
      e^A = sum_(k = 0)^(d - 1) A^k / k! + 1/ lambda^d (e^lambda - sum_(k = 0)^d lambda^k / k!) A^d
    $

  + Si $R = (X - mu)^d (X - lambda)$, on pose $tilde(A) = A - mu I_n$, $tilde(A)$ annule $X^d (X - lambda + mu)$ et on reprend le cas précédent.

  + Cas général : on fait la division euclidienne de $X^k$ par $R$
    $
      X^k = Q_k R + P_k \
      A^k = P_k (A)
    $
    Et on somme.

#card("exeqkereamin", "Exercice : égalité des noyaux d'une matrice et de son exponentielle", ("Maths.Algèbre.Algèbre linéaire.Exponentielle d'endomorphismes",))

+ Montrer que pour tout $A in M_n (CC)$, $ker A subset.eq ker (e^A - I_n)$. A-t-on l'égalité ?

+ Montrer que pour $N in M_n (CC)$ nilpotente, $ker N = ker (e^N - I_n)$.

+ Trouver une CNS sur $A in M_n (CC)$ pour que $ker A = ker (e^A - I_n)$.

#answer

+ Pour tout $A in M_n (CC)$, $X in ker A$
  $
    (e^A - I_n) X &= (sum_(k = 1)^(+oo) A^k / k!) X \ &= sum_(k = 0)^(+oo)(A^k X) / k! = 0 
  $

  En général l'égalité ne tient pas :
  $
    A = dmat(2 i pi, 2 i pi) \
    ker A = {0} \
    e^A - I_2 = 0 \
    ker (e^A - I_2) = CC^2
  $

+ Premier sens fait ci-dessus.

  soit $X in ker (e^N - I_n)$ #h(1fr)
  $
  d = min Set(k in NN^*, N^k X = 0) <= n
  $
  Donc
  $
    0 = (e^N - I_n) X = sum_(k = 1)^(d - 1) N^k / k! X
  $
  Or
  $
    (X, N X, dots, N^(d - 1) X)
  $
  Est libre, ainsi
  $
    forall i in [|1, d-1|],  1 / k! = 0
  $
  D'où
  $
    d = 1 quad "et" quad N X = 0
  $

+ Dans le cas général, soit $A in M_n (CC)$
  $
    underbrace(dmat(N, lambda_1 I_m_1 + N_1, dots.down, lambda_p I_m_p + N_p), P^(-1) A P = B)
  $
  Avec $dim ker A = dim ker N$
  $
    underbrace(inline(dmat(e^N - I_m, e^(lambda_1) e^(N_1) - I_m_1, dots.down, e^(lambda_p) e^(N_p) - I_m_p)), P^(-1) (e^A - I_n) P = M)
  $

  Or $ker (e^N - I_m) = ker N$ et les $e^(lambda_i) e^(N_i) - I_m_i$ sont inversibles ssi $e^(lambda_i) != 1$, on peut alors conclure :

  On a égalité ssi il n'existe pas $lambda in "Sp"(A) \\ {0}$ tel que $e^lambda = 1$.


