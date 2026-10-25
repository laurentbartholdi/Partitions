### Compilation ###

make

### Exécution ###

./dfa [nombre_maximum_etats]

Le premier argument est un maximum : les automates sont parcourus par nombres
d'états croissants, de 1 jusqu'à cette borne incluse. **Chaque langage n'est
imprimé qu'une fois par exécution**, même s'il admet des représentants de tailles
différentes. Un filtre exact des langages est partagé entre toutes les tailles
et tous les modes. Le premier représentant imprimé utilise donc le plus petit
nombre d'états possible dans le mode choisi.

Pour autoriser les transitions non définies :

./dfa [nombre_maximum_etats] --partial

Sans `--partial`, seuls les automates complets sont générés, comme auparavant.
Avec `--partial`, les automates complets et partiels sont générés directement,
accessibles depuis l'état initial, à renommage des états près. Une transition
non définie rejette le mot et n'est pas imprimée. Les états de langage droit vide
sont exclus ; le langage vide est représenté uniquement par un état initial non
final sans transitions. La borne ne compte pas de puits implicite.

Le générateur conserve l'arbre d'accessibilité et autorise une valeur supplémentaire
« non définie » pour chaque autre transition. Il ne génère pas toutes les façons
de supprimer des arêtes d'automates complets, ce qui évite les doublons. Le test de
minimalité vérifie la coaccessibilité puis utilise le raffinement de Moore.

Pour autoriser un ensemble non vide d'états initiaux :

./dfa [nombre_maximum_etats] --multi-initial
./dfa [nombre_maximum_etats] --partial --multi-initial

Un mot est accepté s'il l'est depuis au moins un état initial. Tous les états
sont accessibles depuis l'ensemble des états initiaux, sans exiger qu'un seul
état initial atteigne tous les autres. Le format de sortie indique chaque état
initial par `i0`, `i1`, etc., comme pour les états finaux. Chaque ligne commence
par le nombre d'états du représentant imprimé.

Avec `--multi-initial`, on conserve les automates dont les états ont des langages
droits distincts (et sans états morts en mode partiel). Ce critère local ne suffit
pas à garantir un minimum global. Le parcours croissant des tailles, avec une
clé exacte du langage obtenue par déterminisation, minimisation et numérotation
canonique, assure que seul le premier représentant de chaque langage est imprimé.
Deux exécutions avec des bornes différentes ont le même préfixe de sortie.

Le générateur parcourt directement des forêts d'accessibilité ; un test des
permutations des racines élimine les doublons à renommage près. Le filtre des
langages mémorise une clé par langage imprimé. La déterminisation peut nécessiter
jusqu'à 2^n états : ce mode coûte donc davantage en temps et en mémoire.

Tests : `make test` compare exhaustivement les sorties à une énumération
indépendante pour 1, 2 et 3 états, dans les quatre combinaisons des options.
Il vérifie aussi l'absence de doublons de langage entre tailles, le choix d'un
représentant de taille minimale et la stabilité du préfixe quand la borne augmente.

Les dépendances des fichiers d'en-tête sont générées automatiquement dans les
fichiers `.d` ; `make` recompile les fichiers concernés sans nécessiter `-B`.

### Visualisation ###

Transformer le format DOT en Postscript
dot -Tps dfa.dot > dfa.eps

### Bidouiller le code ###

Enlever l'affichage ASCII:
Commenter la ligne 67 de MainExhaustivDFA.cpp

Modifier l'affichage ASCII:
Fonction ligne 289 de include/DFAAutomaton.hpp

Enlever la conversion en DOT
Commenter la ligne 68 de MainExhaustivDFA.cpp
