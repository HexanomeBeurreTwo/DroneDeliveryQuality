open util/integer

open Models
open Invariants
open Predicates
open Helpers

/*check {
	all d1, d2 : Drone | ((d1 != d2) and (d1.coordonate = d2.coordonate)) => ((d1.coordonate = Entrepot.coordonate) and (d2.coordonate = Entrepot.coordonate))
}*/

// ===== DEBUG ===== //
fact { Entrepot.coordonate.x = 0 and Entrepot.coordonate.y = 0}

// ===== INIT ===== //
pred init[height, length, droneNb, receptacleNb: Int] {
	Grille.l = length and
	Grille.h = height and
	Grille.DNB = droneNb and
	#Drone= droneNb and
	Grille.RNB = receptacleNb and
	#Receptacle = receptacleNb
}

run {
	init[20,20,8,5]
} for 20
