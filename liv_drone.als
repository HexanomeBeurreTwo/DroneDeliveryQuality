open util/integer

open Models
open Invariants
open Predicates
open Helpers

/*check {
	all d1, d2 : Drone | ((d1 != d2) and (d1.coordinate = d2.coordinate)) => ((d1.coordinate = Entrepot.coordinate) and (d2.coordinate = Entrepot.coordinate))
}*/

// ===== DEBUG ===== //
//fact { Entrepot.coordinate.x = 0 and Entrepot.coordinate.y = 0}

//sig Time {}

run {#Drone = 2 and #Receptacle = 3 and #Commande = 2
}  for 10
