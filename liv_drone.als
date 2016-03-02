module version1

open util/integer

open Models
open Invariants
open Predicates
open Helpers

// ===== INIT ===== //
/*
pred initGrid [height, length, droneNb, receptacleNb, deliveryNb: Int] {
	Grille.l = length and
	Grille.h = height and
	Grille.DNB = droneNb and
	#Drone= droneNb and
	Grille.RNB = receptacleNb and
	#Receptacle = receptacleNb
	#Commande = deliveryNb
}
*/

assert Remplissage {
	all d:Drone | all t:Time | d.coordinate.t = Entrepot.coordinate
					  	 and #d.livraison = 0 
					 	 and #Entrepot.commandes > 0 => d.livraison = Entrepot.commandes.first 
																		 		  and Entrepot.commandes = Entrepot.commandes.rest
}

// ===== CHECK ===== //
/*check {
	all d1, d2 : Drone | ((d1 != d2) and (d1.coordinate = d2.coordinate)) => ((d1.coordinate = Entrepot.coordinate) and (d2.coordinate = Entrepot.coordinate))
}*/
//check UnDroneParCommande {}

// ===== DEBUG ===== //
fact { Entrepot.coordinate.x = 0 and Entrepot.coordinate.y = 0}

run {
	//initGrid[15,15,8,5,3]
	#Drone = 2 and #Receptacle = 3 and #Commande = 2
}  for 10

/*
run {
	//initGrid[15,15,8,5,3]
	#Drone =
} for 20
*/
