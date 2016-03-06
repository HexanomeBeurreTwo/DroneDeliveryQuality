open util/integer

open Models
open Invariants
open Predicates
open Helpers

// ===== DEBUG ===== //

// il y a pas de temps t où deux Drones différents ont la même coordonnée c, sauf si c = Entrepôt
/*check {
	all d1, d2 : Drone |
	no t:Time | 
	 ( d1 != d2  and  d1.coordinate.t = d2.coordinate.t ) and
	( d1.coordinate.t != Entrepot.coordinate and  d2.coordinate.t != Entrepot.coordinate )
} */


//fact { Entrepot.coordinate.x = 0 and Entrepot.coordinate.y = 0}

/*check {
	no c: Commande | some i,j : Int | i!=j and  Entrepot.commandes[i] =c and  Entrepot.commandes[j] =c
	no i : Int | some c1,c2 : Commande | c1!=c2 and  Entrepot.commandes.c1 =i and  Entrepot.commandes.c2 =i
} */

fact {
	//all t : Time | no d : Drone | d.livraison.t = none and d.coordinate.t not in Entrepot.coordinate 
}



check {
	//all t : Time | all c : Commande | (c.localisation.t in Drone or c.localisation.t in Entrepot or c.localisation.t in Receptacle )
	//some t : Time | some c : Commande | c.localisation.t in Drone and c.localisation.t in Entrepot
	//all t : Time | no d :Drone | (some c1,c2:Commande | c1 !=c2 and d in c1.localisation.t  and  d in c2.localisation.t )
	//no t : Time | 
	//		(some c : Commande |  c.localisation.t in Entrepot) and
	//		(some d : Drone | d.coordinate.t in Entrepot.coordinate) 
	//no t: Time-last | let t' = t.next {
		//( some c : Commande | c.localisation.t  in Drone and c.localisation.t' in c.destination ) 
		//and (some d : Drone | d.coordinate.t in Entrepot.coordinate)
	//}
	//all t : Time | all d : Drone | d.livraison.t = none or d.coordinate.t in Entrepot.coordinate
	
} 

run {
	#Commande = 5
	#Drone = 2 
	#Receptacle = 3 
}  for 5



