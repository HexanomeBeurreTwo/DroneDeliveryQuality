open util/integer

open Models
open Predicates
open Helpers

// ===== Points ===== //

// Points unicity
fact { all p1 : Point | no p2 : Point-p1 | p1.x = p2.x and p1.y = p2.y }
// Instance near Points
fact { all p: Point | getNearPoints[p,p.near] }
// Every point is in the grid
fact { all p : Point | p.x <= Grille.l and p.y <=Grille.h and p.x>=0 and p.y>=0 }


// ===== Receptacles ===== //

// Only one receptacle by point
fact { all r1 : Receptacle | no r2 : Receptacle-r1 | r1.coordinate = r2.coordinate }
// All receptacles has a way to the warehouse
fact { all r : Receptacle | hasWayToWarehouse[r]}


// ===== Warehouse ===== //

// No Wharehouse and receptacle on the same point
fact { no r : Receptacle | r.coordinate = Entrepot.coordinate }
// One or more Recept near to the warehouse
fact { some r : Receptacle | isNear[r.coordinate, Entrepot.coordinate] }


// ===== Drones ===== //

// Si deux Drones ont une même postion, alors ils sont tous les deux à l'Entrepot
//fact { all d1 : Drone | d1.coordinate != Entrepot.coordinate => ( no d2 : Drone-d1 | (d1.coordinate = d2.coordinate) ) }
fact { 
	all d1 : Drone | 
	all t:Time | 
	( d1.coordinate.t != Entrepot.coordinate)  => 
		( no d2 : Drone-d1 |  (d1.coordinate.t = d2.coordinate.t) ) 
}


// ===== Ways ===== //

fact {
	{ all ch:Chemin | ch.length = #ch.Content.elems } and
	{ all p : Chemin.Content.elems | { some r: Receptacle | p = r.coordinate } or p = Entrepot.coordinate } and
	{ all ch:Chemin | #ch.Content.elems>= 2 } and
	{ all  chemin:Chemin | not chemin.Content.hasDups } and
	{ all chemin:Chemin | all r1,r2:chemin.Content.elems |
		{  r1 != r2 and chemin.Content.idxOf[r1] =plus[chemin.Content.idxOf[r2] ,1] }  => distance[r1,r2] <= 3
	}
}

//==== Commande ====//
// Deux commande ne peuvent se retrouver en même temps sur même Drone
fact {
	all t : Time | all c1 : Commande |   c1.localisation.t in Drone => ( no c2 : Commande |c1!=c2 and  c2.localisation.t = c1.localisation.t)
}

fact{
	all t: Time | all c:Commande | c.localisation.t in Receptacle => c.localisation.t in c.destination 
}

// livraison <=> localisation
fact {
		all t : Time | all c : Commande | all d : Drone | ( d in c.localisation.t  <=> c in d.livraison.t )
}



// ===== Time Management ===== //

fact {
	/*all t :Time-last | let t' = t.next {
		all c : Commande | 
			c.localisation.t in Drone and c.localisation.t.coordinate.t not in c.destination.coordinate =>
			c.localisation.t' = c.localisation.t
	}*/

}

fact Traces {
    init [first]
    all t: Time-last |
        let t' = t.next {
				all d : Drone | 
						( d.coordinate .t = Entrepot.coordinate and d.livraison.t = none ) => d.coordinate .t' = Entrepot.coordinate
						else  distance[d.coordinate.t', d.coordinate.t] <= 1
	}
    all t: Time-last |
        let t' = t.next {
				all c : Commande | 
						c.localisation.t in Receptacle => c.localisation.t' = c.localisation.t
						else	c.localisation.t in Drone => {
							let d = c.localisation.t |
								 d.coordinate.t in c.destination.coordinate 	=>  ( c.localisation.t' = c.destination and d.livraison.t' = none )
								else  /*c.destination.coordinate != d.coordinate.t =>*/  c.localisation.t' = c.localisation.t
						} else 1>0
		}
				//all d : Drone | distance[d.coordinate.t', d.coordinate.t] <= 1 and 
				//distance[d.coordinate.t', Entrepot.coordinate] <= distance[d.coordinate.t, Entrepot.coordinate]
}


fact Remplissage {
    all t: Time-last |
        let t' = t.next |
			 some d : Drone | 
 				( d.coordinate.t = Entrepot.coordinate and d.livraison.t = none 
				and (lone c : Commande | c.localisation.t = Entrepot ) )
				=> 
				( lone c : Commande | d.coordinate.t' = Entrepot.coordinate and d.livraison.t' = c and  c.localisation.t' = d )		
}






