module Invariants

open Models
open Predicates
open Helpers

// ===== Points =====

// Points unicity
fact { all p1 : Point | no p2 : Point-p1 | p1.x = p2.x and p1.y = p2.y }
// Instance neea Points
fact { all p: Point | getNearPoints[p,p.near] }
// Every point is in the grid
fact { all p : Point | p.x <= Grille.l and p.y <=Grille.h and p.x>=0 and p.y>=0 }


// ===== Receptacles =====

// Only one receptacle by point
fact { all r1 : Receptacle | no r2 : Receptacle-r1 | r1.coordinate = r2.coordinate }
// All receptacles has a way to the warehouse
fact { all r : Receptacle | hasWayToWarehouse[r]}

// ===== Warehouse =====

// No Wharehouse and receptacle on the same point
fact { no r : Receptacle | r.coordinate = Entrepot.coordinate }
// One or more Recept near to the warehouse
fact { some r : Receptacle | isNear[r.coordinate, Entrepot.coordinate] }

// ===== Drones =====

// Si deux Drones ont une même postion, alors ils sont tous les deux à l'Entrepot
//fact { all d1 : Drone | d1.coordinate.t != Entrepot.coordinate => ( no d2 : Drone-d1 | (d1.coordinate = d2.coordinate) ) }

// ===== Ways =====

fact {
	{ all ch:Chemin | ch.length = #ch.Content.elems } and
	{ all p : Chemin.Content.elems | { some r: Receptacle | p = r.coordinate } or p = Entrepot.coordinate } and
	{ all ch:Chemin | #ch.Content.elems>= 2 } and
	{ all  chemin:Chemin | not chemin.Content.hasDups } and
	{ all chemin:Chemin | all r1,r2:chemin.Content.elems |
		{  r1 != r2 and chemin.Content.idxOf[r1] =plus[chemin.Content.idxOf[r2] ,1] }  => distance[r1,r2] <= 3
	}
}

// ===== DELIVERIES =====//
fact UnDroneParCommande {
	all d1, d2:Drone | d1!=d2 => d1.livraison!=d2.livraison
}

// ===== TIME ===== //

fact Traces {
    init [first]
    all t: Time-last |
        let t' = t.next |
				all d : Drone | distance[d.coordinate.t', d.coordinate.t] = 1
				//all d : Drone | distance[d.coordinate.t', d.coordinate.t] = 1 and distance[d.coordinate.t', Entrepot.coordinate] <= distance[d.coordinate.t, Entrepot.coordinate] 
}
