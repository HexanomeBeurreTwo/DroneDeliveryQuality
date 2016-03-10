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
	//{ all ch:Chemin | #ch.Content.elems>= 2 } and
	{ all  chemin:Chemin | not chemin.Content.hasDups } and
	{ all chemin:Chemin | all r1,r2:chemin.Content.elems |
		{  r1 != r2 and chemin.Content.idxOf[r1] =plus[chemin.Content.idxOf[r2] ,1] }  => distance[r1,r2] <= 3
	}
}

//==== Commande ====//


// == chemin emprunté par un drone ==//
/*fact {
	all  t : Time | 
	all d : Drone |
		d.livraison.t != none and d.coordinate.t in Entrepot.coordinate => {
			some ch:Chemin |  
			last[ch.Content] = d.livraison.t.destination.coordinate and  first[ch.Content] = Entrepot.coordinate and d.chemin.t = ch
		}
}*/		

// ===== Time Management ===== //
/*
fact EvolutionDroneTemps {
    init [first]
    all t: Time-last |
        let t' = t.next |
				all d : Drone | 
						//( d.coordinate .t = Entrepot.coordinate and d.livraison.t = none ) => d.coordinate .t' = Entrepot.coordinate
						//else // distance[d.coordinate.t', d.coordinate.t] <= 1
						//{
							d.coordinate.t != d.chemin.t.Content.last.coordinate =>
							// On its way
							{
								getNextPointInDelivery[d.coordinate.t, d.chemin.t.Content.rest.first.coordinate, d.coordinate.t']
								and ( d.chemin.t.Content.rest.first.coordinate = d.coordinate.t' => {
									getNextChemin[d.chemin.t,d.chemin.t']
									} else {
									d.chemin.t'=d.chemin.t
									}
								)
							}
							// Destination reached 
							else {
								deliverCommand[d, d.chemin.t.Content.last, t, t']
							}
}
*/
/*
fact EvolutionCommandeTemps {
    all t: Time-last |
        let t' = t.next {
				all c : Commande | 
						c.localisation.t in Receptacle => c.localisation.t' = c.localisation.t
						else	c.localisation.t in Drone => {
							let d = c.localisation.t |
								 d.coordinate.t in c.destination.coordinate 	=>  ( c.localisation.t' = c.destination and d.livraison.t' = none )
								//else  c.destination.coordinate != d.coordinate.t =>  c.localisation.t' = c.localisation.t
						} else 1>0
		}
}
*/

//Chargement des commandes sur les Drones
/*fact Remplissage {
    all t: Time-last |
        let t' = t.next |
			 some d : Drone | 
				some c : Commande |
	 				( d.coordinate.t = Entrepot.coordinate and d.commande.t = none  and c in Entrepot.commandes.t )
					=> 
					( d.coordinate.t' = Entrepot.coordinate and d.commande.t' = c
						and let ch = Chemin |  getWayFromWarehouse[c.destination, ch] and d.chemin.t' = ch
						and Entrepot.commandes.t' = Entrepot.commandes.t - c 
					)		
}*/

/*
fact OneDroneForOneCommand {
	all t: Time | all d1: Drone | no d2: Drone - d1 | d1.commande.t = d2.commande.t
}*/


fact OneCommandIsOnlyInOnePlace {
	all t: Time { 
		all d1: Drone | no d2: Drone - d1 | d1.commande.t = d2.commande.t
		all r1: Receptacle | all r2: Receptacle - r1 | no c: Commande | c in r1.commandes.t and c in r2.commandes.t
		all d: Drone | all r: Receptacle | no c: Commande | c = d.commande.t and c in r.commandes.t
		all r: Receptacle| no c: Commande | c in Entrepot.commandes.t and c in r.commandes.t
		all d: Drone| no c: Commande | c in Entrepot.commandes.t and c = d.commande.t
	}
}


// Juste pour la "compilation"
//check {}



