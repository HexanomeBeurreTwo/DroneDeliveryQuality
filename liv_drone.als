open util/integer

// ===== OBJECTS ===== //
one sig Grille {
	l,h:Int,	//Dimension de la Grille
	RNB:Int, // nombre de Receptacle
	DNB:Int,// nombre de Drone
}

sig Point {
	x,y:Int,
	near: set Point
}

sig Receptacle {
	coordonate: Point
}

one sig Entrepot {
	coordonate: Point
}

sig Chemin {
	Content: seq Point,
	length : Int
}

sig Drone {
	coordonate : Point
}

// ===== FACTS ===== //

// --- Points ---
// Points unicity
fact { all p1 : Point | no p2 : Point-p1 | p1.x = p2.x and p1.y = p2.y }
// Instance neea Points
fact { all p: Point | getNearPoints[p,p.near] }
// Every point is in the grid
fact { all p : Point | p.x <= Grille.l and p.y <=Grille.h and p.x>=0 and p.y>=0 }


// --- Receptacles ---
// Only one receptacle by point
fact { all r1 : Receptacle | no r2 : Receptacle-r1 | r1.coordonate = r2.coordonate }
// All receptacles has a way to the warehouse
fact { all r : Receptacle | hasWayToWarehouse[r]}

// --- Warehouse ---
// No Wharehouse and receptacle on the same point
fact { no r : Receptacle | r.coordonate = Entrepot.coordonate }
// One or more Recept near to the warehouse
fact { some r : Receptacle | isNear[r.coordonate, Entrepot.coordonate] }

// --- Drones ---
// Si deux Drones ont une même postion, alors ils sont tous les deux à l'Entrepot
fact { all d1 : Drone | d1.coordonate != Entrepot.coordonate => ( no d2 : Drone-d1 | (d1.coordonate = d2.coordonate) ) }

// --- Ways ---
fact { 
	{ all ch:Chemin | ch.length = #ch.Content.elems } and
	{ all p : Chemin.Content.elems | { some r: Receptacle | p = r.coordonate } or p = Entrepot.coordonate } and
	{ all ch:Chemin | #ch.Content.elems>= 2 } and
	{ all  chemin:Chemin | not chemin.Content.hasDups } and
	{ all chemin:Chemin | all r1,r2:chemin.Content.elems | 
		{  r1 != r2 and chemin.Content.idxOf[r1] =plus[chemin.Content.idxOf[r2] ,1] }  => distance[r1,r2] <= 3 
	}
}

// ==== PREDICATES ==== //
// Return if two points are near
pred isNear[p1, p2: Point] {
		( p1.x = plus[p2.x,1] and p1.y = p2.y) or ( p1.x = minus[p2.x,1] and p1.y = p2.y) or
		( p1.y = plus[p2.y,1] and p1.x = p2.x) or	( p1.y = minus[p2.y,1] and p1.x = p2.x)
}

// Return a set of near points of p1 in near
pred getNearPoints[p1: Point, near: set Point] {
 all p2 : Point | isNear[p1,p2] => p2 in near else p2 not in near
}

// Return if a warehouse has a way from the warehouses
pred hasWayToWarehouse[r: Receptacle] {
	( distance[r.coordonate, Entrepot.coordonate] <= 3 ) or
	( some ch :Chemin |  last[ch.Content] = r.coordonate and  first[ch.Content] = Entrepot.coordonate )
}


// ===== HELPERS ===== //
//Retourne la valeur absolue d'un entier
fun abs(x: Int): Int{
	x>=0 => x else minus[0,x]
}

//calcule la distance de Manhattan entre deux Intersection 
fun distance[i1,i2: Point]: Int {
	abs[plus[abs[minus[i1.y,i2.y]],abs[minus[i1.x,i2.x]]]]
}

// ===== CHECK ===== //
check {
	all d1, d2 : Drone | ((d1 != d2) and (d1.coordonate = d2.coordonate)) => ((d1.coordonate = Entrepot.coordonate) and (d2.coordonate = Entrepot.coordonate))
}

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





