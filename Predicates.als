module Predicates

open Models
open Helpers

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
