module Helpers

open Models

//Retourne la valeur absolue d'un entier
fun abs(x: Int): Int{
	x>=0 => x else minus[0,x]
}

//calcule la distance de Manhattan entre deux Intersection
fun distance[i1,i2: Point]: Int {
	abs[plus[abs[minus[i1.y,i2.y]],abs[minus[i1.x,i2.x]]]]
}
