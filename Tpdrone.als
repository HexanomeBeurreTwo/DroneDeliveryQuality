//permet de faire des sommes, des produits...
open util/integer

// Carte d'intersections
sig Carte { carte : set Point }

//limites des points sur la carte
sig Point {x, y: Int} {
x<11
y<11
}

//des receptacles
sig Receptacle{pt : Point}

// il y a un seul entrepot
one sig Entrepot extends Receptacle{}

//des drones
sig Drone{
coord :  Point,
dest : Receptacle
}

//valeur absolue d'un nombre
fun abs[x: Int]: Int {
	x >= 0 => x else x.mul[-1]
}

//calcule la distance de Manhattan entre deux Intersection 
fun distance[i1,i2: Point]: Int {
	abs[i1.x - i2.x].add[abs[i1.y - i2.y]]
}

 //il faut au moins un voisin receptacle de l'entrepot
fact voisin {some r: Receptacle, e : Entrepot | distance[r.pt, e.pt]=<3}

//les receptacles ne sont pas sur le meme point que l'entrepot 
fact diff {all r : Receptacle, e: Entrepot | r.pt != e.pt}
//les receptacles ne peuvent être sur un meme point
fact diffRec { all r1, r2 : Receptacle | r1.pt != r2.pt}

//il faut trouver le chemin qui est une suite de receptacle entre l'entrepot et la destination
fact Chemin { 
	all r: Receptacle, e: Entrepot | 
	some chemin: set Receptacle | 
	r in chemin && e in chemin && all r1,r2: chemin | distance[r1.pt, r2.pt] <= 3 
}

pred test  {
	one e:Entrepot | all d:Drone |d.coord = e.pt
	one r1 : Receptacle | r1.pt.x = 5 && r1.pt.y=5

}

run test for exactly 3 Drone, 4 Receptacle, 1 Carte, 100 Point
