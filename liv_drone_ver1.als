module livraisonDrone/version1
open util/integer

abstract sig point {
	x,y:Int,
	droite,haut,bas,gauche : lone point,
	voisin = haut + bas + droite + gauche
}

// Tous les points sont diffirents
fact { all pp : point | no p : point-pp | p.x = pp.x and p.y = pp.y }
// Tous le monde est connecté a au moins un voisin et au maximum à 4 voisins
fact { all p: point |  #p.voisin >= 2 and #p.voisin <= 4 }
// Aucun point n'est voisin de lui même
fact { all p : point | not (p in p.voisin) }

// Tous les voisins sont distincts
fact { 
	all p : point | 
		  ( { p.haut != p.bas and p.haut != p.droite and p.haut != p.gauche} or p.haut = none )
	and ( { p.bas != p.haut and p.bas != p.droite and p.bas != p.gauche} or p.bas = none )
	and  ( { p.droite != p.bas and p.droite != p.haut and p.droite != p.gauche} or p.droite = none )
	and ( { p.gauche != p.bas and p.gauche != p.droite and p.gauche != p.haut} or p.gauche = none )
} 

// Contrainte sur X et Y des voisins
fact {
	all p : point | ( p.haut = none or (p.haut.x = p.x  and  p.haut.y = plus[p.y,1] ) ) and 
	(  p.bas = none or (p.bas.x = p.x  and  p.bas.y = minus[p.y,1] ) ) and 
	(  p.droite = none or (p.droite.x = plus[1,p.x]  and  p.droite.y = p.y ) ) and 
	(  p.gauche = none or (p.gauche.x =minus[ p.x,1]  and  p.gauche.y = p.y ) )
}


// Symétrie de la relation de voisinage entre les points
fact {
	( all p: point | all pv : p.voisin | p.haut = pv <=>  pv.bas = p ) and
	( all p: point | all pv : p.voisin | p.bas = pv <=> pv.haut = p ) and
	( all p: point | all pv : p.voisin | p.gauche = pv <=> pv.droite = p ) and
	( all p: point | all pv : p.voisin | p.droite = pv <=> pv.gauche = p ) 
}

//Tous les points sont connectés
fact connectes{
	all p1:point | some connection : point - p1 | p1 in connection.voisin 
}


sig Chemin { Content: seq point , length : Int }
sig Receptacle extends point { }
one sig Entrepot extends point {}

//Au moins un voisin de l'entrepot est un receptacle
fact {
	some r: Receptacle | r in Entrepot.voisin 
}

one sig Grille {
	l,h:Int,	//Dimension de la Grille
	RNB:Int, // nombre de Receptacle
	DNB:Int,// nombre de Drone
}

pred fixerTailleGrille[H,L : Int ]{
	Grille.l = L and
	Grille.h = H
}


pred fixerNbDrone[nb:Int]{
	Grille.DNB = nb and
	#Drone= nb
}

pred fixerNbRecptacle[nb:Int]{
	Grille.RNB = nb and
	#Receptacle = nb
}

//Tous les points sont dans la grille
fact {
	{ all r : Receptacle | r.x <= Grille.l and r.y <=Grille.h and r.x>=0 and r.y>=0} and 
	Entrepot.x <= Grille.l and Entrepot.y <= Grille.h and Entrepot.x>=0 and Entrepot.y>=0
}

//Retourne la valeur absolue d'un entier
fun abs(x: Int): Int{
	x>=0 => x else minus[0,x]
}


//calcule la distance de Manhattan entre deux Intersection 
fun distance[i1,i2: point]: Int {
	abs[i1.x - i2.x].add[abs[i1.y - i2.y]]
}


// Pour chaque receptacle il exite au moins un chemin partant de l'entrepot menant à lui, 
//avec au max une distance de 3 entre chaque deux receptacles successifs, ce chemin n'as pas de cycle
fact CheminMaxDistance3{
	{ all ch:Chemin | ch.length = #ch.Content.elems  }
	and 
	{all p : Chemin.Content.elems | { some r: Receptacle | p = r } or p = Entrepot }
	and 
	{all ch:Chemin | #ch.Content.elems>= 2 }
	and
	{ all chemin:Chemin| all r1,r2:chemin.Content.elems | 
		{  r1 != r2 and chemin.Content.idxOf[r1] =plus[chemin.Content.idxOf[r2] ,1] }  => distance[r1,r2] <= 3 
	}and {
		all  chemin:Chemin | not chemin.Content.hasDups
	}
}

// Chaque receptacle possede un chemin partant de l'entrepot 
fact {
		all  rec:Receptacle | some ch :Chemin |  last[ch.Content] = rec and  first[ch.Content] = Entrepot	
}


pred estIntersection[p:point] {
	p != Receptacle and p != Entrepot 
}

/*check {
	all p : point  { estIntersection[p]  or p = Receptacle or p = Entrepot } 
} */


sig Drone {position : point}

// Si deux Drones ont une même postion, alors ils sont tous les deux à l'Entrepot
fact {
	all d1,d2:Drone {
		 {d1 != d2 and d1.position = d2.position} => {d1.position = Entrepot and d2.position = Entrepot }
	} 
}

/*check UnDroneParPointSaufEntrepot {
	no d1,d2 : Drone  | d1 != d2 and d1.position = d2.position and d1.position != Entrepot and d2.position != Entrepot
}*/

// Compter le nombre de drone à un point donné
/*fun countNbDronePoint[ p : point ] : Int {
	#(p <: Drone.position )  
}*/

/*
fun fixerNbDroneEntrepot: Int { 
	#( Entrepot :> Drone.position  )  
} */


run { 
	fixerTailleGrille[20,20]
	fixerNbRecptacle[5] 
	fixerNbDrone[8]
	//fixerNbDroneEntrepot = 1
}  for 10





