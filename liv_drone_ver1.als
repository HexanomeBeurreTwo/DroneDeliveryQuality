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
fact { all p: point |  #p.voisin >= 1 and #p.voisin <= 4 }
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

/*
check position {
	{ all p1 : point | all p2 : point - p1 | p1.bas = p2 <=> p1.x = p2.x and p2.y = minus[ p1.y ,1] } and 
	{ all p1 : point | all p2 : point - p1 | p1.haut = p2 <=> p1.x = p2.x and p2.y = plus[ p1.y ,1] }	and 
	{ all p1 : point | all p2 : point - p1 | p1.gauche = p2 <=> p1.x = plus[ p2.x,1] and p2.y = p1.y } and
	{ all p1 : point | all p2 : point - p1 | p1.droite = p2 <=> p1.x = minus[ p2.x,1] and p2.y = p1.y }

}
*/

// Symétrie de la relation de voisinage entre les points
fact {
	( all p: point | all pv : p.voisin | p.haut = pv <=>  pv.bas = p ) and
	( all p: point | all pv : p.voisin | p.bas = pv <=> pv.haut = p ) and
	( all p: point | all pv : p.voisin | p.gauche = pv <=> pv.droite = p ) and
	( all p: point | all pv : p.voisin | p.droite = pv <=> pv.gauche = p ) 
}
/*
assert voisinageSymetrique {
	{ all p1 : point | all p2 : point - p1 | p1.bas = p2 <=>p1= p2.haut  and p2 in p1.voisin and p1 in p2.voisin} and 
	{ all p1 : point | all p2 : point - p1 | p1.gauche = p2 <=>p1= p2.droite  and p2 in p1.voisin and p1 in p2.voisin} 
}

check voisinageSymetrique*/

fact connectes{
	all p1:point | some connection : point - p1 | p1 in connection.voisin 
}



sig Receptacle extends point { chemin : seq point }
one sig Entrepot extends point {}

/*
fact {
	lone r: Receptacle | r in Entrepot.voisin 
}*/

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

/*
//on peut avoir une distance > 3 entre receptacles qui sont pas dans le même chemin
fact distanceEntreReceptacles {
	all r1:Receptacle | some r2 : Receptacle - r1 |plus[ abs[minus[r1.x, r2.x]], abs[minus[r1.y,r2.y]]] <=3   
}
*/
/*
//verification de distanceEntreReceptacles->ok
check{
	some r1,r2:Receptacle |  abs[minus[r1.x , r2.x]] <=3  or abs[minus[r1.y , r2.y]] <=3
} 
*/

//calcule la distance de Manhattan entre deux Intersection 
fun distance[i1,i2: point]: Int {
	abs[i1.x - i2.x].add[abs[i1.y - i2.y]]
}


 
//il faut trouver le chemin qui est une suite de receptacle entre l'entrepot et la destination
/*fact Chemin { 
	all rec: Receptacle | let chemin = rec.chemin |
	not chemin.hasDups and
	chemin.first= Entrepot and last[chemin] = rec
	and all r1 :chemin.elems | some r2: chemin.elems-r1 | 
	let i1 = chemin.idxOf[r1] , i2 = chemin.idxOf[r2] | 
	i1=plus[i2,1] => distance[r1,r2]<=3 	
	
}*/

// Pour chaque receptacle il exite au moins un chemin partant de l'entrepot menant à lui, 
//avec au max une distance de 3 entre chaque deux receptacles successifs, ce chemin n'as pas de cycle
fact CheminEntrepotReceptacle{
	{ 
		all rec:Receptacle | all r1,r2:rec.chemin.elems-rec | 
		{  r1 != r2 and rec.chemin.idxOf[r1] =plus[rec. chemin.idxOf[r2] ,1] }  => distance[r1,r2] <= 3 
	}and {
		all rec:Receptacle |  last[rec.chemin] = rec and  first[rec.chemin] = Entrepot	
	}and {
		all rec:Receptacle | not rec.chemin.hasDups
	}
}

pred fixerLongChemin[long:Int]{
	 { some r:Receptacle | #r.chemin > long}
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
fun countNbDronePoint[ p : point ] : Int {
	#(p <: Drone.position )  
}

fun fixerNbDroneEntrepot: Int { 
	#( Entrepot :> Drone.position  )  
}


run { 
	fixerTailleGrille[20,20]
	fixerNbRecptacle[5] 
	fixerNbDrone[8]
	//fixerNbDroneEntrepot = 1
	fixerLongChemin[5]
}  for 10




// [TEST] juste une petite régle de production	
//check { no p:point | #p.voisin >=2 } for 10

//[TEST]  une deuxieme regle de production 
//pred estVoisin[p1,p2:point] { p1 in p2.voisin }
//run estVoisin for 7


 /*

sig Drone { Position_du_Drone : point }
sig Receptable { Position_du_Receptable : point, Drone_ds_Recptable : Drone }
one sig Entrepot {Position_du_Entrepot : point , Drone_ds_Entrepot : set Drone}

//let Drones = set Drone 
//let Receptables = set Receptable

fact {
	all r : Receptable | r.Position_du_Receptable != Entrepot.Position_du_Entrepot 
	and r.Drone_ds_Recptable != Entrepot.Drone_ds_Entrepot
}

fact {
	{all d:Drone | Entrepot. Position_du_Entrepot = d.Position_du_Drone =>
				 ( no res : Receptable | res.Position_du_Receptable =  d.Position_du_Drone)  } and 
	{ all r:Entrepot | all d:Drone | r.Drone_ds_Entrepot = d => r.Position_du_Entrepot = d.Position_du_Drone } and
	{ all r:Receptable | all d:Drone | r.Drone_ds_Recptable = d => r.Position_du_Receptable = d.Position_du_Drone } 
}

fact {
	all r : Receptable | no rr : Receptable-r | r.Position_du_Receptable = rr.Position_du_Receptable 
}

fact {
	all d : Drone | no dd : Drone -d | d.Position_du_Drone = dd.Position_du_Drone
}

fact{
	all d: Entrepot.Drone_ds_Entrepot | no rs : Receptable | rs.Drone_ds_Recptable = d 
}

fact{
	all d : Drone | d.Position_du_Drone = Entrepot. Position_du_Entrepot <=> d in Entrepot.Drone_ds_Entrepot
}

/*
run {
	#Entrepot = 1
	and #Drone = 0
	and #Receptable = 6
} for 25
*/
