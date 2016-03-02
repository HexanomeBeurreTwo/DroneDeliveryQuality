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

// Symétrie entre les points
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
	all p1:point | some p2 : point - p1 | p1 in p2.voisin 
}



sig Receptacle extends point { }
one sig Entrepot extends point {}

fact {
	some r: Receptacle | r in Entrepot.voisin 
}

one sig Grille {
	l,h:Int
}

fact {
	{ all r : Receptacle | r.x <= Grille.l and r.y <=Grille.h } and 
	Entrepot.x <= Grille.l and Entrepot.y <= Grille.h
}


check {
	
}

 
run {#Receptacle = 6}  for 12




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













