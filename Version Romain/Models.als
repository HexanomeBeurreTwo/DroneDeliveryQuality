open util/ordering[Time] as to

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
	coordinate: Point
}

one sig Entrepot {
	coordinate: Point
}

sig Chemin {
	Content: seq Point,
	length : Int
}

sig Drone {
	coordinate : Point one -> Time,
	livraison : Commande lone -> Time,
	chemin: Chemin lone -> Time
}

sig Commande {
		destination : one Receptacle,
		localisation : {Receptacle+Entrepot+Drone} one -> Time
}

sig Time {}



