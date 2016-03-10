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
	coordinate: Point,
	commandes: set Commande -> Time
}

one sig Entrepot {
	coordinate: Point,
	commandes: set Commande -> Time
}

sig Chemin {
	Content: seq Point,
	length : Int
}

sig Drone {
	coordinate : Point one -> Time,
	commande : Commande lone -> Time,
	chemin: Chemin lone -> Time
}

sig Commande {
		destination : one Receptacle
}

sig Time {}



