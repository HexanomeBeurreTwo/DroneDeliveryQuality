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
	coordinate: Point,
	commandes : seq Commande
}

sig Chemin {
	Content: seq Point,
	length : Int
}

sig Drone {
	coordinate : Point one -> Time,
	livraison : lone Commande
}

sig Commande {
		destination : one Receptacle
}

sig Time {}
