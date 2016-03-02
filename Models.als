module Models

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
