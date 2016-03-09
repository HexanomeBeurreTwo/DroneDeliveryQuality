open Models

//Retourne la valeur absolue d'un entier
fun abs(x: Int): Int{
	x>=0 => x else minus[0,x]
}

//calcule la distance de Manhattan entre deux Intersection
fun distance[i1,i2: Point]: Int {
	abs[plus[abs[minus[i1.y,i2.y]],abs[minus[i1.x,i2.x]]]]
}

/*fun getNextPosition[i1,i2:Point,t:Time] :Point{ 
	
}*/

// ch' est ch sans son premier élément
pred rest[ch:Chemin,ch':Chemin] {
	ch'.Content = ch.Content.rest and
	ch'.length = minus[ch.length,1]
}

// Chemin entrepot receptacle
pred getWayFromWarehouse[r:Receptacle, ch:Chemin] {
	 last[ch.Content] = r.coordinate and  first[ch.Content] = Entrepot.coordinate 
}

//prvieous 
pred previous[t,t':Time] {
	t.*next = t'
}

check{}





