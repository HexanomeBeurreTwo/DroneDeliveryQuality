open util/integer

open Models
open Invariants
open Predicates
open Helpers

run {
	#Commande = 3
	#Drone = 2 
	#Receptacle = 3 
	some d : Drone | some t : Time | d.chemin.t.length > 3
}  for 5 



