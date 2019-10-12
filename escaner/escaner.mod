/*********************************************
 * OPL 12.9.0.0 Model
 * Author: Grupo 5
 * Creation Date: Oct 5, 2019 at 12:41:48 AM
 *********************************************/

int CANT_COD_POST = ...;
int DESTINOS_POR_PASADA = ...;
int TIEMPO_PROC_CAJA = ...;
int CAJAS[1..CANT_COD_POST] = ...;

int TECHO_MAX = ftoi(ceil((CANT_COD_POST - 1) / (DESTINOS_POR_PASADA - 1)));

int CANT_NODOS = ftoi((sum(i in 1..TECHO_MAX) pow(DESTINOS_POR_PASADA, i)) + 1);

dvar int CPN[1..CANT_NODOS];
dvar int CPN_MUERTO[1..CANT_NODOS] in 0..1;
dvar int CPN_VIVO[1..CANT_NODOS] in 0..1;

dvar int CODIGO_POSTAL_EN_NODO[1..CANT_COD_POST][1..CANT_NODOS] in 0..1;

/*
Lo que veo que pasa es que:
- En un mismo nivel estamos permitiendo que un CP vaya a mas de un nodo, deberiamos crear una restriccion que permita, por nivel del arbol, mandar un CP a un solo lugar (y no 2,3,4,5...). Hoy esta pasando que A va a 2 y 3 (porque es indistinto de B / C)
- No veo que tengamos una restriccion que fuerze a un CP a aparecer en otro lado mistico para cumplir. Por ejemplo, puede estar en 2 y en el proximo nivel en 6/7. No distinguimos un CP de otro. Asi como forzamos a que aparezca 1 vez por nivel, deberiamos forzarlo a que solo aparezca si el padre lo tiene tambien. (Sino podria aparecer en 2 y despues en 6/7)
*/

int M = 10000000;
int PADRES = ftoi(pow(DESTINOS_POR_PASADA, TECHO_MAX)) - 1;

minimize sum(nodo in 2..CANT_NODOS) sum(cp in 1..CANT_COD_POST) CODIGO_POSTAL_EN_NODO[cp][nodo] * CAJAS[cp];
subject to {
	CONDICION_INICIAL: 
	  CPN[1] == CANT_COD_POST;
	CPN_MUERTO_O_VIVO:
	  forall(nodo in 1..CANT_NODOS) {
	  	CPN_MUERTO[nodo] + CPN_VIVO[nodo] == 1;	  
	  }
	CANT_COD_POSTAL_POR_NODO:
	 forall(nodo in 1..CANT_NODOS) {
	 	 (sum(cp in 1..CANT_COD_POST) CODIGO_POSTAL_EN_NODO[cp][nodo]) == CPN[nodo];
	 } 
	RELACION_COD_POSTAL_PADRE_HIJO:
	  forall(padre in 1..PADRES) {
	  	(CPN_VIVO[padre] == 1) =>	  
	  		(sum(hijo in ((padre * DESTINOS_POR_PASADA) + 1 - DESTINOS_POR_PASADA + 1)..(padre * DESTINOS_POR_PASADA + 1)) CPN[hijo]) == CPN[padre];
	  }
    CANT_COD_POSTAL_MUERTOS:
      forall(nodo in 1..CANT_NODOS) {
         CPN[nodo] <= CPN_MUERTO[nodo] + ((1 - CPN_MUERTO[nodo]) * M);
         CPN[nodo] >= CPN_MUERTO[nodo];
      }
      (sum(nodo in 1..CANT_NODOS) CPN_MUERTO[nodo]) == CANT_COD_POST;
    COD_POSTAL_EN_NIVEL:
      forall(nivel in 1..(TECHO_MAX + 1)) {
        forall(cp in 1..CANT_COD_POST) {
          (sum(nodo in ftoi(pow(DESTINOS_POR_PASADA, nivel - 1))..ftoi(pow(DESTINOS_POR_PASADA, nivel) - 1)) CODIGO_POSTAL_EN_NODO[cp][nodo]) <= 1;        
        }      
      }
}

 
 
 
 
 
 
 
 
 
 
 
 

