/*********************************************
 * OPL 12.9.0.0 Model
 * Author: Grupo 5
 * Creation Date: Oct 5, 2019 at 12:41:48 AM
 *********************************************/
 
int CANT_COD_POST = 3; //Hardcode

int DESTINOS_POR_PASADA = ...;
int TIEMPO_PROC_CAJA = ...;
int CAJAS[0..CANT_COD_POST - 1] = ...;

int TECHO_MAX = ftoi(ceil((CANT_COD_POST - 1) / (DESTINOS_POR_PASADA - 1)));

int CANT_NODOS = ftoi((sum(i in 1..TECHO_MAX) pow(DESTINOS_POR_PASADA, i)) + 1);

dvar int CPN[1..CANT_NODOS];
dvar int CPN_MUERTO[1..CANT_NODOS] in 0..1;

dvar int CODIGO_POSTAL_EN_NODO[0..(CANT_COD_POST - 1)][1..CANT_NODOS] in 0..1;

int M = 10000000;

range seba = 1..2;

minimize sum(nodo in 2..CANT_NODOS) sum(cp in 0..(CANT_COD_POST - 1)) CODIGO_POSTAL_EN_NODO[cp][nodo] * CAJAS[cp];
subject to {
	CONDICION_INICIAL: 
	  CPN[1] == CANT_COD_POST;
	CANT_COD_POSTAL_POR_NODO:
	 forall(nodo in 1..CANT_NODOS) {
	 	 (sum(cp in 0..(CANT_COD_POST - 1)) CODIGO_POSTAL_EN_NODO[cp][nodo]) == CPN[nodo];
	 } 
	RELACION_COD_POSTAL_PADRE_HIJO:
	  forall(padre in 1..(CANT_NODOS - ftoi(pow(DESTINOS_POR_PASADA, TECHO_MAX + 1)))) {
	  	  (sum(hijo in ((padre * DESTINOS_POR_PASADA) + 1 - DESTINOS_POR_PASADA + 1)..(padre * DESTINOS_POR_PASADA + 1)) CPN[hijo - 1]) == CPN[padre - 1];
	  }
    CANT_COD_POSTAL_MUERTOS:
      forall(nodo in 1..CANT_NODOS) {
         CPN[nodo] <= CPN_MUERTO[nodo] + ((1 - CPN_MUERTO[nodo]) * M);
         CPN[nodo] >= CPN_MUERTO[nodo];
      }
      (sum(nodo in 1..CANT_NODOS) CPN_MUERTO[nodo]) == CANT_COD_POST;
}

 
 
 
 
 
 
 
 
 
 
 
 

