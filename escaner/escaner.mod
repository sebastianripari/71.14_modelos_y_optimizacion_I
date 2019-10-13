/*********************************************
 * OPL 12.9.0.0 Model
 * Author: Grupo 5
 * Creation Date: Oct 5, 2019 at 12:41:48 AM
 *********************************************/

int CANT_COD_POST = ...;
int DESTINOS_POR_PASADA = ...;
int TIEMPO_PROC_CAJA = ...;
int CAJAS[1..CANT_COD_POST] = ...;

int NIVELES_ARBOL = ftoi(ceil((CANT_COD_POST - 1) / (DESTINOS_POR_PASADA - 1)));

int CANT_NODOS = ftoi((sum(i in 1..NIVELES_ARBOL) pow(DESTINOS_POR_PASADA, i)) + 1);

dvar int CANTIDAD_CODIGOS_POSTALES_EN_NODO[1..CANT_NODOS];
dvar int ENVIA_CODIGO_POSTAL[1..CANT_NODOS] in 0..1;
dvar int ESCANEA_CODIGOS_POSTALES[1..CANT_NODOS] in 0..1;

dvar int CODIGO_POSTAL_EN_NODO[1..CANT_COD_POST][1..CANT_NODOS] in 0..1;

int M = 10000000;
int CANTIDAD_NODOS_PADRE = (CANT_NODOS - ftoi(pow(DESTINOS_POR_PASADA, NIVELES_ARBOL)));

minimize sum(nodo in 2..CANT_NODOS) sum(cp in 1..CANT_COD_POST) CODIGO_POSTAL_EN_NODO[cp][nodo] * CAJAS[cp] * TIEMPO_PROC_CAJA;
subject to {
	CONDICION_INICIAL: 
	  CANTIDAD_CODIGOS_POSTALES_EN_NODO[1] == CANT_COD_POST;
	CPN_MUERTO_O_VIVO:
	  forall(nodo in 1..CANT_NODOS) {
	  	ENVIA_CODIGO_POSTAL[nodo] + ESCANEA_CODIGOS_POSTALES[nodo] == 1;	  
	  }
	CANT_COD_POSTAL_POR_NODO:
	 forall(nodo in 1..CANT_NODOS) {
	 	 (sum(cp in 1..CANT_COD_POST) CODIGO_POSTAL_EN_NODO[cp][nodo]) == CANTIDAD_CODIGOS_POSTALES_EN_NODO[nodo];
	 } 
	RELACION_COD_POSTAL_PADRE_HIJO:
	  forall(padre in 1..CANTIDAD_NODOS_PADRE) {
	  	(ESCANEA_CODIGOS_POSTALES[padre] == 1) =>	  
	  		(sum(hijo in ((padre * DESTINOS_POR_PASADA) + 1 - DESTINOS_POR_PASADA + 1)..(padre * DESTINOS_POR_PASADA + 1)) CANTIDAD_CODIGOS_POSTALES_EN_NODO[hijo]) == CANTIDAD_CODIGOS_POSTALES_EN_NODO[padre];
	  }
    CANT_COD_POSTAL_MUERTOS:
      forall(nodo in 1..CANT_NODOS) {
         CANTIDAD_CODIGOS_POSTALES_EN_NODO[nodo] <= ENVIA_CODIGO_POSTAL[nodo] + ((1 - ENVIA_CODIGO_POSTAL[nodo]) * M);
         CANTIDAD_CODIGOS_POSTALES_EN_NODO[nodo] >= ENVIA_CODIGO_POSTAL[nodo];
      }
      (sum(nodo in 1..CANT_NODOS) ENVIA_CODIGO_POSTAL[nodo]) == CANT_COD_POST;
    COD_POSTAL_FORWARDING:
      // Esta rule valida no solo que los hijos tengan al del padre, sino tambien que solo aparezca 1 vez cada uno por nivel (porque justamente viene dado implicitamente)
      forall(cp in 1..CANT_COD_POST) {
        forall(padre in 1..CANTIDAD_NODOS_PADRE) {
	  	  (ESCANEA_CODIGOS_POSTALES[padre] == 1) =>	  
	  	    	(sum(hijo in ((padre * DESTINOS_POR_PASADA) + 1 - DESTINOS_POR_PASADA + 1)..(padre * DESTINOS_POR_PASADA + 1)) CODIGO_POSTAL_EN_NODO[cp][hijo]) == CODIGO_POSTAL_EN_NODO[cp][padre];
	    }
 	  }	  
}

 
 
 
 
 
 
 
 
 
 
 
 

