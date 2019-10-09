/*********************************************
 * OPL 12.9.0.0 Model
 * Author: Grupo 5
 * Creation Date: Oct 5, 2019 at 12:41:48 AM
 *********************************************/

/*********************************************
 *                    1
 *                  /   \ 
 *             y11 /     \ y12 
 *                /       \
 *               2         3
 *              / \         
 *         y21 /   \ y22
 *            /     \
 *           4       5    
 *
 * Edges: y12, y13, y24, y25
 *********************************************/

int DESTINOS_POR_PASADA = ...;
int TIEMPO_PROC_CAJA = ...;
int CAJAS[1..3] = ...;
 
int N = 30;
range Edges = 1..N;
 
dvar int y1[Edges][1..DESTINOS_POR_PASADA] in 0..1;
dvar int y2[Edges][1..DESTINOS_POR_PASADA] in 0..1;

minimize sum(i in Edges) ( TIEMPO_PROC_CAJA * ( sum(j in 1..DESTINOS_POR_PASADA) (y1[i][j] + y2[i][j]) ) );
subject to {
  ctUse0:
    forall(i in Edges) {
      // Unique edge in each level
      sum(j in 1..DESTINOS_POR_PASADA) y1[i][j] <= 1;
      sum(j in 1..DESTINOS_POR_PASADA) y2[i][j] <= 1;    
    
      // Should pass through y12 before than y24 or y25
      y1[i][1] >= y2[i][1];
      y1[i][1] >= y2[i][2]; 
    }
  ctUse1:
   (sum(i in Edges) y2[i][1]) == CAJAS[1];
   (sum(i in Edges) y2[i][2]) == CAJAS[2];
   (sum(i in Edges) y1[i][2]) == CAJAS[3];
}
