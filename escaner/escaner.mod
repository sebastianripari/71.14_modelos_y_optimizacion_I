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
 
dvar int y[Edges][1..2][1..DESTINOS_POR_PASADA] in 0..1;

minimize sum(i in Edges) ( TIEMPO_PROC_CAJA * ( sum(j in 1..DESTINOS_POR_PASADA) (y[i][1][j] + y[i][2][j]) ) );
subject to {
  ctUse0:
    forall(i in Edges) {
      // Unique edge in each level
      sum(j in 1..DESTINOS_POR_PASADA) y[i][1][j] <= 1;
      sum(j in 1..DESTINOS_POR_PASADA) y[i][2][j] <= 1;    
    
      // Should pass through y12 before than y24 or y25
      y[i][1][1] >= y[i][2][1];
      y[i][1][1] >= y[i][2][2]; 
    }
  ctUse1:
   (sum(i in Edges) y[i][2][1]) == CAJAS[1];
   (sum(i in Edges) y[i][2][2]) == CAJAS[2];
   (sum(i in Edges) y[i][1][2]) == CAJAS[3];
}
