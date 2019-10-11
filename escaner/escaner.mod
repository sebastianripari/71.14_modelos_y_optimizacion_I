/*********************************************
 * OPL 12.9.0.0 Model
 * Author: Grupo 5
 * Creation Date: Oct 5, 2019 at 12:41:48 AM
 *********************************************/

/*********************************************
 *                     1
 *                  /     \ 
 *             y11 /       \ y12 
 *                /         \
 *               2           3
 *              / \         / \ 
 *         y21 /   \y22 y31/   \y32 
 *            /     \     /     \
 *           4       5   7       6
 *
 * Edges: y12, y13, y24, y25
 *********************************************/

int DESTINOS_POR_PASADA = ...;
int TIEMPO_PROC_CAJA = ...;
int CAJAS[1..3] = ...;
 
int N = 30;
range Edges = 1..N;

int M = 10000000;
 
dvar int y[Edges][1..3][1..DESTINOS_POR_PASADA] in 0..1;
dvar int f[1..3][1..3][1..DESTINOS_POR_PASADA] in 0..1;

minimize sum(i in Edges) ( TIEMPO_PROC_CAJA * ( sum(j in 1..3) sum(k in 1..DESTINOS_POR_PASADA) (y[i][j][k]) ) );
subject to {
  ctUse0:
    forall(i in Edges) {
      // Unique edge in each level
      sum(j in 1..DESTINOS_POR_PASADA) y[i][1][j] <= 1;
      sum(j in 1..DESTINOS_POR_PASADA) y[i][2][j] <= 1;
      sum(j in 1..DESTINOS_POR_PASADA) y[i][3][j] <= 1;    
    
      // Should pass through y12 before than y24 or y25
      forall(j in 1..DESTINOS_POR_PASADA) y[i][1][1] >= y[i][2*1][j];   
      forall(j in 1..DESTINOS_POR_PASADA) y[i][1][2] >= y[i][2*1 + 1][j];   
    }
  ctUse1:
   forall(j in 1..3) {
      forall(k in 1..2) {
        (sum(i in Edges) y[i][j][k]) <= 10 * f[1][j][k] + (1 - f[1][j][k]) * M;
        (sum(i in Edges) y[i][j][k]) >= 10 * f[2][j][k] - (1 - f[2][j][k]) * M;
        
        f[1][j][k] + f[2][j][k] >= 2 * f[3][j][k];
        f[1][j][k] + f[2][j][k] <= 1 + f[3][j][k];
      }            
   }
   ( sum(j in 1..3) sum(k in 1..2) f[3][j][k] ) == 3;
}
