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
 
int TIEMPO_PROC_CAJA = ...;
int CAJAS[1..3] = ...;
 
int N = 30;
range Edges = 1..N;
 
dvar int y11[Edges] in 0..1;
dvar int y12[Edges] in 0..1;
dvar int y21[Edges] in 0..1;
dvar int y22[Edges] in 0..1;

minimize sum(i in Edges) ( TIEMPO_PROC_CAJA * ( y11[i] + y12[i] + y21[i] + y22[i]) );
subject to {
  ctUse0:
    forall(i in Edges) {
      // Unique edge in each level
      y11[i] + y12[i] <= 1;
      y21[i] + y22[i] <= 1;    
    
      // Should pass through y12 before than y24 or y25
      y11[i] >= y21[i];
      y11[i] >= y22[i]; 
    }
  ctUse1:
   (sum(i in Edges) y21[i]) == CAJAS[1];
   (sum(i in Edges) y22[i]) == CAJAS[2];
   (sum(i in Edges) y12[i]) == CAJAS[3];
}
