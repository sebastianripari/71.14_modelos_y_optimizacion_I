/*********************************************
 * OPL 12.9.0.0 Model
 * Author: Grupo 5
 * Creation Date: Oct 5, 2019 at 12:41:48 AM
 *********************************************/

/*********************************************
 *                    1
 *                  /   \ 
 *             y12 /     \ y13 
 *                /       \
 *               2         3
 *              / \         
 *         y24 /   \ y25
 *            /     \
 *           4       5    
 *
 * Edges: y12, y13, y24, y25
 *********************************************/
 
int TIEMPO_PROC_CAJA = ...;
 
int N = 30;
range Edges = 1..N;
 
dvar int y12[Edges] in 0..1;
dvar int y13[Edges] in 0..1;
dvar int y24[Edges] in 0..1;
dvar int y25[Edges] in 0..1;

minimize sum(i in Edges) ( TIEMPO_PROC_CAJA * ( y12[i] + y13[i] + y24[i] + y25[i]) );
subject to {
  ctUse0:
    forall(i in Edges) {
      // Unique edge in each level
      y12[i] + y13[i] <= 1;
      y24[i] + y25[i] <= 1;    
    
      // Should pass through y12 before than y24 or y25
      y12[i] >= y24[i];
      y12[i] >= y25[i]; 
    }
  ctUse1:
   (sum(i in Edges) y13[i]) == 10;
   (sum(i in Edges) y24[i]) == 10;
   (sum(i in Edges) y25[i]) == 10;
}
