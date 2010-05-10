/*@ requires 0 <= x <= 10000 && 0 <= y <= 10000;
    ensures (x + y < 10000 && \result == x + y) ||
            (x + y >= 10000 && \result == 10000); 
 */
int add (int x, int y);

/*@ requires 0 <= x <= 10000 && 0 <= y <= 10000;
    ensures (x * y < 10000 && \result == x * y) ||
            (x * y >= 10000 && \result == 10000); 
 */
int mult (int x, int y);
