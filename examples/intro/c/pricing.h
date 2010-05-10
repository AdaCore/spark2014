#include "sat.h"

typedef struct _Item {
   int price;
   int number;
} Item;

/*@ predicate type_item{S} (Item* it) =
       0 <= it->price <= 10000 && 0 <= it->number <= 10000;
 */

/*@ logic integer mult (integer x, integer y) = 
       x * y <= 10000 ? x * y : 10000;
 */

/*@ requires type_item (&it);
    ensures \result == mult (it.price, it.number);
 */
int price_of_item (Item it);

/*@ logic integer price_of_item{S} (Item* it) = 
       mult (it->price, it->number);
 */

typedef Item* Basket;

/*@ predicate type_basket{S} (Basket bk, integer len) =
       \forall int it; 0 <= it < len ==> type_item (&bk[it]);
 */

/*@ requires \valid_range(bk, 0, len - 1) && type_basket (bk, len);
    ensures \forall int it; 0 <= it < len ==> 
                               \result >= price_of_item (&bk[it]);
 */
int price_of_basket (Basket bk, int len);
