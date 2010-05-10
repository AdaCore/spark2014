#include "pricing.h"

int price_of_item (Item it) {
   return mult (it.price, it.number);
}

int price_of_basket (Basket bk, int len) {
   int total = 0;
   int it;
   /*@ loop invariant \forall int k; 0 <= k < it ==> 
                         total >= price_of_item (&bk[it]);
    */
   for (it = 0; it < len; it++) {
      total = add (total, price_of_item (bk[it]));
   }
   return total;
}
