with Reorder_Q; use Reorder_Q;
package Reorder_P is 
   function F1 return Integer;
   function F2 return Integer is (F1 + G1 - 1);
   function F3 return Integer;
   function F4 return Integer is (F3 + G3 - 1);
private
   function F1 return Integer is (1);
end Reorder_P;
