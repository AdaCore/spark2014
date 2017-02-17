with Private_Q; use Private_Q;
package Private_P is
   function F1 return Integer;
   function F2 return Integer;
   function F3 return Integer;
   function F4 return Integer;
private
   function F4 return Integer is (F3 + G3 - 1);
   function F2 return Integer is (F1 + G1 - 1);
   function F1 return Integer is (1);
end Private_P;
