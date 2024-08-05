with P2; use P2;
with P3;
package P1.Child is
   function F1 return Boolean;
   function F2 return Boolean with Post => F2'Result;
private
   function R return P2.List with Import;
   function F1 return Boolean is (R = null or else R.V1 /= 0);
   function F2 return Boolean is (R = null or else P3.OK (R.V2));
end P1.Child;
