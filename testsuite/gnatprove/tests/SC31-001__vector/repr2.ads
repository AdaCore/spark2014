with ada.Containers.Formal_Vectors; 
with Ada.Strings.Bounded;

package Repr2 is
   package S is new Ada.Strings.Bounded.Generic_Bounded_Length(Max => 20);
   use S;
   subtype index_t is Natural range 1 .. 100;
   
   package Vec is new Ada.Containers.Formal_Vectors
     (Index_Type => index_t, 
      Element_Type => S.Bounded_String);   
   subtype vec_t is Vec.Vector;
      
end Repr2;
