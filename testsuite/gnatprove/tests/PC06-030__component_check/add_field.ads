with Use_Var; use Use_Var;
package Add_Field with SPARK_Mode is

   D : constant Integer := C;

   type Child is new Root with record
      G : Natural range D .. Integer'Last;
   end record;

   type My_Array is array (Positive range <>) of Natural range D .. Integer'Last;

   function Init_Array return My_Array;

   X : My_Array := Init_Array;

   pragma Assert (for all I in X'Range => X (I) >= 0);
end Add_Field;
