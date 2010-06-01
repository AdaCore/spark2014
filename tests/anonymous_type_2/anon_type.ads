------------------------------------------------------------------------------
--  Test the anonymous type in constrained_array_definition,

package Anon_Type
is
   subtype Index is Integer range 0 .. 4;
   subtype Value is Integer range 0 .. 9;
   type Array1 is array (Index) of Value;
   type Array2 is array (Integer range 5 .. 9) of Integer range 0 .. 9;
   Size : constant Integer :=10;
   type Array3 is array(1 .. Size) of Value;
   type Array4 is array (1 .. 10) of Value;
   type Array5 is array (1 .. 10, 1 .. 10) of Value;

   procedure Exchange(A1 : out Array1; A2 : out Array2;
                      A3 : out Array3; A4 : out Array4);
end Anon_Type;

