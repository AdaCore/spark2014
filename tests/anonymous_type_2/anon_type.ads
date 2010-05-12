------------------------------------------------------------------------------
--  Test the anonymous type in constrained_array_definition,
--  discrete_subtype_definition and component_definition

package Anon_Type
is
   subtype Index is Integer range 0 .. 4;
   subtype Value is Integer range 0 .. 9;
   type Array1 is array (Index) of Value;
   type Array2 is array (Integer range 5 .. 9) of Integer range 0 .. 9;
   type Array3 is array (Integer range <>) of Integer;
   procedure exchange(A1 : out Array1; A2 : out Array2);
end Anon_Type;

