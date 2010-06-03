-----------------------------------------------------------------------------
--  Examples for fix the anonymous type in object declarations or definitions

package Anon_Type is
   type Matrix is array(Integer  range <>, Integer range <>)
   of Integer range 0 .. 10;
   function Increment (Var_In : in Integer) return Integer;
end Anon_Type;

