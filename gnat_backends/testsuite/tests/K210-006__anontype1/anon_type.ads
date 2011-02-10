-----------------------------------------------------------------------------
--  Examples for fix the anonymous type in object declarations or definitions

package Anon_Type is
   type Vector is array(Integer range <>) of Float;
   function Increment (Var_In : in Integer) return Integer;
end Anon_Type;

