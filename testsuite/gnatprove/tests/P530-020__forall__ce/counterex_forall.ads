----------------------------------------------------------------------------
--  These are test VCs which exercise arrays.
----------------------------------------------------------------------------

package Counterex_forall
is
   type Int_Set     is array (Integer) of Boolean;
   type Int_Int is array (Integer) of Integer;

   function Single_Char_Set_Broken (C : in Integer) return Int_Set
     with Post => (for all I in Integer =>
                     Single_Char_Set_Broken'Result (I) = (I > C));

   procedure Test_Invariant (R : out Int_Int);

end Counterex_forall;
