with Access_To_Constants; use Access_To_Constants;

package Access_To_Constants_2 with SPARK_Mode is
   pragma Elaborate_Body;

   Z : Int_Acc := new Integer'(15);
   Z_2 : constant C_Int_Acc := C_Int_Acc (Z); --  This is a move
end Access_To_Constants_2;
