generic

   C : in Integer;

package Lib.MLM.G_Cm_Par is

   subtype T_Number is
      Integer range 0 .. C;

   subtype T_Index is
      Integer range 1 .. C;

end Lib.MLM.G_Cm_Par;
