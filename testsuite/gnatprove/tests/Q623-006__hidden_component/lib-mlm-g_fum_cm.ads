with Lib.MLM.G_Cm_Par.G_Cm;

generic

   type T_Id is (<>);

package Lib.MLM.G_FUM_Cm is

   package Par is
      new G_Cm_Par (C => 1);

   subtype T_Number is
      Par.T_Number;

   subtype T_Index is
      Par.T_Index;

   package Internal is
     new Par.G_Cm (T_Id => T_Id);

   subtype T_FUM_Cm is Internal.T_M;


end Lib.MLM.G_FUM_Cm;
