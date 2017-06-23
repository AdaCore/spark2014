with Lib.MLM.G_FUM_Cm.G_Q;

generic

   type T_Command_Id is (<>);

package Lib.MLM.G_MLMs is

   package Cm is
      new G_FUM_Cm (T_Id => T_Command_Id);

   package All_F is
      new Cm.G_Q;

end Lib.MLM.G_MLMs;
