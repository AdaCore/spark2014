package Depends_Illegal_3_Helper
  with SPARK_Mode
is
   G_Var1, G_Var2, G_Var3 : Integer;

   procedure Implicit_Depends (Par1 :        Integer;
                               Par2 :    out Integer;
                               Par3 : in out Integer)
     with Global => (Input  => G_Var1,
                     Output => G_Var2,
                     In_Out => G_Var3);
   --  Since the body of Implicit_Depends will not be provided, callers of
   --  this function will access an implicit depends which will be as follows:
   --     Depends => ((Par2,
   --                  Par3,
   --                  G_Var2,
   --                  G_Var3) => (Par1,
   --                              Par3,
   --                              G_Var1,
   --                              G_Var3))
end Depends_Illegal_3_Helper;
