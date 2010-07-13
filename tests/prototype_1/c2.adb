package body C2 is

   procedure I1
     (-- Servant : in out Servant_T;
      Param_1 : in Data_Model.Int32_T;
      Param_2 : in Data_Model.Int32_T; -- out
      Param_3 : out Data_Model.Int32_T)
   is
      use type Data_Model.Int32_T;
   begin
      Param_3 := Param_1 + Param_2;
   end I1;

   procedure I2
     (-- Servant : in out Servant_T;
      Param_1 : in Data_Model.Int32_T;
      Param_2 : out Data_Model.Int32_T)
   is
      use type Data_Model.Int32_T;
      P1, P2 : Data_Model.Int32_T;
   begin
      C3.J1 (-- Servant.C3_Servant,
             Param_1 => P1);
      C3.J2 (-- Servant.C3_Servant,
             Param_1 => P2);
      Param_2 := Param_1 + P1 + P2;
   end I2;

end C2;
