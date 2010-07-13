package body C1 is

   procedure Activate (Ret : out Data_Model.Int32_T) is -- (Servant : in out Servant_T) is
      use type Data_Model.Int32_T;
   begin
      C2.I2 (-- Servant.C2_Servant,
             Param_1 => 1,
             Param_2 => Ret);
   end Activate;

end C1;
