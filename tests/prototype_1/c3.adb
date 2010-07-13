package body C3 is

   procedure J1
     (-- Servant : in out Servant_T;
      Param_1 : out Data_Model.Int32_T)
   is
      use type Data_Model.Int32_T;
   begin
      Param_1 := 3;
   end J1;

   procedure J2
     (-- Servant : in out Servant_T;
      Param_1 : out Data_Model.Int32_T) is
      -- pragma Unreferenced (Servant);
      use type Data_Model.Int32_T;
   begin
      Param_1 := 7;
   end J2;

end C3;
