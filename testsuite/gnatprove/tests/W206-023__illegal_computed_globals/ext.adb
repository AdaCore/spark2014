package body Ext with SPARK_Mode => Off is
   function Read_And_Write_X return Integer is
   begin
      X := X+ 1;
      return X;
   end Read_And_Write_X;
   function Read_Y return Integer is
   begin
      return Y;
   end Read_Y;
   function Read_Z return Integer is
   begin
      return Z;
   end Read_Z;
end Ext;
