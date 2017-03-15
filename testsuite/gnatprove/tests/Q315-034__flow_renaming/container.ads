package Container with SPARK_Mode is

   procedure Update_State_X;

   procedure Proxy renames Update_State_X;

   procedure Update_State_X_Via_Proxy;

end;
