with State;

package body Container with SPARK_Mode => Off is

   procedure Update_State_X is
   begin
      State.Flip;
   end;

   procedure Update_State_X_Via_Proxy is
   begin
      Proxy;
   end;

end;
