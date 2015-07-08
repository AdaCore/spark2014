with System;

procedure Addr
  with SPARK_Mode
is
   procedure Do_Stuff (A : System.Address) is
   begin
      null;
   end Do_Stuff;
   X : Integer;
begin
   Do_Stuff (X'Address);
end Addr;
