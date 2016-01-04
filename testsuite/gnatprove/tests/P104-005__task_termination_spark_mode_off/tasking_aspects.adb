package body Tasking_Aspects is

   task body TT
      with SPARK_Mode => Off
   is
      X     : aliased Integer := 0;
      X_Ptr : access  Integer := X'Access;
   begin
      null;
   end;

end;
