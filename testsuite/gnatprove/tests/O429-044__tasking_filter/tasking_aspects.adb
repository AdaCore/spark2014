package body Tasking_Aspects is

   protected body PT_With_Entry_Aspect is
      entry Dummy
         with SPARK_Mode => Off
      when True
      is
         X : aliased Integer := 0;
         X_Ptr : access Integer := X'Access;
      begin
         null;
      end;
   end;

   task body TT
      with SPARK_Mode => Off
   is
      X : aliased Integer := 0;
      X_Ptr : access Integer := X'Access;
   begin
      null;
   end;

end;
