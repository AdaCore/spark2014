package body Use_Ghost2 with SPARK_Mode is

   procedure Main (X : out Integer) is
      Success : Boolean;
   begin
      Do_Stuff (Success);
      if Success then
         X := 1;
      else
         X := 0;
      end if;
   end Main;

end Use_Ghost2;
