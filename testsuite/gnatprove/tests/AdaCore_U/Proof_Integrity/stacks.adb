package body Stacks with SPARK_Mode is
   procedure Push (S : in out Stack; E : Natural) is
   begin
      if S.Top >= Max then
         raise Is_Full_E;
      end if;

      S.Top := S.Top + 1;
      S.Content (S.Top) := E;
   end Push;
end Stacks;
