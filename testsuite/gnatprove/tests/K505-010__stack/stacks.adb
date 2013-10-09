package body Stacks is
   pragma SPARK_Mode (Off);

   procedure Push (S : in out Stack; E : Element) is
   begin
      if S.Is_Full then
         Error.Set_Erroneous;
         return;
      end if;

      S.Top := S.Top + 1;
      S.Data (S.Top) := E;
   end Push;

   procedure Pop (S : in out Stack) is
   begin
      if S.Is_Empty then
         Error.Set_Erroneous;
         return;
      end if;

      S.Top := S.Top - 1;
   end Pop;

end Stacks;
