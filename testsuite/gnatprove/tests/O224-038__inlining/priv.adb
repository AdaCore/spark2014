package body Priv with SPARK_Mode is

   procedure Set (P : in out Priv_Rec; I : Positive) is
   begin
      if I in 1 .. P.C then
         P.Content (I) := 0;
      end if;
   end Set;

   procedure Init (P : in out Priv_Rec) is
   begin
      for I in 1 .. P.C loop
         Set (P, I); -- This call should not be inlined
      end loop;
   end Init;

end Priv;
