package body Raise_Statements is
   procedure Returning_Proc is
   begin
      if G < Integer'Last then
         G := G + 1;
      else
         G := Integer'First;
      end if;
   end Returning_Proc;

   procedure Non_Returning_Proc (Par : Integer) is
   begin
      loop
         G := Par;
      end loop;
   end Non_Returning_Proc;

   procedure OK_1 (Par1 : in out Integer;
                   Par2 : in     Integer)
   is
   begin
      if Par2 = 0 then
         Returning_Proc;
         pragma Assert (False);
         Returning_Proc;
         return;
      elsif Par2 = 1 then
         Returning_Proc;
         raise Program_Error;
         Returning_Proc;
      else
         Par1 := Par1 + Par2 - 3;
         return;
      end if;

      Non_Returning_Proc (Par1);
   end OK_1;

   procedure OK_2 (Par : Integer) is
   begin
      if Par > 0 then
         G := 1;
      end if;

      if Par = 0 then
         Non_Returning_Proc (Par);
      end if;
   end OK_2;

   procedure OK_3 (OK : Boolean) is
   begin
      if OK then
         G := 1;
      else
         if G = 0 then
            G := 2;
         end if;
         pragma Assert (False);
         G2 := 1;
      end if;
   end OK_3;

   procedure Foo (A : Boolean;
                  O : out Integer)
   with Depends => (O => A)
   is
   begin
      if A then
         O := 12;
      else
         raise Program_Error;
      end if;
   end Foo;
end Raise_Statements;
