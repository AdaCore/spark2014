pragma Extensions_Allowed (All_Extensions);

procedure Main
  with SPARK_Mode
is

   procedure P (X : aliased out Integer)
     with Exceptional_Cases => (Program_Error => X = 3)
   is
   begin
      begin
         X := 1;
         return;
      finally
         X := 2;
         if (X > 0) then
            raise Program_Error;
         end if;
      end;
   finally
      X := 3;
   end;

   Z : aliased Integer;
begin
   P (Z);
exception
   when Program_Error =>
      pragma Assert (Z = 3);
end;
