procedure Main with SPARK_Mode is
   type T is new Integer;

   function F (B : Boolean) return T with
     Side_Effects,
     Exceptional_Cases => (Program_Error => True);

   function F (B : Boolean) return T is
   begin
      if B then
         return 0;
      else
         raise Program_Error;
      end if;
   end F;

   X : T;
begin
   X := F (False);
exception
   when Program_Error =>
      pragma Assert (X = 1);  --@INITIALIZED:CHECK
end Main;
