procedure Main with Always_Terminates is
   type TF is access function return Boolean;

   function F return Boolean is
      function FF return Boolean with Pre => True is
         X : TF := F'Access;  --@TERMINATION:FAIL
      begin
         return X.all;
      end;

   begin
      return FF;
   end;

   Y : Boolean := F;
begin
   null;
end;
