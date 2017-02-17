package body Extended_Returns is

   function Init
     (Discr    : Integer;
      Init_Val : Natural) return Record_T is
   begin
      return Result : Record_T (Discr) do --@RANGE_CHECK:FAIL
         Result.A := Init_Val;

         if Discr = 0 then
            Result.B := Init_Val;
         elsif Discr = 1 then
            Result.C := Init_Val;
            Result.D := Init_Val;
         end if;
      end return;
   end Init;

end Extended_Returns;
