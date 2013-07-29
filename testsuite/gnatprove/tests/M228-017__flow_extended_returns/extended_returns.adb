package body Extended_Returns
is
   function Init_Record (Discr    : Integer;
                         Init_Val : Natural) return Record_T
   is
   begin
      return Result : Record_T (Discr) do
         Result.A := Init_Val;
         if Discr = 0 then
            Result.B := Init_Val;
         elsif Discr = 1 then
            Result.C := Init_Val;
            Result.D := Init_Val;
         end if;
      end return;
   end Init_Record;


   function Ret_Int (Par : Integer) return Integer
   is
   begin
      return X : Integer do
         if Par > 0 then
            X := 1;
         else
            X := -1;
         end if;
      end return;
   end Ret_Int;


   function Simple_Extended return Natural
   is
   begin
      return Retarded_Var : Natural := 0;
   end Simple_Extended;
end Extended_Returns;
