package body Record_Discr with SPARK_Mode is

   function Search_Upto_3 (R : Result_3; E : Natural) return Result_Ty is
   begin
      pragma Assert (R.UpTo = 3);
      if R.To_Search (1) = E then
         return Mk_Result (True, 1);
      elsif R.To_Search (2) = E then
         return Mk_Result (True, 2);
      elsif R.To_Search (3) = E then
         return Mk_Result (True, 3);
      else
         return Mk_Result (False);
      end if;
   end Search_Upto_3;

   function Search_Upto (R : Interm_Result; E : Natural) return Result_Ty is
      type My_Res is new Result_Ty (R.Upto /= 0);
      type Res_False is new Result_Ty (False);

      function Bad (R : Result_Ty) return Res_False;
      function Bad (R : Result_Ty) return Res_False is
      begin
	 return Res_False (R); -- @DISCRIMINANT_CHECK:FAIL
      end Bad;

      Result : constant Result_Ty :=
        Mk_Result (Found => (R.Upto /= 0), Content =>
                        (if R.Upto = 0 then 1 else R.Upto));

      Result1 : constant My_Res := My_Res (Result);
      Result1_Base : constant Result_Ty := Result_Ty (Result1);
   begin
      if R.Upto = 0 or else R.To_Search (R.Upto) = E then
         return Result1_Base;
      else
         return Search_Upto
           (R => (UpTo      => R.UpTo - 1,
                  To_Search => R.To_Search (1 .. (R.Upto - 1))),
            E => E);
      end if;
   end Search_Upto;

   function Search (A : Nat_Array; E : Natural) return Result_Ty is
      type My_Interm is new Interm_Result (UpTo => A'Last);

      Init : constant My_Interm := My_Interm'(UpTo => A'Last, To_Search => A);
   begin
      return Search_Upto (Init, E);
   end Search;

end;
