package body P is

   function Pack (A : T1; B : T2; C : T3) return R is
      Result : R;
      Tmp : Integer;
   begin
      Tmp := X;
      Tmp := (Tmp + F1 (Y)) + (Z + T);
      P1 (Tmp);
      Result := (A, B, C, Tmp);
      return Result;
   end;

end;
