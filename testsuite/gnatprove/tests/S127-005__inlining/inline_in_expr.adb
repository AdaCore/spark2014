pragma SPARK_Mode;
procedure Inline_In_Expr is
   function Dummy return Integer is
      Tmp : Integer := 0;
   begin
      for X in 1 .. 100 loop
         Tmp := Tmp + 1;
      end loop;
      return Tmp;
   end Dummy;

   X : Integer := Dummy;
   B : Boolean;
begin
   B := (for all Y in 1 .. Dummy => X = Dummy);
   X := (if (if Dummy = 1 then Dummy else Dummy) = 1 then Dummy else Dummy);
end Inline_In_Expr;
