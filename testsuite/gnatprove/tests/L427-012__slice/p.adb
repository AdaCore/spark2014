procedure P is
   New_Str : String (1 .. 5) := "12345";
   New_Sub : String (1 .. 5) := New_Str;
   Pos     : Integer := 1;
begin
   while New_Str (Pos .. 5) /= New_Sub loop
      Pos := Pos + 1;
   end loop;
end P;
