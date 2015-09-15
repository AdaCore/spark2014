with Stack; use Stack;
procedure Use_Stack with SPARK_Mode,
  Pre => not Is_Empty and not Is_Empty2 is
   E : Element := 1;
   F : Element;
begin
   F := Peek;
   Push3 (E);
   pragma Assert (Peek = E or Peek = F);
   F := Peek2;
   Push4 (E);
   pragma Assert (Peek2 = E or Peek2 = F);
end Use_Stack;
