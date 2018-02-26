with Stacks; use Stacks;
procedure Test_Stack (S : in out Stack_Root'Class) with SPARK_Mode is
   E : Element;
begin
   S.Reset;
   for I in Element range 1 .. 5 loop
      S.Push (I);
   end loop;
   pragma Assert (S.Get_Model = (1, 2, 3, 4, 5));
   for I in reverse Element range 1 .. 5 loop
      S.Pop (E);
      pragma Assert (E = I);
   end loop;
   pragma Assert (S.Is_Empty);
end Test_Stack;
