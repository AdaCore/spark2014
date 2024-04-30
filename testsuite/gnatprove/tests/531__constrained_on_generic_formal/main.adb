with P;

procedure Main is
   type My_String is new String(1 .. 10);

   procedure P0 is new P(Integer);
   procedure P1 is new P(My_String);

   X : Integer := 0;
   S : My_String := (1..10 => ' ');
begin
   P0 (X);
   P1 (S);
end;
