procedure P is

   X : Integer := 0;
   Y : Integer renames X;

begin
   Y := Y + 1;
   pragma Assert (Y = 1);
end;
