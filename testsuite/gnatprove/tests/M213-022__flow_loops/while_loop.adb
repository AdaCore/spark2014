procedure While_Loop (X : in Natural;
                      Y : out Integer)
is
begin

   Y := 0;
   while X /= Y loop
      Y := Y + 1;
   end loop;

end While_Loop;
