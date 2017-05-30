procedure Succ_Floats (A, B : Boolean) is
   X : Float;
begin
   X := 0.0;
   pragma Assert (Float'Succ (X) > 0.0);
   pragma Assert (Float'Succ (X) < 1.0);
   pragma Assert (Float'Pred (X) < 0.0);
   pragma Assert (Float'Pred (X) > -1.0);

   X := 1.0;
   pragma Assert (Float'Succ (X) > 1.0);
   pragma Assert (Float'Succ (X) < 1.1);
   pragma Assert (Float'Pred (X) < 1.0);
   pragma Assert (Float'Pred (X) > 0.9);

   X := Float'Last;
   if A then
      X := Float'Succ (X); --  overflow fails here
   else
      pragma Assert (Float'Pred (X) < Float'Last);
   end if;
   pragma Assert (Float'Pred (X) > 0.0);

   X := Float'First;
   if B then
      X := Float'Pred (X); --  overflow fails here
   else
      pragma Assert (Float'Succ (X) > Float'First);
   end if;
   pragma Assert (Float'Succ (X) < 0.0);
end Succ_Floats;
