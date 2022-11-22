procedure Int is
   A : constant Integer := 3 with Warnings => Off;
   B : constant Integer := 3;

   C : constant Float := 1.0 with Warnings => Off;

   procedure Dummy with Import, Global => null, Annotate => (GNATprove, Always_Return);

begin

   --  if branch is dead

   if A /= 3 then
      Dummy;
   else
      Dummy;
   end if;

   if B /= 3 then
      Dummy;
   else
      Dummy;
   end if;

   --  else branch is dead

   if A < 5 then
      Dummy;
   else
      Dummy;
   end if;

   if B < 5 then
      Dummy;
   else
      Dummy;
   end if;

   --  we should emit a warning

   if C = 2.0 then
      Dummy;
   else
      Dummy;
   end if;
end Int;
