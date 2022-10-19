procedure Polarity is
   A : constant Boolean := True with Warnings => Off;
   B : constant Boolean := True;
   C : constant Boolean := False with Warnings => Off;
   D : constant Boolean := False;

   E : Boolean := True with Warnings => Off;

   Foo : constant Boolean := True;
   Bar : constant Boolean := False;

   procedure Dummy with Import, Global => null, Annotate => (GNATprove, Always_Return);
begin

   --  else branch is dead

   if A then
      Dummy;
   else
      Dummy;
   end if;

   if B then
      Dummy;
   else
      Dummy;
   end if;

   --  we should emit warnings on dead code because E is not a constant

   if E then
      Dummy;
   else
      Dummy;
   end if;

   --  if branch is dead

   if not A then
      Dummy;
   else
      Dummy;
   end if;

   if not B then
      Dummy;
   else
      Dummy;
   end if;

   -- else branch is dead

   if A or else Bar then
      Dummy;
   else
      Dummy;
   end if;

   if B or else Bar then
      Dummy;
   else
      Dummy;
   end if;

   -- if branch is dead

   if Foo and then C then
      Dummy;
   else
      Dummy;
   end if;

   if Foo and then D then
      Dummy;
   else
      Dummy;
   end if;

   -- else branch is dead

   if Bar or else (not (Bar and then C)) then
      Dummy;
   else
      Dummy;
   end if;

   if Bar or else (not (Bar and then B)) then
      Dummy;
   else
      Dummy;
   end if;

   -- first branch is dead (and we should complain), third and else branch are dead

   if Bar then
      Dummy;
   elsif A then
      Dummy;
   elsif Bar then
      Dummy;
   else
      Dummy;
   end if;

   if Bar then
      Dummy;
   elsif B then
      Dummy;
   elsif Bar then
      Dummy;
   else
      Dummy;
   end if;
end Polarity;
