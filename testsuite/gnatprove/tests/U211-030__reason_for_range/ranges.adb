procedure Ranges (X1, X2 : Integer) is
   subtype T is Integer range -10 .. 10;
   subtype U is Integer range 0 .. 20;
   Y : U;

   type A is array (1 .. 1) of U;
   Z : A;

begin
   if X1 in T then
      Y := T(X1);
   else
      Y := T(X1);
   end if;

   if X2 in T then
      Z := (1 => T(X2));
   else
      Z := (1 => T(X2));
   end if;
end Ranges;
