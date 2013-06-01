procedure Foo (A : in     Boolean;
               X : in out Integer;
               Y : in out Integer; --  Initial value of Y not used
               Z :    out Integer) --  Initial value of Z used
is
   B : Boolean;  --  Initial value used
begin

   if A then   --  Pointless
      Y := X;  --  Pointless
   else
      Y := Z;  --  Pointless
   end if;
   Y := 3;
   if A or B then  --  Use of B
      return;
   else
      X := 0;
   end if;
   Y := 0;

end Foo;

--  Final derives should be:
--  X from X, A, [B]
--  Y from    A, [B]
--  Z from            Z
