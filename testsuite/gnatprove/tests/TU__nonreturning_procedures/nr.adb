package body NR
is
   --  TU : 1. A call to a nonreturning procedure introduces an
   --  obligation to prove that the statement will not be executed,
   --  much like the verification condition associated with ``pragma
   --  Assert (False);`` [In other words, the verification conditions
   --  introduced for a call to a nonreturning procedure are the same
   --  as those introduced for a runtime check which fails
   --  unconditionally. See also section :ref:`exceptions`, where a
   --  similar verification rule is imposed on ``raise_statements``.]

   procedure Op1
   is
   begin
      if X <= 0 then
         P; -- this call should be proved non-executable @RAISE:PASS
      end if;
      X := X + 1;
   end Op1;

   procedure Op2
   is
   begin
      if X <= 1 then
         P; -- Might be executed, therefore failed proof here @RAISE:FAIL
      end if;
      X := X + 1;
   end Op2;

end NR;
