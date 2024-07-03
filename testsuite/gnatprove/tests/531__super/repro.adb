pragma Extensions_Allowed (All_Extensions);
procedure Repro with SPARK_Mode is
   package Pack is
      type T1 is tagged null record;
      procedure P (V : T1) with Pre'Class => False;

      type T2 is new T1 with null record;
      procedure P (V : T2) with Pre'Class => True;
   end Pack;

   package body Pack is
      procedure P (V : T1) is null;
      procedure P (V : T2) is null;
   end Pack;

   use Pack;

   procedure Call (V : T2'Class) is
   begin
      V.P; -- @PRECONDITION:PASS
      V'Super.P; -- @PRECONDITION:FAIL
                 --  Equivalent to "P (T1 (V));", a nondispatching call
                 --  to T1's primitive procedure P.
   end;
begin
   null;
end;
