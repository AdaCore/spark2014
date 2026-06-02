procedure Potentially_Invalid with SPARK_Mode is
   type R is record
      F : Positive;
   end record;
   type A is array (Positive range <>) of R;
   X : A (1 .. 42) with Potentially_Invalid;
   procedure P (I : Integer)
     with Global => (In_Out => X),
     Pre => (I <= X'Last),
     Post => (if I > 0 then X (I)'Old.F >= 2); --@INDEX_CHECK:PASS
   procedure P (I : Integer) is
   begin
      X (I).F := 8;
   end P;
begin
   null;
end Potentially_Invalid;
