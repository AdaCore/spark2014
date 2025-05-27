procedure Test_Loops with SPARK_Mode is

   type R is record
      I : aliased Positive;
   end record;

   procedure Test_Loop_1 (X : out R) with
     Potentially_Invalid => X,
     Global => null;

   procedure Test_Loop_1 (X : out R) is
   begin
      X := (I => 12);
      for K in 1 .. 100 loop
         X.I := X.I / 2 + 1;  --  @VALIDITY_CHECK:PASS
      end loop;
   end Test_Loop_1;

   procedure Test_Loop_2 (X : in out R) with
     Potentially_Invalid => X,
     Global => null;

   procedure Test_Loop_2 (X : in out R) is
   begin
      for K in 1 .. 100 loop
         X.I := X.I / 2 + 1; --  @VALIDITY_CHECK:FAIL
      end loop;
   end Test_Loop_2;

   procedure Test_Loop_3 (X : out R; Y : R) with
     Potentially_Invalid => (X, Y),
     Global => null;

   procedure Test_Loop_3 (X : out R; Y : R) is
   begin
      X := (I => 12);
      for K in 1 .. 100 loop
         if K = 1 then
            X := Y;
         else
            X.I := X.I / 2 + 1; --  @VALIDITY_CHECK:FAIL
         end if;
      end loop;
   end Test_Loop_3;

   procedure Test_Loop_4 (X : out R; Y : R) with
     Potentially_Invalid => X,
     Global => null;

   procedure Test_Loop_4 (X : out R; Y : R) is
   begin
      X := (I => 12);
      for K in 1 .. 100 loop
         if K = 1 then
            X := Y;
         else
            X.I := X.I / 2 + 1; --  @VALIDITY_CHECK:PASS
         end if;
      end loop;
   end Test_Loop_4;

begin
   null;
end Test_Loops;
