procedure Flow with SPARK_Mode is

   type T is record
      C1, C2 : Integer;
   end record;

   procedure Test (X1, X2 : Integer; Y1, Y2 : out Integer)
     with Post    => Y1 = X1 and Y2 = X2,
          Depends => (Y1 => X1, Y2 => X2)
   is
      Proxy : T;
   begin
      Proxy :=
        (declare
            Local : constant T := (C1 => X1, C2 => X2);
         begin
            Local);

      Y1 := Proxy.C1;
      Y2 := Proxy.C2;
      --  A convoluted way to assign Y1 with X1 and Y2 with X2
   end Test;

   procedure Test2 (X : Integer; Y : out Integer)
     with Depends => (Y => null, null => X), Post => Y = 0  --  these contracts are correct
   is
   begin
      Y := (declare
              C : constant Integer := X;
            begin
              0);
   end Test2;

   procedure Test3 (X : out Integer)
     with Global => null
   is
      A : array (1 .. 1) of Integer := (others => 1);
   begin
      --  First_Variable_Use of X with Targeted => True will only look at the RHS of the assignment statement
      A (X) := 0;  --  Test is about reported location of (correct) check
      X := A (X);
   end Test3;

   V1, V2 : Integer;
   V3 : T;

begin
   Test (1, 2, V1, V2);
   Test2 (1, V1);
   Test3 (V1);
end;
