procedure Test_Bounds with SPARK_Mode is
   subtype My_Nat is Natural range 0 .. 100;
   type Nat_Array is array (Positive range <>) of Natural;
   type My_T (X : My_Nat := 0) is record
      Content : Nat_Array (1 .. X);
   end record;

   procedure Change (X : in out My_T) with
     Pre  => not X'Constrained,
     Post => X.Content'Last = X.Content'Last'Old  --  @POSTCONDITION:FAIL
   is
   begin
      X := (X => 10, Content => (1 .. 10 => 0));
   end Change;

   procedure Change_2 (X : in out My_T) with
     Pre  => not X'Constrained,
     Post => X.X = X.X'Old                        --  @POSTCONDITION:FAIL
   is
   begin
      X := (X => 10, Content => (1 .. 10 => 0));
   end Change_2;

begin
   null;
end Test_Bounds;
