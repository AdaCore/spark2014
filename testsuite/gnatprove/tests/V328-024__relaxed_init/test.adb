procedure Test with SPARK_Mode is
   type Relaxed_Int is new Integer with Relaxed_Initialization;
   type Relaxed_Rec is record
      X : Integer;
      Y : Integer;
   end record with Relaxed_Initialization;
   C : Relaxed_Int;
   D : Integer := 1;
   R : Relaxed_Rec;

   procedure Foo with Global => (Input => C) is
      type Arr is array (Positive range <>) of Relaxed_Int;
      A : Arr (1 .. 3) := (1 => C, others => <>);
   begin
      null;
   end Foo;

   procedure Bar with Global => (Input => (D, R)) is
      type Arr is array (Positive range <>) of Relaxed_Rec;
      A : Arr (1 .. 3) := (1 => R, others => (X => D, Y => <>));
   begin
      null;
   end Bar;
begin
   null;
end Test;
