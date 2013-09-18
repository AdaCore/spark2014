package body Foo
  with SPARK_Mode
is

   ----------------------------------------------------------------------
   --  These tests aim to show the difference between reals and floats
   ----------------------------------------------------------------------

   --  For reals this is true
   --  For floats this is true
   procedure Add_Monotonic (X, Y : Float)
     with Pre => (X > 0.0 and Y > 0.0)
   is
   begin
      pragma Assert (X + Y >= X);  -- Should be true
   end Add_Monotonic;

   --  For reals this is true
   --  For floats this is false
   procedure Add_Strictly_Monotonic (X, Y : Float)
     with Pre => (X > 0.0 and Y > 0.0)
   is
   begin
      pragma Assert (X + Y > X);  -- Should be false
   end Add_Strictly_Monotonic;

   --  For reals this is true
   --  For floats this is true
   procedure Transitive (X, Y, Z : Float)
     with Pre => (X < Y and Y < Z)
   is
   begin
      pragma Assert (X < Z); -- Should be true
   end Transitive;

   --  For reals this is false
   --  For floats this is true
   procedure Smooth (X, Y, Z : Float)
     with Pre => (X = 1.0 and Z = 1.0000001 and X < Y and Y < Z)
   is
   begin
      pragma Assert (False);  --  Should be provable as no value for Y exists
   end Smooth;

   --  For reals this is true
   --  For floats this is true, in most cases (but here it is as we
   --  rule out NaN)
   procedure Equality (X : Float)
   is
   begin
      pragma Assert (X = X);  --  Should be true
   end Equality;

   --  Should not be provable for reals or floats
   procedure Introduce_NaN_1 (X, Y : Float; Z : out Float)
     with Pre => (X = 12.25 and Y = 0.0)
   is
   begin
      Z := X / Y;
   end Introduce_NaN_1;

   --  Ignoring the division check, the actual equality should be:
   --     For reals true
   --     For floats false
   procedure Introduce_NaN_2 (X, Y : Float)
     with Pre => (X = 0.0 and Y = 0.0)
   is
   begin
      pragma Assert (X / Y = X / Y);  --  should be false (ignoring
                                      --  the division checks)
   end Introduce_NaN_2;

   ----------------------------------------------------------------------
   --  These tests do nothign too fancy, but they go through
   --  awkward code-paths in VCG to make sure the implementation
   --  is reasonably robust
   ----------------------------------------------------------------------

   procedure Unary_Ops (X : Float)
   is
   begin
      pragma Assert (- (- X) = + X);
   end Unary_Ops;

   procedure Floats_And_Double (X : Float; Y : Long_Float)
   is
   begin
      pragma Assert ((Float (Y) = X) = (Long_Float (X) = Y));
   end Floats_And_Double;


end Foo;

