procedure Main with SPARK_Mode is
   type Untagged is record
      F : Integer;
      G : Integer;
   end record;
   function "=" (X, Y : Untagged) return Boolean is (X.G = Y.G) with Pre => False;

   type Holder is record
      C : Untagged;
   end record;
   type Arr is array (Positive range 1 .. 1) of Untagged;

   H1 : Holder := (C => (1, 2));
   H2 : Holder := (C => (2, 2));
   A1 : Arr    := (1 => (1, 2));
   A2 : Arr    := (1 => (2, 2));
begin
   pragma Assert (H1 = H2); -- There should be a precondition failure here
   pragma Assert (A1 = A2); -- There should be a precondition failure here
end;
