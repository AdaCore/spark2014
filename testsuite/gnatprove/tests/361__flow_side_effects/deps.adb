procedure Deps is

   --  Declare functions with all combinations of explicit dependencies

   function F1 (A : Boolean; B : out Boolean) return Boolean
      with Side_Effects, Depends => (B => A, F1'Result => A)
   is
   begin
      B := A;
      return A;
   end;

   function F2 (A : Boolean; B : out Boolean) return Boolean
      with Side_Effects, Depends => (B => null, F2'Result => A)
   is
   begin
      B := True;
      return A;
   end;

   function F3 (A : Boolean; B : out Boolean) return Boolean
      with Side_Effects, Depends => (B => A, F3'Result => null)
   is
   begin
      B := A;
      return True;
   end;

   function F4 (A : Boolean; B : out Boolean) return Boolean
      with Side_Effects, Depends => (B => null, F4'Result => null, null => A)
   is
   begin
      pragma Assert (A);
      B := True;
      return True;
   end;

   --  Check that declared dependencies behave as expected in calls

   procedure Test1 (X : Boolean; Y, Z : out Boolean)
      with Depends => (Y => X, Z => X)
   is
   begin
      Z := F1 (X, Y);
   end;

   procedure Test2 (X : Boolean; Y, Z : out Boolean)
      with Depends => (Y => null, Z => X)
   is
   begin
      Z := F2 (X, Y);
   end;

   procedure Test3 (X : Boolean; Y, Z : out Boolean)
      with Depends => (Y => X, Z => null)
   is
   begin
      Z := F3 (X, Y);
   end;

   procedure Test4 (X : Boolean; Y, Z : out Boolean)
      with Depends => (Y => null, Z => null, null => X)
   is
   begin
      Z := F4 (X, Y);
   end;

   I, J, K : Boolean;

begin
   I := True;
   Test1 (I, J, K);
   Test2 (I, J, K);
   Test3 (I, J, K);
   Test4 (I, J, K);
end;
