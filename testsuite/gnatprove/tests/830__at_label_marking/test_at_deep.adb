pragma Extensions_Allowed (All_Extensions);

procedure Test_At_Deep with SPARK_Mode
is
   type Int_Access is access Integer;

   function Traverse (X : access Integer) return access Integer is (X);

   function Allocate (X : Integer) return Int_Access is
   begin
      return new Integer'(X);
   end Allocate;

   --  References to At should not be of a deep type unless they are calls to
   --  allocating functions.

   procedure Test_1 is
      X : Int_Access := new Integer'(12);
      Y : Int_Access;
   begin
      <<L1>>
      X.all := 13;
      Y := X'At (L1); --  Should be rejected, introduces a copy
   end Test_1;

   procedure Test_2 is
      X : Int_Access := new Integer'(12);
   begin
      <<L1>>
      X.all := 13;
      declare
         Y : access Integer := Traverse (X)'At (L1); --  Should be rejected, introduces a copy
      begin
         Y.all := Y.all + 1;
      end;
   end Test_2;

   procedure Test_3 is
      X : Integer := 12;
      Y : Int_Access;
   begin
      <<L1>>
      X := 13;
      Y := Allocate (X)'At (L1); --  OK, At on allocating function in valid allocating context
   end Test_3;

begin
   null;
end;
