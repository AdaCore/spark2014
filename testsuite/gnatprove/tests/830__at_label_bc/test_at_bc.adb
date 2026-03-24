pragma Extensions_Allowed (All_Extensions);

procedure Test_At_BC with SPARK_Mode
is
   type Int_Access is access Integer;

   function Allocate (X : Integer) return Int_Access is
   begin
      return new Integer'(X);
   end Allocate;

   procedure Test_1 is
      X : Int_Access := new Integer'(12);
      Y : Int_Access;
      C : Integer;
   begin
      <<L1>>
      Y := X;
      C := X.all'At (L1); --  OK, X is readable at L1 even if it is moved now
   end Test_1;

   procedure Test_2 is
      X : Int_Access := new Integer'(12);
      Y : Int_Access;
      C : Integer;
   begin
      Y := X;
      <<L1>>
      X := Y;
      C := X.all'At (L1); --  Should be rejected, X is moved at L1
   end Test_2;

   procedure Test_3 is
      X : Integer := 12;
      Y : Int_Access;
   begin
      <<L1>>
      X := 13;
      pragma Assert (Allocate (X)'At (L1).all = 12); --  OK, the prefix is a newly allocated object
   end Test_3;

begin
   null;
end;
