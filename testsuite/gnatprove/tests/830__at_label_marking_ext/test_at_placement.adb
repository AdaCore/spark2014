pragma Extensions_Allowed (All_Extensions);

procedure Test_At_Placement with SPARK_Mode
is

   --  If the prefix of At is an allocating function call, it should be in a
   --  pragma or constant declaration.

   type Int_Access is access Integer;

   type Int_Cst_Access is access constant Integer;

   type Int_Access_Wrapper is record
      R : Int_Access;
   end record;

   type Int_Access_Wrapper_Cst_Access is access constant Int_Access_Wrapper;

   function Allocate (X : Integer) return Int_Access is
   begin
      return new Integer'(X);
   end Allocate;

   --  This is a more compact variant of a procedure with the same parent unit
   --  and name in 830__at_label_marking. The form here creates the wrapper
   --  using an aggregate.

   procedure Test_Allocate_3 is
      X : Integer := 12;
   begin
      <<L1>>
      X := 13;
      declare
         Y : constant Int_Access_Wrapper := (R => Allocate (X)'At (L1)); --  OK, At on allocating function in constant declaration
      begin
         null;
      end;
   end Test_Allocate_3;
begin
   null;
end;
