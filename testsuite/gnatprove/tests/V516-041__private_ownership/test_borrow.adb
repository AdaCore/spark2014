with Private_Ownership;
with Private_Tagged;
with Private_Tagged_Ext;
with Private_Discriminants;
procedure Test_Borrow with SPARK_Mode is
   procedure Test_Private_Pointer with
     Global => null
   is
      use Private_Ownership;
      B : Pool_Specific_Access;
      C : Pool_Specific_Access;
   begin
      B := Allocate (13);
      pragma Assert (Deref (B) = 13);
      C := B;
      pragma Assert (Deref (B) = 13); --  Reject, B is moved
   end Test_Private_Pointer;
   procedure Test_Private_Pointer_2 with
     Global => null
   is
      use Private_Ownership;
      type V is new Pool_Specific_Access with
        Predicate => Is_Null (Pool_Specific_Access (V)) or else Deref (Pool_Specific_Access (V)) > 0;
      type Holder is record
         A : V;
      end record;
      B : Holder;
      C : Holder;
   begin
      B.A := Allocate (13);
      pragma Assert (Deref (B.A) = 13);
      C := B;
      pragma Assert (Deref (B.A) = 13); --  Reject, B is moved
   end Test_Private_Pointer_2;
   procedure Test_Private_Tagged with
     Global => null
   is
      use Private_Tagged;
      B : Pool_Specific_Access;
      C : Pool_Specific_Access;
   begin
      B := Allocate (13);
      pragma Assert (Deref (B) = 13);
      C := B;
      pragma Assert (Deref (B) = 13); --  Reject, B is moved
   end Test_Private_Tagged;
   procedure Test_Private_Tagged_2 with
     Global => null
   is
      use Private_Tagged_Ext;
      B : V;
      C : V;
   begin
      B := Allocate (13);
      pragma Assert (Deref (B) = 13);
      C := B;
      pragma Assert (Deref (B) = 13); --  Reject, B is moved
   end Test_Private_Tagged_2;
   procedure Test_Discriminant with
     Global => null
   is
      use Private_Discriminants;
      B : Pool_Specific_Access;
      C : Pool_Specific_Access;
   begin
      B := Allocate (13);
      pragma Assert (Deref (B) = 13);
      C := B;
      pragma Assert (Deref (B) = 13); --  Reject, B is moved
   end Test_Discriminant;
   procedure Test_Discriminant_2 with
     Global => null
   is
      use Private_Discriminants;
      subtype V is Pool_Specific_Access (True);
      type Holder is record
         A : V;
      end record;
      B : Holder;
      C : Holder;
   begin
      B.A := Allocate (13);
      pragma Assert (Deref (B.A) = 13);
      C := B;
      pragma Assert (Deref (B.A) = 13); --  Reject, B is moved
   end Test_Discriminant_2;
begin
   null;
end;
