pragma Extensions_Allowed (All_Extensions);

--  A subset of the original unit P with side-effect function returning record
--  object, to trigger the flattening machinery where allowed.

procedure P1 is

   type Rec is record
      C : Boolean;
   end record;

   X : Rec := (C => True);

   function Flip return Rec
      with Side_Effects,
           Global => (In_Out => X)
   is
   begin
      X.C := not X.C;
      return X;
   end;

   function Test_Simple_Return_Statement return Rec
      with Global => (In_Out => X), Side_Effects
   is
   begin
      return Flip;
   end;

   function "+" (A, B : Integer) return Rec
      with Global => (In_Out => X), Side_Effects
   is
      pragma Unreferenced (A, B);
   begin
      return Flip;
   end;

   function Test_Extended_Return_Statement return Rec
      with Global => (In_Out => X), Side_Effects
   is
   begin
      return Tmp : Rec := Flip do
         Tmp.C := not Tmp.C;
      end return;
   end;

begin
   null;
end;
