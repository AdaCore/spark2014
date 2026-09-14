pragma Extensions_Allowed (All_Extensions);

procedure P is
   X : Boolean := True;
   function Flip return Boolean
      with Side_Effects,
           Global => (In_Out => X)
   is
   begin
      X := not X;
      return X;
   end;

   function Test_Simple_Return_Statement return Boolean
      with Global => (In_Out => X), Side_Effects
   is
   begin
      return Flip;
   end;

   --  same as above but with an operator symbol

   function "+" (A, B : Integer) return Boolean
      with Global => (In_Out => X), Side_Effects
   is
      pragma Unreferenced (A, B);
   begin
      return Flip;
   end;

   function Test_Extended_Return_Statement return Boolean
      with Global => (In_Out => X), Side_Effects
   is
   begin
      return Tmp : Boolean := Flip do
         Tmp := not Tmp;
      end return;
   end;

   procedure Test_If_Statement
     with Global => (In_Out => X)
   is
   begin
      if Flip then
         X := not X;
      elsif Flip then
         X := not X;
      end if;
   end;

   procedure Test_Case_Statement
     with Global => (In_Out => X)
   is
   begin
      case Flip is
         when True =>
            X := not X;
         when False =>
            X := not X;
      end case;
   end;

   procedure Test_Exit_Statement
     with Global => (In_Out => X)
   is
   begin
      loop
         exit when Flip;
      end loop;
   end;

   procedure Test_Continue_Statement
     with Global => (In_Out => X)
   is
   begin
      loop
         continue when Flip;
         exit;
      end loop;
   end;

begin
   null;
end;
