with Simple;
with Reentrancy;
with Inside_Out;
with Globals;
with Aggregates;
with Object;
with Derived;

procedure Testinv is
begin
   declare
      use Simple;
      X : T;
   begin
      Create (X);
      Update (X);
      pragma Assert (Get (X) = 1);
   end;

   declare
      use Reentrancy;
      X : T;
   begin
      Create (X);
      Update (X);
      pragma Assert (Get (X) = 1);
   end;

   declare
      use Inside_Out;
      X : T;
   begin
      Create (X);
      Update (X);
      pragma Assert (Get (X) = 1);
   end;

   declare
      use Globals;
   begin
      Abs_Create;
      Abs_Update;
      pragma Assert (Abs_Get = 1);

      Gen_Create;
      Gen_Update;
      pragma Assert (Gen_Get = 1);

      Abs_Gen_Create;
      Abs_Gen_Update;
      pragma Assert (Abs_Gen_Get = 1);
   end;

   declare
      use Aggregates;
      Y : Arr_T;
      Z : Rec_T;
   begin
      Create_Arr (Y);
      Update_Arr (Y);
      pragma Assert (Get_Arr (Y) = 1);

      Create_Rec (Z);
      Update_Rec (Z);
      pragma Assert (Get_Rec (Z) = 1);
   end;

   declare
      use Object;
      X : T;
   begin
      Create (X);
      Update (X);
      pragma Assert (Get (X) = 1);
   end;

   declare
      use Derived;
      X : T;
      Y : D;
   begin
      Create (X);
      Update (X);
      pragma Assert (Get (X) = 1);

      Create (Y);
      Update (Y);
      pragma Assert (Get (Y) = 0);
   end;

end Testinv;
