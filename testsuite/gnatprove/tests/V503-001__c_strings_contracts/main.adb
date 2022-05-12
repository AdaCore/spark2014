with Interfaces.C;         use Interfaces.C;
with Interfaces.C.Strings; use Interfaces.C.Strings;

procedure Main is

   procedure Check_Pred_0 is
      A : Chars_Ptr := New_String ("hello");
   begin
      Update (A, 0, String'("hello!"), True); --@PRECONDITION:FAIL
   end Check_Pred_0;

   procedure Check_Pred_Last is
      A : Chars_Ptr := New_String ("hello");
   begin
      Update (A, Size_T'Last, String'("hello!"), True); --@PRECONDITION:FAIL
   end Check_Pred_Last;

   procedure Check_Volatility is
      A : Chars_Ptr := New_String ("hello");
      B : Chars_Ptr := New_String ("hello");
   begin
      pragma Assert (A = B); --@ASSERT:FAIL
   end Check_Volatility;

   procedure Check_Update_Effect is
      A : Chars_Ptr := New_String ("hello");
      S : constant String := Value (A);
   begin
      pragma Assert (Value (A) = S);
      Update (A, 0, String'("hi"));
      pragma Assert (Value (A) = S); --@ASSERT:FAIL
   end Check_Update_Effect;
begin
   null;
end Main;
