package body Mixed
is
   type Unsigned_Byte is range 0 .. 255;
   type Enum_T is (Elem_0, Elem_1, Elem_2);

   type Rec is record
      B : Boolean;
      E : Enum_T;
      I : Integer;
   end record;


   function Get_I (R : in Rec) return Integer
     with Post => Get_I'Result = R.I  --  @POSTCONDITION:PASS
   is
   begin
      return R.I;
   end Get_I;

   function Id (R: in Rec) return Rec
     with Post => R = Id'Result  --  @POSTCONDITION:PASS
   is
   begin
      return R;
   end Id;

   pragma Warnings (Off, "* has no effect");
   procedure Test_A_1 (R : in Rec)
     with Depends => (null => R)
   is
      N : Integer;
   begin
      N := Get_I (R);
      pragma Assert (N = 0);  --  @ASSERT:FAIL
   end Test_A_1;
   pragma Warnings (On, "* has no effect");

   procedure Test_A_2 (R : in     Rec;
                       X :    out Boolean)
     with Depends => (X => R)
   is
      N : Integer;
      S : Rec;
   begin
      S := Id (R);
      N := S.I;
      X := N = 0;
      pragma Assert (X);  --  @ASSERT:FAIL
   end Test_A_2;

end Mixed;
