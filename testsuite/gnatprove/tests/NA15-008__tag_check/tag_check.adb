package body Tag_Check is

   function Make (X : Integer) return T is
   begin
      return T'(X => X);
   end Make;

   procedure Assign (X : out T'Class; Y : T'Class) is
   begin
      --  The following tag check should be unprovable. But it should not make
      --  the following unprovable assertion prove, either
      X := Y;               --@TAG_CHECK:FAIL
      pragma Assert(False); --@ASSERT:FAIL
   end Assign;

   procedure Make_New (X : out T'Class; Y : Integer) is
   begin
      --  The following should not generate a check
      X := Make (Y);
   end Make_New;

   procedure Two (X, Y : T) is
   begin
      null;
   end Two;

   procedure Three (X, Y, Z : T) is
   begin
      null;
   end Three;


   procedure Use_Two (X, Y : T'Class) is
   begin
      Two (X, Y); --@TAG_CHECK:FAIL
   end Use_Two;

   procedure Use_Three (X, Y, Z : T'Class) is
   begin
      Three (X, Y, Z); --@TAG_CHECK:FAIL
   end Use_Three;
end Tag_Check;
