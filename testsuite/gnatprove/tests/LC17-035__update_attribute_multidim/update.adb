package body Update is

   procedure Basic_Array_Update
     (A: in out Array_3D; I: in Index; New_Val: Integer) is
   begin
     A(I, I, I) := New_Val;
   end Basic_Array_Update;

   procedure Basic_Array_Update2
     (A: in out Array_3D; I: in Index; New_Val: Integer) is
   begin
     A(I, I, I) := New_Val;
   end Basic_Array_Update2;

end Update;
