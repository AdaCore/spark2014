package body Default is
   function Sub (X : Integer := 0; Y : Integer) return Integer
   is
   begin
      return X - Y;
   end Sub;

   function Add (X : Integer; Y : Integer := 0) return Integer
   is
   begin
      return X + Y;
   end Add;

   function Use_Sub return Integer is
   begin
      return (Sub (1,2) + Sub (Y => 2));
   end;

   function Use_Add return Integer is
   begin
      return (Add (1,2) + Add (2));
   end;
end Default;
