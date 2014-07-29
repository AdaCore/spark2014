procedure Get_Size with SPARK_Mode is

   type T is record
      X : Integer;
   end record;

   type A is array (1 .. 10) of T;

   function F return Integer is (T'Size);

   X : Integer := T'Size;
begin
   pragma Assert (X = F);
   pragma Assert (A'Size = 10 * T'Size);
end Get_Size;
