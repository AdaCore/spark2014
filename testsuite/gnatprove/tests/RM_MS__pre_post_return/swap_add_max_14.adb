package body Swap_Add_Max_14
  with SPARK_Mode
is
   procedure Swap (X, Y : in out Integer) is
      Temporary: Integer;
   begin
      Temporary := X;
      X         := Y;
      Y         := Temporary;
   end Swap;

   function Add (X, Y : Integer) return Integer is (X + Y);

   function Max (X, Y : Integer) return Integer is
     (if X >= Y then X
      else Y);

   function Divide (X, Y : Integer) return Integer is (X / Y);

   procedure Swap_Array_Elements(I, J : Index; A: in out Array_Type) is
      Temporary: Integer;
   begin
      Temporary := A(I);
      A(I)      := A(J);
      A(J)      := Temporary;
   end Swap_Array_Elements;
end Swap_Add_Max_14;
