package body Update is

   function F1 (Init_Val : Integer) return Array_1D is
      Arr : Array_1D := Array_1D'(others => An_Arr(5));
   begin
      Arr(1) := X;
      Arr(2) := X;
      Arr(3) := Init_Val + 1;
      return Arr;
   end F1;

   procedure Basic_Array_Update
     (A: in out Array_1D; I: in Index; New_Val: Integer) is
   begin
     A(I) := New_Val;
   end Basic_Array_Update;

   procedure Basic_Array_Update2
     (A: in out Array_1D; I: in Index; New_Val: Integer) is
   begin
     A(I) := New_Val;
   end Basic_Array_Update2;

   function F2 (Arr_In : Array_1D; I : Index) return Array_1D is
   begin
      return Arr_In'Update(1..I => 7);
   end F2;

   function F3 (Arr_In: Array_1D) return Array_1D is
      Arr : Array_1D := Arr_In;
   begin
      Arr(1) := X;
      Arr(2) := 1;
      Arr(3) := An_Arr(4);
      Arr(4) := X;
      return Arr;
   end F3;

   function F4 (Arr_In : Array_1D; I : Index; J : Index) return Array_1D is
   begin
      return Arr_In'Update(1..I => 10, I..J => 20);
   end F4;

   function F5 (Arr_In: Array_1D) return Array_1D is
      Arr : Array_1D := Arr_In;
   begin
      Arr(2) := 1;
      return Arr;
   end F5;

   procedure My_Init_Array (A: out Array_1D) is
   begin
      A := Array_1D'(others => 1);
      A := A'Update(3 => 2, 4..5 => 3);
   end My_Init_Array;

   procedure My_Init_Array2 (A: out Array_1D; I : in Index) is
   begin
      A := Array_1D'(others => 1);
      A := A'Update(I => 2, 4..5 => X);
   end My_Init_Array2;

   procedure Swap_Elements (I,J: in Index; A: in out Array_1D) is
      Tmp: Integer;
   begin
      Tmp  := A(I);
      A(I) := A(J);
      A(J) := Tmp;
   end Swap_Elements;

   function Swap_Fun (Arr_In : Array_1D; I, J : Index) return Array_1D is
      Arr : Array_1D := Arr_In;
   begin
      Arr(I) := Arr_In(J);
      Arr(J) := Arr_In(I);
      return Arr;
   end Swap_Fun;

end Update;
