with Ada.Text_IO;  use Ada.Text_IO;

procedure Fixed_Lower_Bound_Types_And_Objects is

   type FLB_0_Int_1D is array (Integer range 0 .. <>) of Integer;

   type FLB_1_Int_1D is array (Integer range 1 .. <>) of Integer;

   Arr_FLB_0_1D : FLB_0_Int_1D (0 .. 99);
   Arr_FLB_1_1D : FLB_1_Int_1D (1 .. 100);


   type Colors is (Red, Orange, Yellow, Green, Blue, Violet);

   type Color_Array is array (Colors range Red .. <>) of Integer;

   subtype C_Red_Blue is Color_Array (Red .. Blue);


   type FLB_0_1_2D
     is array (Integer range 0 .. <>, Integer range 1 .. <>) of Integer;

   type Mixed_FLB_0_Box_2D
     is array (Integer range 0 .. <>, Integer range <>) of Integer;

   type Mixed_FLB_Box_1_2D
     is array (Integer range <>, Integer range 1 .. <>) of Integer;

   Arr_FLB_0_1_2D     : FLB_0_1_2D (0 .. 5, 1 .. 10);
   Arr_Mixed_FLB_0_2D : Mixed_FLB_0_Box_2D (0 .. 5, 10 .. 20);
   Arr_Mixed_FLB_1_2D : Mixed_FLB_Box_1_2D (7 .. 9, 1 .. 8);


   procedure Proc_FLB_0 (A : in out FLB_0_Int_1D) is
   begin
      pragma Assert (A'First = 0);

      Put_Line ("A'first =" & A'first'Image);
      Put_Line ("A'last  =" & A'last'Image);

      A(0) := A(A'Last);
   end Proc_FLB_0;

   procedure Proc_FLB_1 (A : FLB_1_Int_1D) is
   begin
      pragma Assert (A'First = 1);

      Put_Line ("A'first =" & A'first'Image);
      Put_Line ("A'last  =" & A'last'Image);
   end Proc_FLB_1;

   function Func_FLB_1 (A : FLB_1_Int_1D) return FLB_1_Int_1D is
   begin
      return A (5 .. 8);
   end Func_FLB_1;

   procedure Proc_Colors (A : in out Color_Array) is
   begin
      pragma Assert (A'First = Red);

      Put_Line ("A'first =" & A'first'Image);
      Put_Line ("A'last  =" & A'last'Image);

      A(A'First) := A(A'Last);
   end Proc_Colors;

   A_0_7  : FLB_0_Int_1D (0 .. 7);
   A_1_10 : FLB_1_Int_1D (1 .. 10) := (1, 2, 3, 4, 5, 6, 7, 8, 9, 10);
   A_1_5  : FLB_1_Int_1D := A_1_10 (3 .. 7);        -- Sliding

   All_Colors : Color_Array (Red .. Violet);
   A_Red_Blue : Color_Array (Red .. Blue);

   All_But_Red_1 : Color_Array := All_Colors (Orange .. Violet);  -- Sliding
   All_But_Red_2 : C_Red_Blue  := All_Colors (Orange .. Violet);  -- Sliding

begin
   Proc_FLB_0 (A_0_7);
   Proc_FLB_0 (A_0_7 (3 .. 5));                     -- Sliding

   Proc_FLB_1 (A_1_10);
   Proc_FLB_1 (A_1_5);
   Proc_FLB_1 (A_1_10 (3 .. 7));                    -- Sliding
   Proc_FLB_1 (Func_FLB_1 (A_1_10));                -- Func result already slid

   Proc_Colors (All_Colors);
   Proc_Colors (All_But_Red_1);
   Proc_Colors (All_But_Red_2);
   Proc_Colors (All_But_Red_1 (Yellow .. Blue));    -- Sliding
   Proc_Colors (All_But_Red_2 (Yellow .. Blue));    -- Sliding
   Proc_Colors (A_Red_Blue);
   Proc_Colors (A_Red_Blue (Yellow .. Green));      -- Sliding
end Fixed_Lower_Bound_Types_And_Objects;
