with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

   subtype Int is Integer range 1 .. 9;

   subtype Sub_Int is Int range 2 .. 4;

   type Power_Of_Two is
      (One, Two, Four, Eight, Sixteen, Thirty_Two, Sixty_Four);
   for Power_Of_Two use (One        => 1,
                         Two        => 2,
                         Four       => 4,
                         Eight      => 8,
                         Sixteen    => 16,
                         Thirty_Two => 32,
                         Sixty_Four => 64);

   subtype Sub_POT1 is Power_Of_Two range One  .. Sixteen;
   subtype Sub_POT2 is Power_Of_Two range Four .. Sixty_Four;

   type Arr is array (1 .. 5) of Int
      with Default_Component_Value => 1;

   type Arr_Unconstr is array (Int range <>) of Int
      with Default_Component_Value => 1;

   type Arr_Non_Contiguous is array (Power_Of_Two range <>) of Integer
      with Default_Component_Value => 9;

   ---------------------
   --  Check_Contents --
   ---------------------

   function Check_Contents (A : Arr; A1, A2, A3, A4, A5 : Int) return Boolean
   is
      F : constant Int := A'First;
   begin
      return   A (F)     = A1
      and then A (F + 1) = A2
      and then A (F + 2) = A3
      and then A (F + 3) = A4
      and then A (F + 4) = A5;
   end Check_Contents;

   function Check_Contents (A : Arr_Unconstr; A1, A2 : Int) return Boolean
   is
      F : constant Int := A'First;
   begin
      return A (F) = A1 and then A (F + 1) = A2;
   end Check_Contents;

   function Check_Contents (A : Arr_Unconstr; A1, A2, A3 : Int) return Boolean
   is
      F : constant Int := A'First;
   begin
      return A (F) = A1 and then A (F + 1) = A2 and then A (F + 2) = A3;
   end Check_Contents;

   function Check_Contents (A : Arr_Unconstr; A1, A2, A3, A4, A5 : Int)
      return Boolean
   is
      F : constant Int := A'First;
   begin
      return   A (F)     = A1
      and then A (F + 1) = A2
      and then A (F + 2) = A3
      and then A (F + 3) = A4
      and then A (F + 4) = A5;
   end Check_Contents;

   function Check_Contents
      (A                   : Arr_Non_Contiguous;
       A1, A2, A4, A8, A16 : Integer)
      return Boolean
   is
      Elements     : constant array (1 .. 5) of Integer :=
         (A1, A2, A4, A8, A16);
      Elements_Idx : Integer := 1;
   begin
      for I in A'Range loop
         if A (I) /= Elements (Elements_Idx) then
            return False;
         end if;
         Elements_Idx := Elements_Idx + 1;
      end loop;

      return True;
   end Check_Contents;

   function Check_Contents
      (A                             : Arr_Non_Contiguous;
       A1, A2, A4, A8, A16, A32, A64 : Integer)
      return Boolean
   is
      Elements     : constant array (1 .. 7) of Integer :=
         (A1, A2, A4, A8, A16, A32, A64);
      Elements_Idx : Integer := 1;
   begin
      for I in A'Range loop
         if A (I) /= Elements (Elements_Idx) then
            return False;
         end if;
         Elements_Idx := Elements_Idx + 1;
      end loop;

      return True;
   end Check_Contents;

   ------------------
   -- Check_Bounds --
   ------------------

   function Check_Bounds (A : Arr_Unconstr; First, Last : Int) return Boolean
   is (A'First = First and then A'Last = Last);

   -----------------------
   -- Check_All_Indices --
   -----------------------

   function Check_All_Indices
      (A                             : Arr_Non_Contiguous;
       I1, I2, I4, I8, I16, I32, I64 : Power_Of_Two) return Boolean
   is
      Elements     : constant array (1 .. 7) of Power_Of_Two :=
         (I1, I2, I4, I8, I16, I32, I64);
      Elements_Idx : Integer := 1;
   begin
      for I in A'Range loop
         if I /= Elements (Elements_Idx) then
            return False;
         end if;

         Elements_Idx := Elements_Idx + 1;
      end loop;

      return True;
   end Check_All_Indices;

   function Check_All_Indices
      (A                   : Arr_Non_Contiguous;
       I1, I2, I4, I8, I16 : Power_Of_Two) return Boolean
   is
      Elements     : constant array (1 .. 5) of Power_Of_Two :=
         (I1, I2, I4, I8, I16);
      Elements_Idx : Integer := 1;

   begin
      for I in A'Range loop
         if I /= Elements (Elements_Idx) then
            return False;
         end if;


         Elements_Idx := Elements_Idx + 1;
      end loop;

      return True;
   end Check_All_Indices;

   --------------------
   -- Dynamic_Bounds --
   --------------------

   function Dynamic_Bounds (Low, High : Int) return Arr_Unconstr is
      AU : constant Arr_Unconstr (Low .. High) := (5, 5, 5, 5, 5);
   begin
      return AU;
   end Dynamic_Bounds;

   ----------
   -- Same --
   ----------

   function Same (X : Int) return Int is (X);

   --  Local variables

   Int_One  : constant Int := 1;
   X        : constant Int := Same (4);
   Y        : constant Int := Same (8);

   --  Constrained arrays

   A1  : constant Arr := (1, 2, 3, 4, 5);                  --  (1, 2, 3, 4, 5)
   A2  : constant Arr :=
      (1 => 1, 2 => 2, 3 => 3, 4 => 4, 5 => 5);            --  (1, 2, 3, 4, 5)
   A3  : constant Arr := (1 | 3 | 5 => 1, 2 | 4 => 2);     --  (1, 2, 1, 2, 1)
   A4  : constant Arr := (1 .. 3 => <>, 4 => 8, 5 => 9);   --  (1, 1, 1, 8, 9)
   A5  : constant Arr := (1 .. 3 => 7, others => 2);       --  (7, 7, 7, 2, 2)
   A6  : constant Arr := (2, others => 5);                 --  (2, 5, 5, 5, 5)
   A7  :          Arr;                                     --  (1, 1, 1, 1, 1)
   A8  : constant Arr := (Int_One .. 5 => Int_One);        --  (1, 1, 1, 1, 1)
   A9  : constant Arr := (for I in 1 .. 4 => I, 5 => 5);   --  (1, 2, 3, 4, 5)
   A10 : constant Arr := (A1 with delta 3 => 9);           --  (1, 2, 3, 4, 5)
   A11 : constant Arr := (for I in 1 | 3 .. 3 | 5 => 1,
                          others => 2);                    --  (1, 2, 1, 2, 1)
   A12 : constant Arr := (for I in Sub_Int | 5 => 1,
                          others => 9);                    --  (9, 1, 1, 1, 1)

   --  Unconstrained arrays

   AU1  : constant Arr_Unconstr := (1, 2, 3);                       --  (1, 2, 3)
   AU2  : constant Arr_Unconstr := (4 => 4, 5 => 5);                --  (4, 5)
   AU3  : constant Arr_Unconstr := (1 | 3 | 5 => 1, 2 | 4 => 2);    --  (1, 2, 1, 2, 1)
   AU4  : constant Arr_Unconstr := (1 .. 3 => <>, 4 => 8, 5 => 9);  --  (1, 1, 1, 8, 9)
   AU5  : constant Arr_Unconstr := (AU4 with delta 3 => 9);         --  (1, 1, 9, 8, 9)

   AU6  : constant Arr_Unconstr (1 .. 5) :=
      (1 .. 3 => 7, others => 2);                                   --  (7, 7, 7, 2, 2)
   AU7  : constant Arr_Unconstr (1 .. 5)      := (2, others => 5);  --  (2, 5, 5, 5, 5)

   AU8  : constant Arr_Unconstr := Dynamic_Bounds (2, 6);           --  (5, 5, 5, 5, 5)
   AU9  : constant Arr_Unconstr (3 .. 7) :=
      (AU8 with delta 4 => 9);                                      --  (5, 5, 9, 5, 5)
   AU10 : constant Arr_Unconstr (4 .. 6) := (1, 2, 3);              --  (1, 2, 3)
   AU11 : constant Arr_Unconstr := AU10;                            --  (1, 2, 3)
   AU12 : constant Arr_Unconstr (7 .. 9) := AU10;                   --  (1, 2, 3)
   AU13 : constant Arr_Unconstr (X .. Y) :=
      (5 | 7 => 2, others => 1);                                    --  (1, 2, 1, 2, 1)
   AU14 : constant Arr_Unconstr (X + 1 ..  Y + 1) := AU13;          --  (1, 2, 1, 2, 1)
   AU15 : constant Arr_Unconstr (X - 1 ..  Y - 1) := AU13;          --  (1, 2, 1, 2, 1)
   AU16 :          Arr_Unconstr (7 .. 9);                           --  (1, 1, 1)

   --  Array with non-contiguous indices

   ANC1 : constant Arr_Non_Contiguous := (for I in Power_Of_Two => 5);   --  (5, 5, 5, 5, 5, 5, 5)
   ANC2 : constant Arr_Non_Contiguous (Sub_POT1) := (1, 2, 4, 8, 16);    --  (1, 2, 4, 8, 16)
   ANC3 : constant Arr_Non_Contiguous (Sub_POT2) := ANC2;                --  (1, 2, 4, 8, 16)

begin

   Put_Line ("----------------------");
   Put_Line ("-- Array aggregates --");
   Put_Line ("----------------------");
   Put_Line ("");

   Put_Line ("Constrained arrays");
   Put_Line ("");

   Put_Line ("A1  : " & Boolean'Image (Check_Contents (A1 , 1, 2, 3, 4, 5)));
   Put_Line ("A2  : " & Boolean'Image (Check_Contents (A2 , 1, 2, 3, 4, 5)));
   Put_Line ("A3  : " & Boolean'Image (Check_Contents (A3 , 1, 2, 1, 2, 1)));
   Put_Line ("A4  : " & Boolean'Image (Check_Contents (A4 , 1, 1, 1, 8, 9)));
   Put_Line ("A5  : " & Boolean'Image (Check_Contents (A5 , 7, 7, 7, 2, 2)));
   Put_Line ("A6  : " & Boolean'Image (Check_Contents (A6 , 2, 5, 5, 5, 5)));
   Put_Line ("A7  : " & Boolean'Image (Check_Contents (A7 , 1, 1, 1, 1, 1)));
   Put_Line ("A8  : " & Boolean'Image (Check_Contents (A8 , 1, 1, 1, 1, 1)));
   Put_Line ("A9  : " & Boolean'Image (Check_Contents (A9 , 1, 2, 3, 4, 5)));
   Put_Line ("A10 : " & Boolean'Image (Check_Contents (A10, 1, 2, 9, 4, 5)));
   Put_Line ("A11 : " & Boolean'Image (Check_Contents (A11, 1, 2, 1, 2, 1)));
   Put_Line ("A12 : " & Boolean'Image (Check_Contents (A12, 9, 1, 1, 1, 1)));
   Put_Line ("");

   Put_Line ("Unconstrained arrays");
   Put_Line ("");

   Put_Line ("AU1  : " & Boolean'Image (Check_Contents (AU1 , 1, 2, 3)));
   Put_Line ("AU2  : " & Boolean'Image (Check_Contents (AU2 , 4, 5)));
   Put_Line ("AU3  : " & Boolean'Image (Check_Contents (AU3 , 1, 2, 1, 2, 1)));
   Put_Line ("AU4  : " & Boolean'Image (Check_Contents (AU4 , 1, 1, 1, 8, 9)));
   Put_Line ("AU5  : " & Boolean'Image (Check_Contents (AU5 , 1, 1, 9, 8, 9)));
   Put_Line ("AU6  : " & Boolean'Image (Check_Contents (AU6 , 7, 7, 7, 2, 2)));
   Put_Line ("AU7  : " & Boolean'Image (Check_Contents (AU7 , 2, 5, 5, 5, 5)));
   Put_Line ("AU8  : " & Boolean'Image (Check_Contents (AU8 , 5, 5, 5, 5, 5)));
   Put_Line ("AU9  : " & Boolean'Image (Check_Contents (AU9 , 5, 5, 9, 5, 5)));

   Put_Line ("AU10 : " & Boolean'Image (Check_Contents (AU10, 1, 2, 3)));
   Put_Line ("AU11 : " & Boolean'Image (Check_Contents (AU11, 1, 2, 3)));
   Put_Line ("AU12 : " & Boolean'Image (Check_Contents (AU12, 1, 2, 3)));
   Put_Line ("AU13 : " & Boolean'Image (Check_Contents (AU13, 1, 2, 1, 2, 1)));
   Put_Line ("AU14 : " & Boolean'Image (Check_Contents (AU14, 1, 2, 1, 2, 1)));
   Put_Line ("AU15 : " & Boolean'Image (Check_Contents (AU15, 1, 2, 1, 2, 1)));

   Put_Line ("AU10 bounds : " & Boolean'Image (Check_Bounds (AU10, 4, 6)));
   Put_Line ("AU11 bounds : " & Boolean'Image (Check_Bounds (AU11, 4, 6)));
   Put_Line ("AU12 bounds : " & Boolean'Image (Check_Bounds (AU12, 7, 9)));
   Put_Line ("AU13 bounds : " & Boolean'Image (Check_Bounds (AU13, 4, 8)));
   Put_Line ("AU14 bounds : " & Boolean'Image (Check_Bounds (AU14, 5, 9)));
   Put_Line ("AU15 bounds : " & Boolean'Image (Check_Bounds (AU15, 3, 7)));

   Put_Line ("AU16 before reassignment : "
            & Boolean'Image (Check_Contents (AU16, 1, 1, 1)));
   Put_Line ("AU16 bounds              : "
            & Boolean'Image (Check_Bounds (AU16, 7, 9)));
   AU16 := AU10;
   Put_Line ("AU15 after reassignment  : "
            & Boolean'Image (Check_Contents (AU16, 1, 2, 3)));
   Put_Line ("AU16 bounds              : "
            & Boolean'Image (Check_Bounds (AU16, 7, 9)));
   Put_Line ("");

   Put_Line ("Unconstrained arrays");
   Put_Line ("");

   Put_Line ("ANC1         : "
            & Boolean'Image (Check_Contents (ANC1, 5, 5, 5, 5, 5, 5, 5)));
   Put_Line ("ANC1 indices : "
            & Boolean'Image (Check_All_Indices (ANC1,
                                                One,
                                                Two,
                                                Four,
                                                Eight,
                                                Sixteen,
                                                Thirty_Two,
                                                Sixty_Four)));

   Put_Line ("ANC2         : "
            & Boolean'Image (Check_Contents (ANC2, 1, 2, 4, 8, 16)));
   Put_Line ("ANC2 indices : "
            & Boolean'Image
               (Check_All_Indices (ANC2, One, Two, Four, Eight, Sixteen)));

   Put_Line ("ANC3         : "
            & Boolean'Image (Check_Contents (ANC3, 1, 2, 4, 8, 16)));
   Put_Line ("ANC3 indices : "
            & Boolean'Image
               (Check_All_Indices
                  (ANC3, Four, Eight, Sixteen, Thirty_Two, Sixty_Four)));

end Main;
