with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

   type Int is range 1 .. 10;

   type Int_Array is array (Int) of Int;

   procedure Increment_Array_Nested_Loop_Simple (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) <= Int'Last - 2);

   procedure Increment_Array_Nested_Loop_Inner (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) <= Int'Last - 2);

   procedure Increment_Array_Nested_Loop_Outter (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) <= Int'Last - 2);

   procedure Very_Nested (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) <= Int'Last - 3);

   procedure Loop_Entry_In_Loop_Spec (I : in out Int)
      with Pre => I < Int'Last;

   --  Implementations

   ----------------------------------------
   -- Increment_Array_Nested_Loop_Simple --
   ----------------------------------------

   procedure Increment_Array_Nested_Loop_Simple (A : in out Int_Array) is
   begin
      Put_Line ("Going to increment every element of A twice...");
      Outter: for J in A'Range loop
         A(J) := A(J) + 1;
         Put_Line ("A (" & Int'Image (J) & " ) :" & Int'Image (A(J)));
         Inner: for K in Int(1) .. Int(1) loop   --  Only loop once
            A(J) := A(J) + K;
            pragma Assert (A(J) = A'Loop_Entry(J) + 1);
            Put_Line ("A (" & Int'Image (J) & " ) :" & Int'Image (A(J)));
         end loop Inner;
      end loop Outter;
      Put_Line ("Incrementation finished.");
   end Increment_Array_Nested_Loop_Simple;

   ---------------------------------------
   -- Increment_Array_Nested_Loop_Inner --
   ---------------------------------------

   procedure Increment_Array_Nested_Loop_Inner (A : in out Int_Array) is
   begin
      Put_Line ("Going to increment every element of A twice...");
      Outter: for J in A'Range loop
         A(J) := A(J) + 1;
         Put_Line ("A (" & Int'Image (J) & " ) :" & Int'Image (A(J)));
         Inner: for K in Int(1) .. Int(1) loop   --  Only loop once
            A(J) := A(J) + K;
            pragma Assert (A(J) = A'Loop_Entry(Inner)(J) + 1);
            Put_Line ("A (" & Int'Image (J) & " ) :" & Int'Image (A(J)));
         end loop Inner;
      end loop Outter;
      Put_Line ("Incrementation finished.");
   end Increment_Array_Nested_Loop_Inner;

   ----------------------------------------
   -- Increment_Array_Nested_Loop_Outter --
   ----------------------------------------

   procedure Increment_Array_Nested_Loop_Outter (A : in out Int_Array) is
   begin
      Put_Line ("Going to increment every element of A twice...");
      Outter: for J in A'Range loop
         A(J) := A(J) + 1;
         Put_Line ("A (" & Int'Image (J) & " ) :" & Int'Image (A(J)));
         Inner: for K in Int(1) .. Int(1) loop   --  Only loop once
            A(J) := A(J) + K;
            pragma Assert (A(J) = A'Loop_Entry(Outter)(J) + 2);
            Put_Line ("A (" & Int'Image (J) & " ) :" & Int'Image (A(J)));
         end loop Inner;
      end loop Outter;
      Put_Line ("Incrementation finished.");
   end Increment_Array_Nested_Loop_Outter;

   -----------------
   -- Very_Nested --
   -----------------

   procedure Very_Nested (A : in out Int_Array) is
   begin
      Put_Line ("Going to increment every element of A thrice...");
      One: for J in A'Range loop
         A(J) := A(J) + 1;
         Put_Line ("A (" & Int'Image (J) & " ) :" & Int'Image (A(J)));
         Two: for K in Int(1) .. Int(1) loop   --  Only loop once
            A(J) := A(J) + K;
            Put_Line ("A (" & Int'Image (J) & " ) :" & Int'Image (A(J)));
            Three: for L in Int(1) .. Int(1) loop   -- Only loop once
               A(J) := A(J) + K;
               pragma Assert (A(J) = A'Loop_Entry(One)(J) + 3);
               pragma Assert (A(J) = A'Loop_Entry(Two)(J) + 2);
               pragma Assert (A(J) = A'Loop_Entry(Three)(J) + 1);
               Put_Line ("A (" & Int'Image (J) & " ) :" & Int'Image (A(J)));
            end loop Three;
         end loop Two;
      end loop One;
      Put_Line ("Incrementation finished.");
   end Very_Nested;

   -----------------------------
   -- Loop_Entry_In_Loop_Spec --
   -----------------------------

   procedure Loop_Entry_In_Loop_Spec (I : in out Int) is
   begin
      Put_Line ("Loop once...");
      for J in Int(1) .. Int(1) loop   --  Only loop once
         I := I + 1;
         pragma Assert (for all K in 1 .. I'Loop_Entry => K = K);
         Put_Line (Int'Image (J));
      end loop;
      Put_Line ("Done looping");
   end Loop_Entry_In_Loop_Spec;

   --  Local variables

   A1 : Int_Array := (others => 1);
   A2 : Int_Array := (others => 1);
   A3 : Int_Array := (others => 1);
   A4 : Int_Array := (others => 1);

   I : Int := 1;

begin
   Put_Line ("Increment_Array_Nested_Loop_Simple");
   Increment_Array_Nested_Loop_Simple (A1);
   Put_Line ("");

   Put_Line ("Increment_Array_Nested_Loop_Inner");
   Increment_Array_Nested_Loop_Inner (A2);
   Put_Line ("");

   Put_Line ("Increment_Array_Nested_Loop_Outter");
   Increment_Array_Nested_Loop_Outter (A3);
   Put_Line ("");

   Put_Line ("Very_Nested");
   Very_Nested (A4);
   Put_Line ("");

   Put_Line ("Loop_Entry_In_Loop_Spec");
   Loop_Entry_In_Loop_Spec (I);

end Main;
