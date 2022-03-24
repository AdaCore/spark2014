with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

   type Int is range 1 .. 10;

   type Int_Array is array (Int) of Int;

   type Array_Record is record
      A : Int_Array := (others => 1);
   end record;

   function Same (I : in Int) return Int;

   function Same (A : in Int_Array) return Int_Array
      with Post => Same'Result = A;

   procedure Increment_Assert (I : in out Int)
      with Pre => I <= Int'Last - 3;

   procedure Increment_Invariant (I : in out Int)
      with Pre => I <= Int'Last - 3;

   procedure Increment_Array_Assert (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) < Int'Last);

   procedure Increment_Array_Invariant (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) < Int'Last);

   procedure Loop_Entry_On_Call_Assert (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) < Int'Last);

   procedure Loop_Entry_On_Call_Invariant (A : in out Int_Array)
      with Pre => (for all J in A'Range => A(J) < Int'Last);

   procedure Loop_Entry_On_Arr_In_Record_Assert (R : in out Array_Record)
      with Pre => (for all J in R.A'Range => R.A(J) < Int'Last);

   procedure Loop_Entry_On_Arr_In_Record_Invariant (R : in out Array_Record)
      with Pre => (for all J in R.A'Range => R.A(J) < Int'Last);

   procedure Loop_Entry_In_Call_Param (I : in Int);

   --  Implementations

   ----------
   -- Same --
   ----------

   function Same (I : in Int) return Int is (I);

   function Same (A : in Int_Array) return Int_Array is (A);

   ---------------
   -- Increment --
   ---------------

   procedure Increment_Assert (I : in out Int) is
   begin
      Put_Line ("I before:" & Int'Image (I));
      for J in 1 .. 3 loop
         I := I + 1;
         pragma Assert (I /= I'Loop_Entry);
         Put_Line ("I during:" & Int'Image (I));
      end loop;
      Put_Line ("I after: " & Int'Image (I));
   end Increment_Assert;

   procedure Increment_Invariant (I : in out Int) is
   begin
      Put_Line ("I before:" & Int'Image (I));
      for J in 1 .. 3 loop
         I := I + 1;
         pragma Loop_Invariant (I /= I'Loop_Entry);
         Put_Line ("I during:" & Int'Image (I));
      end loop;
      Put_Line ("I after: " & Int'Image (I));
   end Increment_Invariant;

   ---------------------
   -- Increment_Array --
   ---------------------

   procedure Increment_Array_Assert (A : in out Int_Array) is
   begin
      Put_Line ("Going to increment every element of A...");
      for J in A'Range loop
         A(J) := A(J) + 1;

         pragma Assert (A(J) = A'Loop_Entry(J) + 1);
         Put_Line ("A (" & Int'Image (J) & " ) incr:" & Int'Image (A(J)));
      end loop;
      Put_Line ("Incrementation finished.");
   end Increment_Array_Assert;

   procedure Increment_Array_Invariant (A : in out Int_Array) is
   begin
      Put_Line ("Going to increment every element of A...");
      for J in A'Range loop
         A(J) := A(J) + 1;

         pragma Loop_Invariant (for all K in A'First .. J =>
                                 A(K) = A'Loop_Entry(K) + 1);
         Put_Line ("A (" & Int'Image (J) & " ) incr:" & Int'Image (A(J)));
      end loop;
      Put_Line ("Incrementation finished.");
   end Increment_Array_Invariant;

   ------------------------
   -- Loop_Entry_On_Call --
   ------------------------

   procedure Loop_Entry_On_Call_Assert (A : in out Int_Array)
   is
      pragma Unevaluated_Use_Of_Old (Allow);
   begin
      Put_Line ("Going to increment every element of A...");
      for J in A'Range loop
         A(J) := A(J) + 1;

         pragma Assert (A(J) = Same (A)'Loop_Entry(J) + 1);
         Put_Line ("A (" & Int'Image (J) & " ) incr:" & Int'Image (A(J)));
      end loop;
      Put_Line ("Incrementation finished.");
   end Loop_Entry_On_Call_Assert;

   procedure Loop_Entry_On_Call_Invariant (A : in out Int_Array)
   is
      pragma Unevaluated_Use_Of_Old (Allow);
   begin
      Put_Line ("Going to increment every element of A...");
      for J in A'Range loop
         A(J) := A(J) + 1;

         pragma Loop_Invariant (for all K in A'First .. J =>
                                 A(K) = Same (A)'Loop_Entry(K) + 1);
         Put_Line ("A (" & Int'Image (J) & " ) incr:" & Int'Image (A(J)));
      end loop;
      Put_Line ("Incrementation finished.");
   end Loop_Entry_On_Call_Invariant;

   ---------------------------------
   -- Loop_Entry_On_Arr_In_Record --
   ---------------------------------

   procedure Loop_Entry_On_Arr_In_Record_Assert (R : in out Array_Record) is
   begin
      Put_Line ("Going to increment every element of R.A...");
      for J in R.A'Range loop
         R.A(J) := R.A(J) + 1;

         pragma Assert (R.A(J) = R.A'Loop_Entry(J) + 1);
         Put_Line ("R.A (" & Int'Image (J) & " ) incr:" & Int'Image (R.A(J)));
      end loop;
      Put_Line ("Incrementation finished.");
   end Loop_Entry_On_Arr_In_Record_Assert;

   procedure Loop_Entry_On_Arr_In_Record_Invariant (R : in out Array_Record) is
   begin
      Put_Line ("Going to increment every element of R.A...");
      for J in R.A'Range loop
         R.A(J) := R.A(J) + 1;

         pragma Loop_Invariant (for all K in R.A'First .. J =>
                                 R.A(K) = R.A'Loop_Entry(K) + 1);
         Put_Line ("R.A (" & Int'Image (J) & " ) incr:" & Int'Image (R.A(J)));
      end loop;
      Put_Line ("Incrementation finished.");
   end Loop_Entry_On_Arr_In_Record_Invariant;

   ------------------------------
   -- Loop_Entry_In_Call_Param --
   ------------------------------

   procedure Loop_Entry_In_Call_Param (I : in Int) is
   begin
      Put_Line ("Looping 3 times...");
      for J in 1 .. 3 loop
         pragma Assert (Same(I'Loop_Entry) = I);
         Put_Line (Integer'Image (J));
      end loop;
      Put_Line ("Done looping.");
   end Loop_Entry_In_Call_Param;

   --  Local variables

   I1 : Int := 1;
   I2 : Int := 1;

   A1 : Int_Array := (others => 1);
   A2 : Int_Array := (others => 1);
   A3 : Int_Array := (others => 1);
   A4 : Int_Array := (others => 1);

   R1 : Array_Record := (A => (others => 1));
   R2 : Array_Record := (A => (others => 1));

begin

   Put_Line ("Increment_Assert");
   Increment_Assert (I1);
   Put_Line ("");

   Put_Line ("Increment_Invariant");
   Increment_Invariant (I2);
   Put_Line ("");

   Put_Line ("Increment_Array_Assert");
   Increment_Array_Assert (A1);
   Put_Line ("");

   Put_Line ("Increment_Array_Invariant");
   Increment_Array_Invariant (A2);
   Put_Line ("");

   Put_Line ("Loop_Entry_On_Call_Assert");
   Loop_Entry_On_Call_Assert (A3);
   Put_Line ("");

   Put_Line ("Loop_Entry_On_Call_Invariant");
   Loop_Entry_On_Call_Invariant (A4);
   Put_Line ("");

   Put_Line("Loop_Entry_On_Arr_In_Record_Assert");
   Loop_Entry_On_Arr_In_Record_Assert (R1);
   Put_Line ("");

   Put_Line ("Loop_Entry_On_Arr_In_Record_Invariant");
   Loop_Entry_On_Arr_In_Record_Invariant (R2);
   Put_Line ("");

   Put_Line ("Loop_Entry_In_Call_Param");
   Loop_Entry_In_Call_Param (1);

end Main;
