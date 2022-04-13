with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

   procedure Palindrome (Str : String)
      with Pre => True
   is
      Length, I, J, Stop : Integer;
   begin

      if Str = "" then
         Put_Line ("Empty string !!!");
      else
         Length := Str'Length;
         I      := Str'First;
         J      := Str'Last;
         Stop   := I + (Length - 1) / 2;

         while I < Stop and Str(I) = Str(J) loop
            I := I + 1;
            J := J - 1;

            pragma Loop_Invariant (I in I'Loop_Entry .. Stop);
            pragma Loop_Invariant (J in Stop .. J'Loop_Entry);
            pragma Loop_Invariant (I - I'Loop_entry = J'Loop_entry - J);
         end loop;

         Put_Line (Boolean'Image (I = Stop));
      end if;
   end Palindrome;

   -----------------
   -- Array Equal --
   -----------------

   type Arr is array (Integer range <>) of Integer;

   procedure Equal (A1, A2 : Arr) is
   begin
      if A1 = A2 then
         Put_Line ("Success");
      else
         Put_Line ("Failure");
      end if;
   end Equal;

   --  Local variables

   Int_First : constant Integer := Integer'First;
   Int_Last  : constant Integer := Integer'Last;

   Empty1 : constant Arr (2 .. 1)   := (others => 42);
   Empty2 : constant Arr (42 .. 24) := (others => 24);

   Ones1 : constant Arr (Int_First .. Int_First + 2) := (others => 1);
   Ones2 : constant Arr (Int_Last - 2 .. Int_Last) := (Int_Last - 2 => 1,
                                                       Int_Last - 1 => 1,
                                                       Int_Last     => 1);
   Ones3 : constant Arr (75 .. 75 + 2) := (76 => 1, others => 1);
   Ones4 : constant Arr (1 .. 3) := (1 => 1, 3 => 1, others => 1);

   Mix1 : constant Arr (1 .. 11) := (2  => 3,
                                     3  => 3,
                                     5  => 4,
                                     7  => 5,
                                     9  => 2,
                                     10 => 3,
                                     others => 1);
   Mix2 : constant Arr (5 .. 15) := (6  => 3,
                                     7  => 3,
                                     9 => 4,
                                     11 => 5,
                                     13 => 2,
                                     14 => 3,
                                     others => 1);
begin

   Put_Line ("----------------");
   Put_Line ("-- Palindrome --");
   Put_Line ("----------------");
   Put_Line ("");

   Put_Line ("Empty string :");
   Palindrome ("");
   Put_Line ("");

   Put_Line ("NotAPalindrome :");
   Palindrome ("NotAPalindrome");
   Put_Line ("");

   Put_Line ("ADA :");
   Palindrome ("ADA");
   Put_Line ("");

   Put_Line ("adaada :");
   Palindrome ("adaada");
   Put_Line ("");

   Put_Line ("-----------------");
   Put_Line ("-- Array Equal --");
   Put_Line ("-----------------");
   Put_Line ("");

   Equal (Empty1, Empty2);
   Equal (Ones1, Ones2);
   Equal (Ones3, Ones4);
   Equal (Mix1, Mix2);

end Main;
