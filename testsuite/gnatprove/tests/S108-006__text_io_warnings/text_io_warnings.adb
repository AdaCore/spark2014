with Ada.Text_IO; use Ada.Text_IO;

procedure Text_IO_Warnings with
  SPARK_Mode,
  Pre => Line_Length = 0 and Page_Length = 0
is
   Source : File_Type;
   type Int_Num is range -20..20;
   package Int_IO is new Integer_IO (Int_Num); use Int_IO;
   Int_Get : Int_Num;
   Sum : Integer := 0;


   Target : File_Type;
   Nat : Natural;
   Ch : Character;
   Bool : Boolean;
   Str : String(1..6);
   A_Line : String(1..40);
begin
   Open (Source, In_File, "source.txt");
   Set_Col (Source, 5);
   for J in 1..100 loop
      Get (Source, Int_Get);
      Sum := Sum + Integer(Int_Get);
      pragma Loop_Invariant (Sum in J*(-20) .. J*(20));
   end loop;
   Reset (Source, Append_File);
   Set_Col (Source, 3);
   Set_Line_Length (Source, 30);
   Set_Col (Source, 5);
   Set_Col (Source, 31);
   if Sum in -20 .. 20 then
      Put (Source, Int_Num(Sum));
   end if;
   New_Line (Source);
   Close (Source);


   Create (Target, Out_File, "target.txt");
   Set_Col (Target, 1);
   Open (Source, In_File, "source.txt");
   Set_Col (Source, 1);
   pragma Assert (Mode (Target) = Out_File);
   Put_Line (Target, Name (Target));
   Put_Line (Target, Form (Target));
   pragma Assert (Is_Open (Target));

   Flush (Target);
   Flush;

   Set_Line_Length (Target, 40);
   pragma Assert (Line_Length (Target) = 40);
   Set_Line_Length (40);
   pragma Assert (Line_Length = 40);

   Set_Page_Length (Target, 80);
   pragma Assert (Page_Length (Target) = 80);
   Set_Page_Length (80);
   pragma Assert (Page_Length = 80);

   New_Line (Target);
   New_Line;

   Skip_Line (Source, 2);
   Skip_Line (2);

   Put_Line (Target, Boolean'Image (End_Of_Line (Source)));
   Put_Line (Boolean'Image (End_Of_Line));

   New_Page (Target);
   New_Page;

   Skip_Page (Source);
   Skip_Page;

   Put_Line (Target, Boolean'Image (End_Of_Page (Source)));
   Put_Line (Boolean'Image (End_Of_Page));

   Put_Line (Target, Boolean'Image (End_Of_File (Source)));
   Put_Line (Boolean'Image (End_Of_File));

   Set_Col (Target, 8);
   Set_Col (8);

   Set_Line (Target, 2);
   Set_Line (2);

   Put_Line (Target, Count'Image (Col (Target)));
   Put_Line (Count'Image (Col));
   Put_Line (Target, Count'Image (Line (Target)));
   Put_Line (Count'Image (Line));
   Put_Line (Target, Count'Image (Page (Target)));
   Put_Line (Count'Image (Page));

   Reset (Source);
   Reset (Target, Out_File);

   Get (Source, Ch);
   Put (Target, Ch);
   Get (Ch);
   Put (Ch);

   Look_Ahead (Source, Ch, Bool);
   if not Bool then
      Put (Target, Ch);
   end if;
   Look_Ahead (Ch, Bool);
   if not Bool then
      Put (Target, Ch);
   end if;
   Get_Immediate (Source, Ch);
   Put (Target, Ch);
   Get_Immediate (Ch);
   Put (Ch);
   Get_Immediate (Source, Ch, Bool);
   if Bool then
      Put (Target, Ch);
   end if;
   Get_Immediate (Ch, Bool);
   if Bool then
      Put (Ch);
   end if;

   Get (Source, Str);
   Put (Target, Str);
   Get (Str);
   Put (Str);

   Get_Line (Source, A_Line, Nat);
   Put_Line (Target, A_Line(1..Nat));
   Get_Line (A_Line, Nat);
   Put_Line (A_Line(1..Nat));

   Delete (Source);
   Close (Target);
end Text_IO_Warnings;
