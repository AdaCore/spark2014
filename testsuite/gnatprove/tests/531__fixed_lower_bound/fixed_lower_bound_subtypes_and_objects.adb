with Ada.Text_IO;  use Ada.Text_IO;

procedure Fixed_Lower_Bound_Subtypes_And_Objects is

   Str_Const : constant String := "abcdefg";

   subtype FLB_String is String (1 .. <>);

   Str1 : FLB_String := Str_Const (2 .. 5);  -- Sliding performed here

   pragma Assert (Str1'First = 1);

   Str2 : String (2 .. <>) := Str_Const;

   procedure Print (A : FLB_String) is
   begin
      pragma Assert (A'First = 1);

      Put_Line ("A = """ & A & """");
      Put_Line ("A'first =" & A'first'Image);
      Put_Line ("A'last  =" & A'last'Image);
   end Print;

   procedure Pass_String (S : String) is

      FS1 : FLB_String := S;                -- Sliding performed here
      FS2 : String (S'Last .. <>) := S;     -- Sliding performed here

   begin
      pragma Assert (FS1'First = 1);
      pragma Assert (FS2'First = S'Last);

      Put_Line ("FS1 = """ & FS1 & """");
      Put_Line ("FS1'first =" & FS1'first'Image);
      Put_Line ("FS1'last  =" & FS1'last'Image);

      Put_Line ("FS2 = """ & FS2 & """");
      Put_Line ("FS2'first =" & FS2'first'Image);
      Put_Line ("FS2'last  =" & FS2'last'Image);
   end Pass_String;

   S : String (2 .. 11) := "0123456789";

begin
   Print (Str1);
   Print (Str2);

   Pass_String (S);

   Pass_String (S (5 .. 10));

   declare
      type Arr is array (Integer range <>) of Integer;
      type Arr_FLB_1 is array (Integer range 1 .. <>) of Integer;

      A07 : Arr (0 .. 7);
      AFLB10 : Arr_FLB_1 (1 .. 10);

      procedure Pass_Arr (A : Arr) is
      begin
         pragma Assert (A'First = 1);

         Put_Line ("A'first =" & A'first'Image);
         Put_Line ("A'last  =" & A'last'Image);
      end Pass_Arr;

   begin
      declare
         AF1 : Arr_FLB_1 := Arr_FLB_1 (A07);             -- Sliding conversion
         AF2 : Arr_FLB_1 := Arr_FLB_1 (AFLB10 (2 .. 7)); -- Sliding conversion
      begin
         Pass_Arr (Arr (AF1));
         Pass_Arr (Arr (AF2));
      end;
   exception
     when others =>
        Put_Line ("FAILED: unexpected exception raised for OK conversion");
   end;

   declare
      Cstr : FLB_String (2 .. 10);  -- Raise CE due to inconsistent FLB
   begin
      raise Program_Error;  -- Shouldn't execute this
   end;

exception
  when Constraint_Error =>
     Put_Line ("Fixed-lower-bound consistency check raised CE");
  when others =>
     Put_Line ("FAILED: Some unexpected exception raised");
end Fixed_Lower_Bound_Subtypes_And_Objects;
