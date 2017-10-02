with Ada.Text_IO;     use Ada.Text_IO;

with Bounded_Dynamic_Strings;

procedure Demo is

   type Dynamic_String is new Bounded_Dynamic_Strings.Sequence;
   --  a better name for a string wrapper

begin
   declare
      T1_Capacity : constant := 40; -- arbitrary
      T1_Value    : constant String := "";
      T1          : Dynamic_String := Instance (T1_Capacity, T1_Value);

      T2_Value    : constant String := "Goodbye Cruel World!!";
      T2          : Dynamic_String := Instance (T2_Value);
   begin
      pragma Assert (T1.Capacity = T1_Capacity,     "decl test 1");
      pragma Assert (T2.Capacity = T2_Value'Length, "decl test 2");
      pragma Assert (Value (T1) = T1_Value,         "decl test 3");
      pragma Assert (Value (T1) /= Value (T2),      "decl test 4");
      pragma Assert (T1 /= T2,                      "decl test 5");
      pragma Assert (Empty (T1),                    "decl test 6");
      pragma Assert (not Empty (T2),                "decl test 7");
      pragma Assert (Contains (T2, 'G'),            "decl test 8");
      pragma Assert (Contains (T2, "bye"),          "decl test 9");
      pragma Assert (Contains (T2, Value (T2)),     "decl test 10");
      pragma Assert (not Contains (T2, "lazy"),     "decl test 11");
      pragma Assert (not Contains (T2, ""),         "decl test 12");

      Clear (T1);
      Clear (T2);
      pragma Assert (Value (T1) = "", "clear test 1");
      pragma Assert (Value (T2) = "", "clear test 2");
      pragma Assert (Length (T1) = 0, "clear test 3");
      pragma Assert (Length (T2) = 0, "clear test 4");
   end;

   declare
      T1_Capacity : constant := 40; -- arbitrary
      T1_Value    : constant String := "";
      T1          : constant Dynamic_String := Instance (T1_Capacity, T1_Value);

      T2_Value    : constant String := "Goodbye Cruel World!!";
      T2          : Dynamic_String := Instance (T2_Value);
   begin
      pragma Assert (Value (T1) = "",         "copy test 1");
      pragma Assert (Value (T2) /= "",        "copy test 2");
      Copy (T1, To => T2);
      pragma Assert (Value (T2) = Value (T1), "copy test 3");
      Copy ("Hello", To => T2);
      pragma Assert (Value (T2) = "Hello",    "copy test 4");
      Copy ("", To => T2);
      pragma Assert (Value (T2) = "",         "copy test 5");
      Copy ('A', To => T2);
      pragma Assert (Value (T2) = "A",        "copy test 6");
   end;

   declare
      T1_Value    : constant String := " World";
      T2_Value    : constant String := "Goodbye Cruel";
      Final_Str   : constant String := T2_Value & T1_Value & "!?";
      T1_Capacity : constant := 40;  -- arbitrary
      T2_Capacity : constant Positive := Final_Str'Length;
      T1          : constant Dynamic_String := Instance (T1_Capacity, T1_Value);
      T2          : Dynamic_String := Instance (T2_Capacity, T2_Value);
   begin
      Append (T1, To => T2);
      pragma Assert (Value (T2) = T2_Value & T1_Value,       "append test 1");
      Append ("!", To => T2);
      pragma Assert (Value (T2) = T2_Value & T1_Value & "!", "append test 2");
      Append ('?', To => T2);
      pragma Assert (Value (T2) = Final_Str,                 "append test 3");
   end;

   declare
      T1_Capacity : constant := 40; -- arbitrary
      T1_Value    : constant String := "World";
      T1          : Dynamic_String := Instance (T1_Capacity, T1_Value);

      T2_Value    : constant String := "Goodbye World!!";
      T2          : constant Dynamic_String := Instance (T2_Value);

      Pos         : Natural;
   begin
      Pos := Location (T1, Within => T2);
      pragma Assert (Pos = 9, "location test 1, Pos is" & Pos'Img);
      Pos := Location (T1_Value, Within => T2);
      pragma Assert (Pos = 9, "location test 2, Pos is" & Pos'Img);
      Pos := Location ("!", Within => T2);
      pragma Assert (Pos = 14, "location test 3, Pos is" & Pos'Img);
      Pos := Location ('?', Within => T2);
      pragma Assert (Pos = 0, "location test 4, Pos is" & Pos'Img);
      Pos := Location (T2_Value, Within => T2);
      pragma Assert (Pos = 1, "location test 5, Pos is" & Pos'Img);

      Clear (T1);
      Pos := Location (T1, Within => T2);
      pragma Assert (Pos = 0, "location test 6, Pos is" & Pos'Img);
      Pos := Location ("", Within => T2);
      pragma Assert (Pos = 0, "location test 7, Pos is" & Pos'Img);
      Pos := Location (T2, Within => T1);
      pragma Assert (Pos = 0, "location test 8, Pos is" & Pos'Img);
   end;

   Put_Line ("All tests passed");
--  exception
--     when Error : others =>
--        Put_Line (Exception_Information (Error));
end Demo;
