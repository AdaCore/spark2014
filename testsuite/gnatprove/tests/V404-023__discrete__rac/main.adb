with Ada.Text_IO; use Ada.Text_IO;

procedure Main with SPARK_Mode is

   --  Color

   type Color is (Red, Green, Blue, Cyan, Magenta, Yellow);

   type Color_Kind is (Primary, Secondary);

   type Thing is (Blood, Grass, Sea, Sky, Flower, Sun);

   function Get_Color_Of_Thing (T : Thing) return Color;

   --  Time

   type Day is (Mon, Tue, Wed, Thu, Fri, Sat, Sun);

   subtype Weekday is Day range Mon .. Fri;

   type Month is (Jan, Feb, Mar, Apr, May, Jun, Jul, Aug, Sep, Oct, Nov, Dec);

   subtype Spring is Month range Mar ..  Jun;

   --  With a choice list

   procedure In_Choice_List (C : Color);

   procedure Not_In_Choice_List (C : Color);

   procedure In_Choice_List_Left_Not_Static (T : Thing);

   procedure In_Choice_List_Right_Not_Static (C : Color);

   --  With a range

   procedure In_Range (C : Color);

   procedure Not_In_Range (C : Color);

   --  With subtypes

   procedure In_Subtype (D : Day);

   procedure Not_In_Subtype (D : Day);

   --  Mix

   procedure Mix (M : Month);

   --  Implementations

   -------------------------
   -- Get_Colour_Of_Thing --
   -------------------------

   function Get_Color_Of_Thing (T : Thing) return Color is
   begin
      return (case T is
                 when Blood  => Red,
                 when Grass  => Green,
                 when Sea    => Blue,
                 when Sky    => Cyan,
                 when Flower => Magenta,
                 when Sun    => Yellow);

   end Get_Color_Of_Thing;

   --------------------
   -- In_Choice_List --
   --------------------

   procedure In_Choice_List (C : Color) is
      K : Color_Kind := Secondary;
   begin

      if C in Red | Green | Blue then
         K := Primary;
      end if;

      pragma Assert (K = Primary);
      Put_Line ("Color " & Color'Image (C) & " is Red, Green or Blue");

   end In_Choice_List;

   ------------------------
   -- Not_In_Choice_List --
   ------------------------

   procedure Not_In_Choice_List (C : Color) is
      K : Color_Kind := Primary;
   begin

      if C not in Red | Green | Blue then
         K := Secondary;
      end if;

      pragma Assert (K = Secondary);
      Put_Line ("Color " & Color'Image (C) & " is not Red, Green or Blue");

   end Not_In_Choice_List;

   ------------------------------------
   -- In_Choice_List_Left_Not_Static --
   ------------------------------------

   procedure In_Choice_List_Left_Not_Static (T : Thing) is
      K :          Color_Kind := Secondary;
      C : constant Color      := Get_Color_Of_Thing (T);
   begin

      if C in Red | Green | Blue then
         K := Primary;
      end if;

      pragma Assert (K = Primary);
      Put_Line ("Color " & Color'Image (C) & " is Red, Green or Blue");

   end In_Choice_List_Left_Not_Static;

   -------------------------------------
   -- In_Choice_List_Right_Not_Static --
   -------------------------------------

   procedure In_Choice_List_Right_Not_Static (C : Color) is
      K  :          Color_Kind := Secondary;
      C1 : constant Color      := Get_Color_Of_Thing (Blood);
      C2 : constant Color      := Get_Color_Of_Thing (Grass);
      C3 : constant Color      := Get_Color_Of_Thing (Sky);
   begin

      if C in C1 | C2 | C3 then
         K := Primary;
      end if;

      pragma Assert (K = Primary);
      Put_Line ("Color " & Color'Image (C) & " is "
                & Color'Image (C1) & ", "
                & Color'Image (C2) & " or "
                & Color'Image (C3));

    end In_Choice_List_Right_Not_Static;

   --------------
   -- In_Range --
   --------------

   procedure In_Range (C : Color) is
      K : Color_Kind := Secondary;
   begin

      if C in Red .. Blue then
         K := Primary;
      end if;

      pragma Assert (K = Primary);
      Put_Line ("Color " & Color'Image (C) & " is Red, Green or Blue");

   end In_Range;

   ------------------
   -- Not_In_Range --
   ------------------

   procedure Not_In_Range (C : Color) is
      K : Color_Kind := Primary;
   begin

      if C not in Red .. Blue then
         K := Secondary;
      end if;

      pragma Assert (K = Secondary);
      Put_Line ("Color " & Color'Image (C) & " is not Red, Green or Blue");

   end Not_In_Range;

   ----------------
   -- In_Subtype --
   ----------------

   procedure In_Subtype (D : Day) is
      Work : Boolean := True;
   begin

      if D in Weekday then
         Work := False;
      end if;

      pragma Assert (not Work);
      Put_Line (Day'Image (D) & " is a between Monday and Friday");

   end In_Subtype;

   --------------------
   -- Not_In_Subtype --
   --------------------

   procedure Not_In_Subtype (D : Day) is
      Sleep : Boolean := True;
   begin

      if D not in Weekday then
         Sleep := False;
      end if;

      pragma Assert (not Sleep);
      Put_Line (Day'Image (D) & " is Saturday or Sunday");

   end Not_In_Subtype;

   ---------
   -- Mix --
   ---------

   procedure Mix (M : Month) is
      B : Boolean := True;
   begin

      --  Subtype, single value and range
      if M in Spring | Jul | Oct .. Dec then
        B := False;
      end if;

      pragma Assert (not B);
      Put_Line (Month'Image (M)
                & " is in Spring, is July, or between October and December");
   end Mix;

begin
   Put_Line ("In_Choice_List");
   In_Choice_List (Green);
   Put_Line ("");

   Put_Line ("Not_In_Choice_List");
   Not_In_Choice_List (Yellow);
   Put_Line ("");

   Put_Line ("In_Choice_List_Left_Not_Static");
   In_Choice_List_Left_Not_Static (Blood);
   Put_Line ("");

   Put_Line ("In_Choice_List_Right_Not_Static");
   In_Choice_List_Right_Not_Static (Cyan);
   Put_Line ("");

   Put_Line ("In_Range");
   In_Range (Blue);
   Put_Line ("");

   Put_Line ("Not_In_Range");
   Not_In_Range (Magenta);
   Put_Line ("");

   Put_Line ("In_Subtype");
   In_Subtype (Tue);
   Put_Line ("");

   Put_Line ("Not_In_Subtype");
   Not_In_Subtype (Sat);
   Put_Line ("");

   Put_Line ("Mix");
   Mix (May);

end Main;
