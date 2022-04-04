package body Discrete is

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

   function In_Choice_List (C : Color) return Color_Kind is
      K : Color_Kind := Secondary;
   begin

     if C in Red | Green | Blue then
        K := Primary;
     end if;

     pragma Assert (K = Secondary); --  @ASSERT:FAIL @COUNTEREXAMPLE

     return K;
   end In_Choice_List;

   ------------------------
   -- Not_In_Choice_List --
   ------------------------

   function Not_In_Choice_List (C : Color) return Color_Kind is
      K : Color_Kind := Primary;
   begin

      if C not in Red | Green | Blue then
         K := Secondary;
      end if;

      pragma Assert (K = Primary);   --  @ASSERT:FAIL @COUNTEREXAMPLE

      return K;
   end Not_In_Choice_List;

   ------------------------------------
   -- In_Choice_List_Left_Not_Static --
   ------------------------------------

   function In_Choice_List_Left_Not_Static (T : Thing) return Color_Kind is
      K : Color_Kind := Secondary;
   begin

      if Get_Color_Of_Thing (T) in Red | Green | Blue then
       K := Primary;
      end if;

      pragma Assert (K = Secondary); --  @ASSERT:FAIL @COUNTEREXAMPLE

      return K;
   end In_Choice_List_Left_Not_Static;

   -------------------------------------
   -- In_Choice_List_Right_Not_Static --
   -------------------------------------

   function In_Choice_List_Right_Not_Static (C : Color) return Color_Kind is
      K : Color_Kind := Secondary;
   begin

      if C in Get_Color_Of_Thing (Blood)
            | Get_Color_Of_Thing (Grass)
            | Get_Color_Of_Thing (Sky)
      then
         K := Primary;
      end if;

      pragma Assert (K = Secondary);   --  @ASSERT:FAIL @COUNTEREXAMPLE

      return K;
    end In_Choice_List_Right_Not_Static;

   --------------
   -- In_Range --
   --------------

   function In_Range (C : Color) return Color_Kind is
      K : Color_Kind := Secondary;
   begin

      if C in Red .. Blue then
         K := Primary;
      end if;

      pragma Assert (K = Secondary); --  @ASSERT:FAIL @COUNTEREXAMPLE

      return K;
   end In_Range;

   ------------------
   -- Not_In_Range --
   ------------------

   function Not_In_Range (C : Color) return Color_Kind is
      K : Color_Kind := Primary;
   begin

      if C not in Red .. Blue then
         K := Secondary;
      end if;

      pragma Assert (K = Primary); --  @ASSERT:FAIL @COUNTEREXAMPLE

      return K;
   end Not_In_Range;

   ----------------
   -- In_Subtype --
   ----------------

   function In_Subtype (D : Day) return Boolean is
      Work : Boolean := True;
   begin

      if D in Weekday then
         Work := False;
      end if;

      pragma Assert (Work);          --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Work;
   end In_Subtype;

   --------------------
   -- Not_In_Subtype --
   --------------------

   function Not_In_Subtype (D : Day) return Boolean is
      Sleep : Boolean := True;
   begin

      if D not in Weekday then
         Sleep := False;
      end if;

      pragma Assert (Sleep);         --  @ASSERT:FAIL @COUNTEREXAMPLE

      return Sleep;
    end Not_In_Subtype;

   ---------
   -- Mix --
   ---------

   function Mix (M : Month) return Boolean is
      B : Boolean := True;
   begin

      --  Subtype, single value and range
      if M in Spring | Jul | Oct .. Dec then
        B := False;
      end if;

      pragma Assert (B);             --  @ASSERT:FAIL @COUNTEREXAMPLE

      return B;
   end Mix;

end Discrete;
