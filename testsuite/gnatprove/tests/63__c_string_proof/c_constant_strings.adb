pragma Assertion_Policy (Ignore);

with SPARK.Cut_Operations; use SPARK.Cut_Operations;

package body C_Constant_Strings with SPARK_Mode => On is

   -----------------------
   -- Local Subprograms --
   -----------------------

   function Find_Nul (Chars : Char_Array) return Size_T with
     Pre  => Is_Nul_Terminated (Chars),
     Post => Find_Nul'Result = Chars'First + C_Length_Ghost (Chars);

   function Value_Def (Item : chars_ptr) return char_array is
      (for I in 0 .. Strlen (Item) => Item (Item'First + I))
   with Pre => Item /= Null_Ptr,
     Annotate => (GNATprove, Hide_Info, "Expression_Function_Body");

   --------------
   -- Find_Nul --
   --------------

   function Find_Nul (Chars : Char_Array) return Size_T is
   begin
      for I in Chars'Range loop
         if Chars (I) = Nul then
            return I;
         end if;
         pragma Loop_Invariant
           (for all J in Chars'First .. I => Chars (J) /= Nul);
      end loop;
      raise Program_Error;
   end Find_Nul;

   ----------
   -- Free --
   ----------

   procedure Free (Item : in out chars_ptr) is null
   with
     SPARK_Mode => Off;

   --------------------
   -- From_Chars_Ptr --
   --------------------

   function From_Chars_Ptr
     (Item : chars_ptr) return Interfaces.C.Strings.chars_ptr
   is
     (raise Program_Error)
   with
     SPARK_Mode => Off;

   --------------------
   -- New_Char_Array --
   --------------------

   function New_Char_Array (Chars : char_array) return chars_ptr is
     (raise Program_Error)
   with
     SPARK_Mode => Off;

   ----------------
   -- New_String --
   ----------------

   function New_String (Str : String) return chars_ptr is
     (raise Program_Error)
   with
     SPARK_Mode => Off;

   ------------
   -- Strlen --
   ------------

   function Strlen (Item : Chars_Ptr) return Size_T is
     (if Item = null then 0 else Find_Nul (Item.all) - Item'First);

   ------------------
   -- To_Chars_Ptr --
   ------------------

   function To_Chars_Ptr
     (Item      : const_char_array_access;
      Nul_Check : Boolean := False) return chars_ptr
   is
      pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Value_Def);
   begin
      return Chars_Ptr (Item);
   end To_Chars_Ptr;

   function To_Chars_Ptr
     (Item      : Interfaces.C.Strings.char_array_access;
      Nul_Check : Boolean := False) return chars_ptr
   is
     (raise Program_Error)
   with
     SPARK_Mode => Off;

   function To_Chars_Ptr
     (Item : Interfaces.C.Strings.chars_ptr) return chars_ptr
   is
     (raise Program_Error)
   with
     SPARK_Mode => Off;

   -----------
   -- Value --
   -----------

   function Value (Item : chars_ptr) return char_array is
    (Value_Def (Item));
   pragma Annotate (GNATprove, Unhide_Info, "Expression_Function_Body", Value_Def);

   function Value
     (Item   : Chars_Ptr;
      Length : Size_T) return Char_Array
   is
      Res_V : constant Char_Array := Value (Item);
   begin
      if Res_V'Last <= Length - 1 then
         return Res_V;
      else
         return Res_V (0 .. Length - 1);
      end if;
   end Value;

   function Value (Item : Chars_Ptr) return String is
   begin
      return Res : String := To_Ada (Value (Item), Trim_Nul => True) do
         pragma Assert
           (for all I in Res'Range =>
              Res (I) = To_Ada (Value (Item) (Size_T (I - 1))));
      end return;
   end Value;

   function Value
     (Item   : Chars_Ptr;
      Length : Size_T) return String
   is
      Res_V : constant Char_Array := Value (Item, Length);
   begin
      if Is_Nul_Terminated (Res_V) then
         pragma Assert (Length > Strlen (Item));
         pragma Assert (for all I in Res_V'Range =>
                          (if I /= Res_V'Last then Res_V (I) /= Nul));
         declare
            Res : constant String := To_Ada (Res_V, Trim_Nul => True);
         begin
            pragma Assert (Res'Length = C_Length_Ghost (Res_V));
            pragma Assert (for all I in Res'Range =>
                             By
                               (Res (I) = To_Ada (Value (Item) (Size_T (I - 1))),
                                Res (I) = To_Ada (Res_V (Size_T (I) - 1 + 0))));
            pragma Assert (if Strlen (Item) <= Size_T (Natural'Last)
                           then (for all I in Res'Range =>
                                   By
                                     (Res (I) = Value (Item) (I),
                                      Value (Item) (I) = To_Ada (Value (Item) (Size_T (I - 1))))));
            return Res;
         end;
      else
         pragma Assert (for all I in Res_V'Range => Value (Item) (I) /= Nul);
         pragma Assert (Strlen (Item) >= Length);
         declare
            Res_N : constant Char_Array := Res_V & Nul;
            pragma Assert (Res_N (Res_N'Last) = Nul);
            pragma Assert (Is_Nul_Terminated (Res_N));
            Res   : constant String := To_Ada (Res_N, Trim_Nul => True);
         begin
            pragma Assert (Res'Length = Res_V'Length);
            pragma Assert (for all I in Res'Range =>
                             By
                               (Res (I) = To_Ada (Value (Item) (Size_T (I - 1))),
                                Res (I) = To_Ada (Res_V (Size_T (I) - 1 + 0))));
            pragma Assert (if Strlen (Item) <= Size_T (Natural'Last)
                           then (for all I in Res'Range =>
                                   By
                                     (Res (I) = Value (Item) (I),
                                      Value (Item) (I) = To_Ada (Value (Item) (Size_T (I - 1))))));
            return Res;
         end;
      end if;
   end Value;

end C_Constant_Strings;
