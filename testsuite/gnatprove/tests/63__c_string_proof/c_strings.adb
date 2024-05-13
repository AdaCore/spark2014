pragma Assertion_Policy (Ignore);

with SPARK.Cut_Operations; use SPARK.Cut_Operations;
with Ada.Unchecked_Deallocation;

package body C_Strings with SPARK_Mode is

   -----------------------
   -- Local Subprograms --
   -----------------------

   procedure Free_chars_ptr is
     new Ada.Unchecked_Deallocation (Char_Array, Chars_Ptr);

   function Find_Nul (Chars : Char_Array) return Size_T with
     Pre  => Is_Nul_Terminated (Chars),
     Post => Find_Nul'Result = Chars'First + C_Length_Ghost (Chars);

   procedure Lemma_Is_Find_Nul (Chars : Char_Array; P : size_t) with
     Ghost,
     Pre => P in Chars'Range
     and then Chars (P) = nul
     and then (for all I in Chars'First .. P => (if I < P then Chars (I) /= nul)),
     Post => Is_Nul_Terminated (Chars)
     and then P = Find_Nul (Chars);

   --------------------
   -- C_Length_Ghost --
   --------------------

   function C_Length_Ghost (Item : char_array) return size_t is
   begin
      for J in Item'Range loop
         if Item (J) = nul then
            return J - Item'First;
         end if;

         pragma Loop_Invariant
           (for all K in Item'First .. J => Item (K) /= nul);
      end loop;

      raise Program_Error;
   end C_Length_Ghost;

   function C_Length_Ghost (Item : String) return Natural is
   begin
      for J in Item'Range loop
         if Item (J) = Character'First then
            return J - Item'First;
         end if;

         pragma Loop_Invariant
           (for all K in Item'First .. J => Item (K) /= Character'First);
      end loop;

      raise Program_Error;
   end C_Length_Ghost;

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

   procedure Free (Item : in out chars_ptr) is
   begin
      Free_Chars_Ptr (Item);
   end Free;

   --------------------
   -- From_Chars_Ptr --
   --------------------

   function From_Chars_Ptr
     (Item : chars_ptr) return Interfaces.C.Strings.chars_ptr
   is
     (raise Program_Error)
   with
     SPARK_Mode => Off;

   -----------------------------
   -- Is_Nul_Terminated_Ghost --
   -----------------------------

   function Is_Nul_Terminated_Ghost (Item : String) return Boolean is
   begin
      for J in Item'Range loop
         if Item (J) = Character'First then
            return True;
         end if;

         pragma Loop_Invariant
           (for all K in Item'First .. J => Item (K) /= Character'First);
      end loop;

      return False;
   end Is_Nul_Terminated_Ghost;

   -----------------------
   -- Lemma_Is_Find_Nul --
   -----------------------

   procedure Lemma_Is_Find_Nul (Chars : Char_Array; P : size_t) is null;

   --------------------
   -- New_Char_Array --
   --------------------

   function New_Char_Array (Chars : Char_Array) return Chars_Ptr is
      Found      : Boolean := False;
      First_Null : Size_T with Relaxed_Initialization;
   begin
      for I in Chars'Range loop
         if Chars (I) = Nul then
            Found := True;
            First_Null := I;
            Lemma_Is_Find_Nul (Chars, First_Null);
            exit;
         end if;
         pragma Loop_Invariant
           (for all J in Chars'First .. I => Chars (J) /= Nul);
      end loop;

      if Found then
         declare
            L_Res : constant Size_T := First_Null - Chars'First;
            Res   : constant Char_Array (0 .. L_Res) :=
              Chars (Chars'First .. First_Null);
         begin
            Lemma_Is_Find_Nul (Res, L_Res);
            pragma Assert (L_Res = C_Length_Ghost (Chars));
            pragma Assert
              (for all I in 0 .. C_Length_Ghost (Chars) =>
                   Res (I) = Chars (Chars'First + I));
            return new Char_Array'(Res);
         end;
      elsif Chars'Length = 0 then
         declare
            Res : constant Char_Array := (0 => Nul);
         begin
            pragma Assert (Find_Nul (Res) = 0);
            return new Char_Array'(Res);
         end;
      else
         declare
            Left : constant Char_Array (0 .. Chars'Length - 1) := Chars;
            Res  : constant Char_Array := Left & Nul;
         begin
            pragma Assert
              (for all I in Chars'Range => Chars (I) /= Nul);
            pragma Assert
              (for all I in 0 .. Size_T (Chars'Length - 1) =>
                 By
                   (Res (I) = Chars (Chars'First + I),
                    Left (I) = Chars (Chars'First + I)));
            pragma Assert
              (for all I in 0 .. Size_T (Chars'Length - 1) =>
                 By
                   (Res (I) /= Nul,
                    Res (I) = Chars (Chars'First + I)
                 and then By
                    (Chars (Chars'First + I) /= Nul,
                     Chars'First + I in Chars'Range)));
            pragma Assert (Res (Res'Last) = Nul);
            Lemma_Is_Find_Nul (Res, Chars'Length);
            return new Char_Array'(Res);
         end;
      end if;
   end New_Char_Array;

   ----------------
   -- New_String --
   ----------------

   function New_String (Str : String) return Chars_Ptr is
      procedure Lemma_C_Length_Ghost_To_C (Str : String) with
        Ghost,
        Post => C_Length_Ghost (To_C (Str)) =
          (if Is_Nul_Terminated_Ghost (Str)
           then size_t (C_Length_Ghost (Str))
           else Str'Length);

      procedure Lemma_C_Length_Ghost_To_C (Str : String) is
         Res : constant Size_T :=
          (if Is_Nul_Terminated_Ghost (Str)
           then size_t (C_Length_Ghost (Str))
           else Str'Length);
      begin
         if Str'Length > 0 then
            pragma Assert
              (for all I in 0 .. Size_T (Str'Length) - 1 =>
                 To_C (Str) (I) = To_C (Str (Natural (I) + Str'First)));
            pragma Assert (To_C (Str) (Res) = nul);
            pragma Assert
              (for all I in 0 ..  Res =>
                 (if I < Res then To_C (Str) (I) /= Nul));
         end if;
      end Lemma_C_Length_Ghost_To_C;

      Res : Chars_Ptr := New_Char_Array (To_C (Str));
   begin
      Lemma_C_Length_Ghost_To_C (Str);
      pragma Assert
        (if Strlen (Res) > 0 then
             (for all I in 1 .. Natural (Strlen (Res)) =>
                By
                  (Value (Res) (I) = Str (Str'First + (I - 1)),
                   Value (Res) (I) = To_Ada (Value (Res) (Size_T (I - 1)))
                   and Value (Res) (Size_T (I - 1)) = To_C (Str) (Size_T (I - 1))
                   and To_C (Str) (Size_T (I - 1)) = To_C (Str (Str'First + Natural (Size_T (I - 1)))))));
      return Res;
   end New_String;

   ------------
   -- Strlen --
   ------------

   function Strlen (Item : Chars_Ptr) return Size_T is
     (Find_Nul (Item.all));

   ------------------
   -- To_Chars_Ptr --
   ------------------

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

   ------------
   -- Update --
   ------------

   procedure Update
     (Item   : in out Chars_Ptr;
      Offset : Size_T;
      Chars  : Char_Array;
      Check  : Boolean := True)
   is
      Old_Val : constant Char_Array := Item.all with Ghost;
      Old_Len : constant Size_T := Strlen (Item) with Ghost;
   begin
      if Chars'Length > 0 then
         pragma Assert (Old_Len > 0);
         Item (Offset .. Offset + (Chars'Length - 1)) := Chars;
         pragma Assert
           (for all I in 0 .. Old_Len =>
              (if I in Offset .. Offset + (Chars'Length - 1)
               then Item (I) = Chars (I - Offset + Chars'First)
               else Item (I) = Old_Val (I)));
         if Is_Nul_Terminated (Chars) then
            declare
               New_Last : constant Size_T := Offset + C_Length_Ghost (Chars) with Ghost;
            begin
               pragma Assert
                 (By
                    (Item (New_Last) = Nul,
                     Item (New_Last) = Chars (New_Last - Offset + Chars'First)));
               pragma Assert
                 (for all I in 0 .. New_Last =>
                    (if I < New_Last
                     then By
                       (Item (I) /= Nul,
                        (if I < Offset
                         then By
                           (Item (I) /= Nul,
                            By (Old_Val (I) /= Nul, I < Old_Len))
                         else By
                           (Item (I) /= Nul,
                            So (I - Offset + Chars'First < Chars'First + C_Length_Ghost (Chars),
                                Chars (I - Offset + Chars'First) /= Nul))))));
               Lemma_Is_Find_Nul (Item.all, New_Last);
               pragma Assert (Strlen (Item) = New_Last);
            end;
         else
            pragma Assert (Item (Old_Len) = Nul);
            pragma Assert
              (for all I in 0 .. Old_Len - 1 =>
                 By
                   (Item (I) /= Nul,
                    (if I < Offset or I > Offset + (Chars'Length - 1)
                     then By
                       (Item (I) /= Nul,
                        By (Old_Val (I) /= Nul, I < Old_Len))
                     else By
                       (Item (I) /= Nul,
                        Chars (I - Offset + Chars'First) /= Nul))));
            Lemma_Is_Find_Nul (Item.all, Old_Len);
            pragma Assert (Strlen (Item) = Old_Len);
         end if;
      end if;
   end Update;

   procedure Update
     (Item   : in out Chars_Ptr;
      Offset : Size_T;
      Str    : String;
      Check  : Boolean := True)
   is
      procedure Lemma_C_Length_Ghost_To_C (Str : String) with
        Ghost,
        Pre  => Str'Length > 0,
        Post => (Is_Nul_Terminated (To_C (Str, Append_Nul => False)) =
                   Is_Nul_Terminated_Ghost (Str))
        and (if Is_Nul_Terminated_Ghost (Str)
             then C_Length_Ghost (To_C (Str, Append_Nul => False)) =
                 Size_T (C_Length_Ghost (Str)));

      procedure Lemma_C_Length_Ghost_To_C (Str : String) is
      begin
         if Str'Length > 0 then
            pragma Assert
              (for all I in 0 .. Size_T (Str'Length) - 1 =>
                 To_C (Str, Append_Nul => False) (I) = To_C (Str (Natural (I) + Str'First)));
            if Is_Nul_Terminated_Ghost (Str) then
               pragma Assert (To_C (Str, Append_Nul => False) (Size_T (C_Length_Ghost (Str))) = Nul);
               pragma Assert
                 (for all I in 0 .. Size_T (C_Length_Ghost (Str)) =>
                    (if I < Size_T (C_Length_Ghost (Str)) then To_C (Str, Append_Nul => False) (I) /= Nul));
            else
               pragma Assert
                 (for all I in 0 .. Size_T (Str'Length) - 1 =>
                      To_C (Str, Append_Nul => False) (I) /= Nul);
            end if;
         end if;
      end Lemma_C_Length_Ghost_To_C;

      Old_Len     : constant Size_T := Strlen (Item) with Ghost;
      Old_Val     : constant Char_Array := Item.all with Ghost;
      Old_Val_Str : constant String :=
        (if Old_Len <= Size_T (Natural'Last) then Value (Item) else "") with Ghost;
   begin
      if Str'Length > 0 then
         declare
            Chars : constant Char_Array := To_C (Str, Append_Nul => False);
         begin
            Lemma_C_Length_Ghost_To_C (Str);
            Update (Item, Offset, Chars, Check);
            pragma Assert
              (for all I in 0 .. Strlen (Item) =>
                   (if I in Offset .. Offset + Chars'Length - 1
                    then Natural (I - Offset) < Chars'Length
                    and then By
                      (Item (I) = To_C (Str (Natural (I - Offset) + Str'First)),
                       Item (I) = Chars (I - Offset + Chars'First))
                    else Item (I) = Old_Val (I)));
            pragma Assert
              (if Old_Len <= Size_T (Natural'Last) then
                   (for all I in 1 .. Natural (Strlen (Item)) =>
                        (if Str'Length > 0
                         and then I in Natural (Offset + 1) .. Natural (Offset + Str'Length)
                         then By
                           (String'(Value (Item)) (I) = Str (I - Natural (Offset + 1) + Str'First),
                            So
                              (I - Natural (Offset + 1) < Str'Length,
                               By
                                 (To_Ada (Item (Size_T (I - 1))) = Str (I - Natural (Offset + 1) + Str'First),
                                  So
                                    (Size_T (I - 1) in Offset .. Offset + Str'Length - 1
                                     and Size_T (I - 1) in 0 .. Strlen (Item)
                                     and Natural (Size_T (I - 1) - Offset) < Str'Length,
                                     Item (Size_T (I - 1)) = To_C (Str (Natural (Size_T (I - 1) - Offset) + Str'First)))))
                            and By
                              (String'(Value (Item)) (I) = To_Ada (Item (Size_T (I - 1))),
                               Item (Size_T (I - 1)) = Char_Array'(Value (Item)) (Size_T (I - 1))))
                         else By
                           (String'(Value (Item)) (I) = Old_Val_Str (I),
                            So
                              (Size_T (I - 1) in 0 .. Strlen (Item),
                               By
                                 (To_Ada (Item (Size_T (I - 1))) = To_Ada (Old_Val (Size_T (I - 1))),
                                  By
                                    (Item (Size_T (I - 1)) = Old_Val (Size_T (I - 1)),
                                     Size_T (I - 1) not in Offset .. Offset + Str'Length - 1
                                     and Size_T (I - 1) in Old_Val'Range))
                               and By
                                 (String'(Value (Item)) (I) = To_Ada (Item (Size_T (I - 1))),
                                  Item (Size_T (I - 1)) = Char_Array'(Value (Item)) (Size_T (I - 1)))
                               and By
                                 (Old_Val_Str (I) = To_Ada (Old_Val (Size_T (I - 1))),
                                  Old_Val (Size_T (I - 1)) = Value (Item) (Size_T (I - 1))))))));
         end;
      end if;
   end Update;

   -----------
   -- Value --
   -----------

   function Value (Item : Chars_Ptr) return Char_Array is
     (Item.all (0 .. Find_Nul (Item.all)));

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
      return To_Ada (Value(Item), Trim_Nul => True);
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
            Res   : constant String := To_Ada (Res_N, Trim_Nul => True);
         begin
            pragma Assert
              (By (Res'Length = Res_V'Length, C_Length_Ghost (Res_N) = Res_V'Length));
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

end C_Strings;
