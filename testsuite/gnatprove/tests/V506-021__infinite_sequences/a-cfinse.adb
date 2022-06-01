pragma Ada_2012;

with Ada.Assertions;

with Ada.Text_IO; use Ada.Text_IO;

package body Ada.Containers.Functional_Infinite_Sequences
with SPARK_Mode => Off
is
   use Containers;
   use Ada.Assertions;
   -----------------------
   -- Local Subprograms --
   -----------------------

   package Big_From_Count is new Signed_Conversions
     (Int => Count_Type);

   function Big (C : Count_Type) return Big_Integer renames
     Big_From_Count.To_Big_Integer;

   --  Store Count_Type'Last as a Big Natural because it is often used

   Count_Type_Big_Last : Big_Natural := Big (Count_Type'Last);

   function To_Count (C : Big_Natural) return Count_Type is
   begin
      --  Put_Line (To_String (C));
      pragma Assert (C <= Count_Type_Big_Last);
      return Big_From_Count.From_Big_Integer (C);
   end To_Count;

   ---------
   -- "=" --
   ---------

   function "=" (Left : Sequence; Right : Sequence) return Boolean is
     (Left.Content = Right.Content);

   ---------
   -- "<" --
   ---------

   function "<" (Left : Sequence; Right : Sequence) return Boolean is
     (Length (Left) < Length (Right)
      and then (for all N in Left =>
                     Get (Left, N) = Get (Right, N)));

   ----------
   -- "<=" --
   ----------

   function "<=" (Left : Sequence; Right : Sequence) return Boolean is
     (Length (Left) <= Length (Right)
      and then (for all N in Left =>
                     Get (Left, N) = Get (Right, N)));

   ---------
   -- Add --
   ---------

   function Add (Container : Sequence; New_Item : Element_Type) return Sequence
   is
     (Add (Container, Last (Container) + 1, New_Item));

   function Add
     (Container : Sequence;
      Position  : Big_Positive;
      New_Item  : Element_Type) return Sequence is
     (Content => Add (Container.Content, To_Count (Position), New_Item));

   --------------------
   -- Constant_Range --
   --------------------

   function Constant_Range
     (Container : Sequence;
      Fst       : Big_Positive;
      Lst       : Big_Natural;
      Item      : Element_Type) return Boolean
   is
      Count_Fst : Count_Type := To_Count (Fst);
      Count_Lst : Count_Type := To_Count (Lst);

   begin
      for J in Count_Fst .. Count_Lst loop
         if Get (Container.Content, J) /= Item then
            return False;
         end if;
      end loop;
      return True;
   end Constant_Range;

   --------------
   -- Contains --
   --------------

   function Contains
     (Container : Sequence;
      Fst       : Big_Positive;
      Lst       : Big_Natural;
      Item      : Element_Type) return Boolean
   is
      Count_Fst : Count_Type := To_Count (Fst);
      Count_Lst : Count_Type := To_Count (Lst);

   begin
      for J in Count_Fst .. Count_Lst loop
         if Get (Container.Content, J) = Item then
            return True;
         end if;
      end loop;
      return False;
   end Contains;

   --------------------
   -- Empty_Sequence --
   --------------------

   function Empty_Sequence return Sequence is
      (Content => <>);

   ------------------
   -- Equal_Except --
   ------------------

   function Equal_Except
     (Left     : Sequence;
      Right    : Sequence;
      Position : Big_Positive) return Boolean
   is
      Count_Pos : Count_Type := To_Count (Position);
      Count_Lst : Count_Type := To_Count (Last (Left));

   begin
      if Length (Left) /= Length (Right) then
         return False;
      end if;

      for J in 1 .. Count_Lst loop
         if J /= Count_Pos then
            if Get (Left.Content, J) /= Get (Right.Content, J) then
               return False;
            end if;
         end if;
      end loop;

      return True;
   end Equal_Except;

   ------------------
   -- Equal_Except --
   ------------------

   function Equal_Except
     (Left  : Sequence;
      Right : Sequence;
      X     : Big_Positive;
      Y     : Big_Positive) return Boolean
   is
      Count_X   : Count_Type := To_Count (X);
      Count_Y   : Count_Type := To_Count (Y);
      Count_Lst : Count_Type := To_Count (Last (Left));

   begin
      if Length (Left) /= Length (Right) then
         return False;
      end if;

      for J in 1 .. Count_Lst loop
         if (J /= Count_X and J /= Count_Y) then
            if Get (Left.Content, J) /= Get (Right.Content, J) then
               return False;
            end if;
         end if;
      end loop;

      return True;
   end Equal_Except;

   ---------
   -- Get --
   ---------

    function Get
     (Container : Sequence;
      Position  : Big_Positive) return Element_Type is
     (Get (Container.Content, To_Count (Position)));

   ----------
   -- Last --
   ----------

   function Last (Container : Sequence) return Big_Natural is
      (Length (Container));

   ------------
   -- Length --
   ------------

   function Length (Container : Sequence) return Big_Natural is
     (Big (Length (Container.Content)));

   -----------------
   -- Range_Equal --
   -----------------

    function Range_Equal
     (Left  : Sequence;
      Right : Sequence;
      Fst   : Big_Positive;
      Lst   : Big_Natural) return Boolean
   is
      Count_Fst : Count_Type := To_Count (Fst);
      Count_Lst : Count_Type := To_Count (Lst);

   begin
      for J in Count_Fst .. Count_Lst loop
         if Get (Left.Content, J) /= Get (Right.Content, J) then
            return False;
         end if;
      end loop;

      return True;
   end Range_Equal;

   -------------------
   -- Range_Shifted --
   -------------------

   function Range_Shifted
     (Left   : Sequence;
      Right  : Sequence;
      Fst    : Big_Positive;
      Lst    : Big_Natural;
      Offset : Big_Integer) return Boolean
   is
      Count_Fst : Count_Type := To_Count (Fst);
      Count_Lst : Count_Type := To_Count (Lst);

   begin
      for J in Count_Fst .. Count_Lst loop
         if Get (Left.Content, J) /= Get (Right, Big (J) + Offset) then
            return False;
         end if;
      end loop;

      return True;
   end Range_Shifted;

   ------------
   -- Remove --
   ------------

   function Remove
     (Container : Sequence;
      Position : Big_Positive) return Sequence is
     (Content => Remove (Container.Content, To_Count (Position)));

   ---------
   -- Set --
   ---------

   function Set
     (Container : Sequence;
      Position  : Big_Positive;
      New_Item  : Element_Type) return Sequence is
     (Content => Set (Container.Content, To_Count (Position), New_Item));

end Ada.Containers.Functional_Infinite_Sequences;
