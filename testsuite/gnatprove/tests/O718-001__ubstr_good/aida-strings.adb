with Ada.Characters.Conversions;
with Ada.Strings.Fixed;
with Ada.Strings.Wide_Fixed;

package body Aida.Strings is
   use type Ada.Strings.Unbounded.Unbounded_String;
   use type Ada.Strings.Wide_Unbounded.Unbounded_Wide_String;

   function To_String (Value : Integer) return String is
   begin
      return Ada.Strings.Fixed.Trim (Source => Integer'Image (Value),
                                     Side   => Ada.Strings.Both);
   end To_String;

   function To_String (Value : Long_Integer_Type) return String is
   begin
      return Ada.Strings.Fixed.Trim (Source => Long_Integer_Type'Image (Value),
                                     Side   => Ada.Strings.Both);
   end To_String;

   function Trim (Text : String) return String is
   begin
      return Ada.Strings.Fixed.Trim (Source => Text,
                                     Side   => Ada.Strings.Both);
   end Trim;

   package body Generic_Bounded_String_Type_Owner is
      pragma SPARK_Mode;

      procedure Initialize (This : out Bounded_String_Type;
                            Text : String) with SPARK_Mode is
      begin
         if Text'Length > Maximum_Length_Of_Bounded_String then
            raise Out_Of_Bounds_Exception;
         end if;

         This.Text := (others => ' ');

         for I in Integer range 1..Text'Length loop
            This.Text (I) := Text (Text'First - 1 + I);
            pragma Loop_Invariant (for all J in Integer range 1..I => This.Text (J) = Text (Text'First - 1 + J));
         end loop;

         This.Text_Length := Text'Length;
      end Initialize;

      procedure Initialize (This                 : out Bounded_String_Type;
                            Text                 : String;
                            Has_Truncated_String : out Boolean)
      is
         Text_Length : constant Integer := Text'Length;
      begin
--           Ada.Strings.Fixed.Move (Source  => Text,
--                                   Target  => This.Text,
--                                   Drop    => Ada.Strings.Right);
         This.Text := (others => ' ');

         if Text_Length > Maximum_Length_Of_Bounded_String then
            for I in Integer range 1..Maximum_Length_Of_Bounded_String loop
               This.Text (I) := Text (Text'First - 1 + I);
            end loop;

            Has_Truncated_String := True;
            This.Text_Length := Maximum_Length_Of_Bounded_String;
         else
            for I in Integer range 1..Text_Length loop
               This.Text (I) := Text (Text'First - 1 + I);
            end loop;

            Has_Truncated_String := False;
            This.Text_Length := Text'Length;
         end if;
      end Initialize;

      function To_String (This : Bounded_String_Type) return String is (This.Text(1 .. This.Text_Length));

      function Equals (This   : Bounded_String_Type;
                       Object : String) return Boolean is
      begin
         return This.To_String = Object;
      end Equals;

      function "="(Left, Right : Bounded_String_Type) return Boolean is
      begin
         if Left.Text_Length = Right.Text_Length then
            if Left.Text_Length = 0 then
               return True;
            end if;

            return Left.To_String = Right.To_String;
         end if;

         return False;
      end "=";

   end Generic_Bounded_String_Type_Owner;

   procedure Initialize (This : out Unbounded_String_Type;
                         Text : String) is
   begin
      Ada.Strings.Unbounded.Set_Unbounded_String (Target => This.Unbounded_Text,
                                                  Source => Text);
   end Initialize;

   function To_String (This : Unbounded_String_Type) return String is (Ada.Strings.Unbounded.To_String (This.Unbounded_Text));

   procedure Append (This : in out Unbounded_String_Type;
                     Text : in     String) is
   begin
      Ada.Strings.Unbounded.Append (Source   => This.Unbounded_Text,
                                    New_Item => Text);
   end Append;

   procedure Append (This : in out Unbounded_String_Type;
                     C    : in     Character) is
   begin
      Ada.Strings.Unbounded.Append (Source   => This.Unbounded_Text,
                                    New_Item => (1 => C));
   end Append;

   function Starts_With (This         : Unbounded_String_Type;
                         Searched_For : String) return Boolean is
   begin
      if Searched_For'Length > Ada.Strings.Unbounded.Length (This.Unbounded_Text) then
         return False;
      end if;

      -- There must exist a nicer way than the following:
      declare
         Source : constant String := Ada.Strings.Unbounded.To_String (This.Unbounded_Text);
      begin
         for Index in Positive range 1..Searched_For'Length loop
            if Source (Index) /= Searched_For (Index) then
               return False;
            end if;
         end loop;
         return True;
      end;
   end Starts_With;

   function Equals (This   : Unbounded_String_Type;
                    Object : Unbounded_String_Type) return Boolean is
   begin
      return This.Unbounded_Text = Object.Unbounded_Text;
   end Equals;

   function Equals (This   : Unbounded_String_Type;
                    Object : String) return Boolean is
   begin
      return This.To_String = Object;
   end Equals;

   function "="(Left, Right : Unbounded_String_Type) return Boolean is
   begin
      return Left.Unbounded_Text = Right.Unbounded_Text;
   end "=";

   function Element (This  : Unbounded_String_Type;
                     Index : Positive) return Character is
   begin
      return Ada.Strings.Unbounded.Element (Source => This.Unbounded_Text,
                                            Index  => Index);
   end Element;

   function Length (This : Unbounded_String_Type) return Natural is
   begin
      return Ada.Strings.Unbounded.Length (This.Unbounded_Text);
   end Length;

   procedure Substring (This        : Unbounded_String_Type;
                        Begin_Index : Natural;
                        Result      : out Unbounded_String_Type) is
   begin
      Result.Unbounded_Text := Ada.Strings.Unbounded.Unbounded_Slice (Source => This.Unbounded_Text,
                                                                      Low    => Begin_Index,
                                                                      High   => This.Length);
   end Substring;

   function Contains_Substring (This         : Unbounded_String_Type;
                                Searched_For : String) return Boolean
   is
      Text : constant String := This.To_String;
   begin
      if Searched_For'Length > This.Length then
         return False;
      end if;

      if Searched_For'Length = 0 then
         return False;
      end if;

      for I in Integer range Text'First .. (Text'Last - Searched_For'Length + 1) loop
         declare
            Has_Found_Match : Boolean := True;
         begin
            for J in Integer range Searched_For'First .. Searched_For'Last loop
               if Text (I + J - Searched_For'First) /= Searched_For (J) then
                  Has_Found_Match := False;
                  exit;
               end if;
            end loop;

            if Has_Found_Match then
               return True;
            end if;
         end;
      end loop;

      return False;
   end Contains_Substring;

   procedure Find_First_Index (This          : in Unbounded_String_Type;
                               To_Search_For : in String;
                               Found_Index   : out Natural;
                               Has_Found     : out Boolean) is
   begin
      Found_Index := Ada.Strings.Unbounded.Index (Source  => This.Unbounded_Text,
                                                  Pattern => To_Search_For);

      if Found_Index = 0 then
         Has_Found := False;
         Found_Index := 0;
      else
         Has_Found := True;
      end if;
   end Find_First_Index;

   procedure Replace (This : in out Unbounded_String_Type;
                      From : in     Character;
                      To   : in     Character) is
   begin
      for I in Positive range 1..This.Length loop
         if Ada.Strings.Unbounded.Element (Source => This.Unbounded_Text,
                                           Index  => I) = From then
            Ada.Strings.Unbounded.Replace_Element (Source => This.Unbounded_Text,
                                                   Index  => I,
                                                   By     => To);
         end if;
      end loop;
   end Replace;

   procedure Set_To_Standard_String (This : out Unbounded_Wide_String_Type;
                                     Text : String) is
   begin
      This.Unbounded_Text := Ada.Strings.Wide_Unbounded.To_Unbounded_Wide_String (Ada.Characters.Conversions.To_Wide_String (Text));
   end Set_To_Standard_String;

   procedure Set_To_Standard_Wide_String (This : out Unbounded_Wide_String_Type;
                                          Text : Wide_String) is
   begin
      This.Unbounded_Text := Ada.Strings.Wide_Unbounded.To_Unbounded_Wide_String (Text);
   end Set_To_Standard_Wide_String;

   procedure Set_To_Standard_Trimmed_Wide_String (This : out Unbounded_Wide_String_Type;
                                          Text : Wide_String) is
   begin
      This.Unbounded_Text := Ada.Strings.Wide_Unbounded.To_Unbounded_Wide_String (Ada.Strings.Wide_Fixed.Trim (Source => Text,
                                                                                                               Side   => Ada.Strings.Both));
   end Set_To_Standard_Trimmed_Wide_String;

   function To_String (This : Unbounded_Wide_String_Type) return String is
   begin
      return Ada.Characters.Conversions.To_String (Ada.Strings.Wide_Unbounded.To_Wide_String (This.Unbounded_Text));
   end To_String;

   function To_Wide_String (This : Unbounded_Wide_String_Type) return Wide_String is
   begin
      return Ada.Strings.Wide_Unbounded.To_Wide_String (This.Unbounded_Text);
   end To_Wide_String;

   function "="(Left, Right : Unbounded_Wide_String_Type) return Boolean is
   begin
      return Left.Unbounded_Text = Right.Unbounded_Text;
   end "=";

end Aida.Strings;
