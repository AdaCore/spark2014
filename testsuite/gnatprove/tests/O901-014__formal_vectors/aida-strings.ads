with Ada.Strings.Unbounded;
with Ada.Strings.Wide_Unbounded;

package Aida.Strings is
   pragma Preelaborate;

   type Unbounded_String_Type;
   type Unbounded_Wide_String_Type;

   function To_String (Value : Integer) return String;

   function Trim (Text : String) return String;

   generic
      Maximum_Length_Of_Bounded_String : Positive;
   package Generic_Bounded_String_Type_Owner is
      pragma SPARK_Mode;

      type Bounded_String_Type;

      subtype Length_Type is Natural range 0 .. Maximum_Length_Of_Bounded_String;

      Out_Of_Bounds_Exception : exception;

      type Bounded_String_Type is tagged private;

      procedure Initialize (This : out Bounded_String_Type;
                            Text : String) with
        Pre'Class => Text'Length <= Maximum_Length_Of_Bounded_String;

      procedure Initialize (This                 : out Bounded_String_Type;
                            Text                 : String;
                            Has_Truncated_String : out Boolean);

      function To_String (This : Bounded_String_Type) return String;

      function Length (This : Bounded_String_Type) return Length_Type;

      function Equals (This   : Bounded_String_Type;
                       Object : String) return Boolean;

      function "="(Left, Right : Bounded_String_Type) return Boolean;

   private

      type Bounded_String_Type is tagged
         record
            Text        : String (1 .. Maximum_Length_Of_Bounded_String) := (others => ' ');
            Text_Length : Length_Type := 0;
         end record;

      function Length (This : Bounded_String_Type) return Length_Type is (This.Text_Length);

   end Generic_Bounded_String_Type_Owner;

   type Unbounded_String_Type is tagged private;

   procedure Initialize (This : out Unbounded_String_Type;
                         Text : String);

   function To_String (This : Unbounded_String_Type) return String;

   procedure Append (This : in out Unbounded_String_Type;
                     Text : in     String);

   function Length (This : Unbounded_String_Type) return Natural;

   function Starts_With (This         : Unbounded_String_Type;
                         Searched_For : String) return Boolean;

   procedure Substring (This        : Unbounded_String_Type;
                        Begin_Index : Natural;
                        Result      : out Unbounded_String_Type);

   function Contains_Substring (This         : Unbounded_String_Type;
                                Searched_For : String) return Boolean;

   procedure Find_First_Index (This          : in Unbounded_String_Type;
                               To_Search_For : in String;
                               Found_Index   : out Natural;
                               Has_Found     : out Boolean);

   function Equals (This   : Unbounded_String_Type;
                    Object : Unbounded_String_Type) return Boolean;

   function Equals (This   : Unbounded_String_Type;
                    Object : String) return Boolean;

   function "="(Left, Right : Unbounded_String_Type) return Boolean;

   type Unbounded_Wide_String_Type is tagged private;

   procedure Set_To_Standard_String (This : out Unbounded_Wide_String_Type;
                                     Text : String);

   procedure Set_To_Standard_Wide_String (This : out Unbounded_Wide_String_Type;
                                          Text : Wide_String);

   procedure Set_To_Standard_Trimmed_Wide_String (This : out Unbounded_Wide_String_Type;
                                                  Text : Wide_String);

   function To_String (This : Unbounded_Wide_String_Type) return String;

   function To_Wide_String (This : Unbounded_Wide_String_Type) return Wide_String;

   function "="(Left, Right : Unbounded_Wide_String_Type) return Boolean;

private

   type Unbounded_String_Type is tagged
      record
         Unbounded_Text : Ada.Strings.Unbounded.Unbounded_String;
      end record;

   type Unbounded_Wide_String_Type is tagged
      record
         Unbounded_Text : Ada.Strings.Wide_Unbounded.Unbounded_Wide_String;
      end record;

end Aida.Strings;
