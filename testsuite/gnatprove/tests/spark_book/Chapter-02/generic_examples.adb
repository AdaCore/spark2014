with Ada.Integer_Text_IO;
with Ada.Text_IO;
procedure Generic_Examples is

   function Count (Source  : in String;
                   Pattern : in Character) return Natural with Global => null is
   -- Returns the number of times Pattern occurs in Source
      Result : Natural := 0;
   begin
      for Index in Source'Range loop
         if Source (Index) = Pattern then
            Result := Result + 1;
         end if;
      end loop;
      return Result;
   end Count;

   -----------------------------------------------------------------------------
   generic
      type Component_Type is private; -- Any type with assignment and equality testing
      type Index_Type     is (<>);    -- Any discrete type
      type Array_Type     is array (Index_Type range <>) of Component_Type;
   function Generic_Count (Source  : in Array_Type;
                           Pattern : in Component_Type) return Natural;
   -- Returns the number of times Pattern occurs in Source

   function Generic_Count (Source  : in Array_Type;
                           Pattern : in Component_Type) return Natural is
      Result : Natural := 0;
   begin
      for Index in Source'Range loop
         if Source (Index) = Pattern  then
            Result := Result + 1;
         end if;
      end loop;
      return Result;
   end Generic_Count;

   function Char_Count is new Generic_Count (Component_Type => Character,
                                             Index_Type     => Positive,
                                             Array_Type     => String);

   type Percent is range 0 .. 100;
   type Percent_Array is array (Character range <>) of Percent;

   function Percent_Count is new Generic_Count (Component_Type => Percent,
                                                Index_Type     => Character,
                                                Array_Type     => Percent_Array);

   -----------------------------------------------------------------------------
   generic
      type Component_Type is limited private; -- Any type
      type Index_Type     is (<>);            -- Any discrete type
      type Array_Type     is array (Index_Type range <>) of Component_Type;
      with function Selected (From_Source  : in Component_Type;
                              Pattern      : in Component_Type) return Boolean;
   procedure Tally (Source  : in Array_Type;
                    Pattern : in Component_Type;
                    Result  : out Natural);
   -- Returns the number of items in Source that are selected for a given Pattern
   -- Calls function Selected to determine if an element in Source qualifies

   procedure Tally (Source  : in Array_Type;
                    Pattern : in Component_Type;
                    Result  : out Natural) is
   begin
      Result := 0;
      for Index in Source'Range loop
         if Selected (Source (Index), Pattern) then
            Result := Result + 1;
         end if;
      end loop;
   end Tally;

   -- Instantiate a procedure to determine how many percentages
   -- in an array indexed by characters are greater than some value
   procedure Tally_Percents is new Tally (Component_Type => Percent,
                                          Index_Type     => Character,
                                          Array_Type     => Percent_Array,
                                          Selected       => ">");


--------------------------------------------------------------------------------
   The_Count   : Natural;
   My_Percents : Percent_Array := (5, 6, 7, 5, 3, 4, 19, 16, 5, 23, 45, 4, 3);

begin

   The_Count := Count (Source  => "How now brown cow",
                       Pattern => 'w');
   Ada.Integer_Text_IO.Put (The_Count);
   Ada.Text_IO.New_Line;


   The_Count := Char_Count (Source  => "How now brown cow",
                            Pattern => 'w');
   Ada.Integer_Text_IO.Put (The_Count);
   Ada.Text_IO.New_Line;

   The_Count := Percent_Count (Source  => My_Percents,
                               Pattern => 5);
   Ada.Integer_Text_IO.Put (The_Count);
   Ada.Text_IO.New_Line;

   -- Determine how many values in My_Percents are greater than 5
   Tally_Percents (Source  => My_Percents,
                   Pattern => 5,
                   Result  => The_Count);
   Ada.Integer_Text_IO.Put (The_Count);
   Ada.Text_IO.New_Line;


end Generic_Examples;
