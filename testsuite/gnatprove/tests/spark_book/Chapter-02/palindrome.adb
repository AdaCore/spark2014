with Ada.Text_IO;
procedure Palindrome is

   function Is_Palindrome (Item : in String) return Boolean is
      Left_Index  : Natural;  -- Two indices mark the beginning and
      Right_Index : Natural;  -- end of the unchecked portion of Item
   begin
      Left_Index  := Item'First;
      Right_Index := Item'Last;
      loop
         exit when Left_Index >= Right_Index or else
                   Item (Right_Index) /= Item (Left_Index);
         Left_Index  := Left_Index + 1;
         Right_Index := Right_Index - 1;
      end loop;
      return Left_Index >= Right_Index;
   end Is_Palindrome;

   Max_Length : constant Positive := 100;
   subtype Line_Type is String (1 .. Max_Length);

   Line  : Line_Type;  -- Characters entered by user
   Count : Natural;    -- Number of characters entered

begin
  Ada.Text_IO.Put_Line ("Enter a line.");
   -- Get_Line reads characters to end of line
   -- Last is the index of the last character read
   Ada.Text_IO.Get_Line (Item => Line,
                         Last => Count);
   -- Slice off garbage before calling Is_Palindrome
   if Is_Palindrome (Line (1 .. Count)) then
      Ada.Text_IO.Put_Line ("is a palindrome");
   else
      Ada.Text_IO.Put_Line ("is not a palindrome");
   end if;
end Palindrome;
