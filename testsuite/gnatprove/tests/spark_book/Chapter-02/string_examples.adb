with Ada.Text_IO; use Ada.Text_IO;
procedure String_Examples is
  Count : Integer;
subtype Name_String is String (1 .. 20);  -- A constrained array type

Currency : constant String := "Dollars";

Name    : Name_String;       -- A string containing 20 characters
Address : String (1 .. 40);  -- A string containing 40 characters
City    : String (3 .. 22);  -- A string containing 20 characters

begin
Address := (others => ' ');

Name := Address;  -- Illegal Assigning 40 characters to a 20 character string
Name := "Peter";  -- Illegal Assigning  5 characters to a 20 character string
Address := Name;  -- Illegal Assigning 20 characters to a 40 character string

City := Name;               -- Legal Both source and target contain 20 characters
Name := Address (1 .. 20);  -- Legal Both source and target contain 20 characters
Address := Name & Name;     -- Legal Both source and target contain 40 characters
Address (9 .. 28) := Name;  -- Legal Both source and target contain 20 characters

Count := 5;
Name (1 .. Count) := "Peter";
Put (Name (1 .. Count));        -- Display Peter

end String_Examples;
