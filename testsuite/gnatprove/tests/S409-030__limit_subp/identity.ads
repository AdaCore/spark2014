package Identity is

   --  A name is a non-null string of up to 255 characters

   subtype Name_Len is Positive range 1 .. 255;
   subtype Name is String (Name_Len);

   No_Name : constant Name := Name'(others => ' ');

   --  A unique identifier for a customer is a sequence of three numbers, each
   --  one between 0 and 999.

   type Num is range 0 .. 999;
   type Num_Position is (Low, Mid, High);
   type Id is array (Num_Position) of Num;

   No_Id : constant Id := Id'(Low => 0, Mid => 0, High => 0);

end Identity;
