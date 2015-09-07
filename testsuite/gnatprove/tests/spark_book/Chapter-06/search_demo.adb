pragma SPARK_Mode(On);

with Ada.Text_IO;
with Generic_Searchers;

procedure Search_Demo is
   subtype Index_Type is Positive range 1 .. 10;
   type Search_Array_Type is array(Index_Type) of Natural;

   Search_Array : Search_Array_Type := (2, 4, 6, 8, 10, 12, 14, 16, 18, 20);

   procedure Searcher is new
     Generic_Searchers.Binary_Search
       (Element_Type => Natural,
        Index_Type   => Index_Type,
        Array_Type   => Search_Array_Type);

   Found        : Boolean;
   Result_Index : Index_Type;
begin
   Searcher(10, Search_Array, Found, Result_Index);
   if not Found then
      Ada.Text_IO.Put_Line("The value 10 was not found");
   else
      Ada.Text_IO.Put_Line("The value 10 was found at index " & Integer'Image(Result_Index));
   end if;
end Search_Demo;
