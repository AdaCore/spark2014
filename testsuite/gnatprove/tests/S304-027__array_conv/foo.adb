pragma Spark_Mode (On);

with Interfaces;

procedure Foo
is

   subtype Byte is Interfaces.Unsigned_8;
   type Byte_Array_Type is array (Positive range <>) of Byte;
   subtype My_Elem is Byte;

   type Element_Array_Type is array (Positive range <>) of My_Elem;

   type Element_Structure_Type (Max_Size : Positive) is record
      Index : Natural := 1;
      Items : Element_Array_Type (1 .. Max_Size);
   end record;


   procedure Get
     (Structure : in     Element_Structure_Type;
      Value     :    out Element_Array_Type)
   with
     Pre  => Value'Length = Structure.Max_Size,
     Post => Value = Structure.Items,
       Import;


   Stored_Items : Byte_Array_Type (1 .. 4);
   Structure    : Element_Structure_Type (4);


begin
   Structure.Items := (1, 2, 3, 4);
   Get (Structure, Element_Array_Type (Stored_Items));
end Foo;
