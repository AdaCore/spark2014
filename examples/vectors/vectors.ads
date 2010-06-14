package Vectors is

   type Extended_Index is range 0 .. 10_000;
   type Element_Type   is range 0 .. 100_000;

   subtype Index_Type is Extended_Index range 1 .. Extended_Index'Last;
   subtype Count_Type is Extended_Index;

   No_Index : constant Extended_Index := Extended_Index'First;

   type Vector is private;
   type Cursor is private;

   No_Element : constant Cursor;

   procedure Init_Vector (Container : out Vector);
   --# derives Container from;

   function Length (Container : Vector) return Count_Type;

   function First_Cursor (Container : Vector) return Cursor;

   function Last_Cursor (Container : Vector) return Cursor;

   function Associated
     (Container : Vector;
      Position  : Cursor) return Boolean;

   function Element_At
     (Container : Vector;
      Position  : Cursor) return Element_Type;
   --# pre Associated (Container, Position);

   procedure Next (Position : in out Cursor);
   --# derives Position from Position;

   procedure Replace_Element
     (Container : in out Vector;
      Position  : Cursor;
      New_Item  : Element_Type);
   --# derives Container from Container, Position, New_Item;
   --# pre Associated (Container, Position);

   procedure Insert
     (Container : in out Vector;
      Before    : Cursor;
      New_Item  : Element_Type);
   --# derives Container from Container, Before, New_Item;
   --# pre Associated (Container, Before)
   --#     and then Length (Container) < Index_Type'Last;

   procedure Delete
     (Container : in out Vector;
      Position  : Cursor);
   --# derives Container from Container, Position;
   --# pre Associated (Container, Position);

private

   type Elements_Array is array (Index_Type) of Element_Type;

   type Vector is record
      Id         : Natural;
      Sig        : Positive;
      Elements   : Elements_Array;
      Last_Index : Extended_Index;
   end record;

   type Cursor is record
      Container_Id  : Natural;
      Container_Sig : Natural;
      Last_Index    : Index_Type;
      Index         : Index_Type;
   end record;

   No_Element : constant Cursor := Cursor'(0, 0, 1, 1);

end Vectors;
