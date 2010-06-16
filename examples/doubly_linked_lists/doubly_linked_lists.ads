package Doubly_Linked_Lists is

   type Symmetric_Index is range -10_000 .. 10_000;
   type Element_Type    is range 0 .. 100_000;

   subtype Extended_Index is Symmetric_Index range 0 .. 10_000;
   subtype Index_Type     is Extended_Index range 1 .. Extended_Index'Last;
   subtype Count_Type     is Extended_Index;

   No_Index : constant Extended_Index := Extended_Index'First;

   type List is private;

   --  Cursor is currently defined as a public subtype, as this is required
   --  with the current version of SPARK to be able to quantify over cursors
   subtype Cursor is Extended_Index;

   No_Element : constant Cursor;

   function Length (Container : List) return Count_Type;

   function Is_Empty (Container : List) return Boolean;
   --# return Length (Container) = 0;

   function Empty_List return List;
   --# return Container => Is_Empty (Container);

   --  To_Index gives the index of the cursor Position in the container List.
   --  If Position is not in List, it returns zero.
   --  This is only used for dynamic and static checking, as its requires
   --  following all links in List structure.
   function To_Index
     (Container : List;
      Position  : Cursor) return Extended_Index;
   --# return Idx => Idx <= Length (Container);

   function First_Cursor (Container : List) return Cursor;
   --# return Pos =>
   --#   (Is_Empty (Container) -> To_Index (Container, Pos) = 0)
   --#   and then
   --#   (not Is_Empty (Container) -> To_Index (Container, Pos) = 1);

   function Last_Cursor (Container : List) return Cursor;
   --# return Pos =>
   --#   (Is_Empty (Container) -> To_Index (Container, Pos) = 0)
   --#   and then
   --#   (not Is_Empty (Container) ->
   --#      To_Index (Container, Pos) = Length (Container));

   function Has_Element
     (Container : List;
      Position  : Cursor) return Boolean;
   --# return To_Index (Container, Position) /= 0;

   function Element
     (Container : List;
      Position  : Cursor) return Element_Type;
   --# pre Has_Element (Container, Position);

   procedure Next
     (Container : List;
      Position  : in out Cursor);
   --# derives Position from Container, Position;
   --# pre  Has_Element (Container, Position);
   --# post (Position~ /= Last_Cursor (Container)
   --#       -> To_Index (Container, Position)
   --#         = To_Index (Container, Position~) + 1)
   --#      and then
   --#      (Position~ = Last_Cursor (Container)
   --#       -> To_Index (Container, Position) = 0);

   --  Used in checks, to indicate that Container2 is Container1 with value
   --  New_Item at position Position
   function With_At_Equal
     (Container1 : List;
      Position   : Cursor;
      New_Item   : Element_Type;
      Container2 : List) return Boolean;
   --# return Length (Container2) = Length (Container1)
   --#        and then
   --#        (for all Pos in Cursor =>
   --#          (Has_Element (Container1, Pos)
   --#          -> To_Index (Container2, Pos) = To_Index (Container1, Pos)))
   --#        and then
   --#        (for all Pos in Cursor =>
   --#          ((Has_Element (Container1, Pos)
   --#           and then Pos /= Position)
   --#          -> Element (Container2, Pos) = Element (Container1, Pos)))
   --#        and then
   --#        Element (Container2, Position) = New_Item;

   procedure Replace_Element
     (Container : in out List;
      Position  : Cursor;
      New_Item  : Element_Type);
   --# derives Container from Container, Position, New_Item;
   --# pre  Has_Element (Container, Position);
   --# post With_At_Equal (Container~, Position, New_Item, Container);

   --  Used in checks, to indicate that Container2 is Container1 plus some
   --  value at index Index
   function Plus_Any_At_Equal
     (Container1 : List;
      Index      : Index_Type;
      Container2 : List) return Boolean;
   --# return Length (Container2) = Length (Container1) + 1
   --#        and then
   --#        (for all Pos in Cursor =>
   --#          ((Has_Element (Container1, Pos)
   --#            and then To_Index (Container1, Pos) < Index)
   --#          -> To_Index (Container2, Pos) = To_Index (Container1, Pos)))
   --#        and then
   --#        (for all Pos in Cursor =>
   --#          (((Has_Element (Container1, Pos)
   --#             and then To_Index (Container1, Pos) >= Index)
   --#          ->
   --#          To_Index (Container2, Pos) = To_Index (Container1, Pos) + 1)))
   --#        and then
   --#        (for all Pos in Cursor =>
   --#          (Has_Element (Container1, Pos)
   --#          -> Element (Container2, Pos) = Element (Container1, Pos)));

   --  Used in checks, to indicate that Container2 is Container1 plus value
   --  New_Item at index Index
   function Plus_At_Equal
     (Container1 : List;
      Index      : Index_Type;
      New_Item   : Element_Type;
      Container2 : List) return Boolean;
   --# return Plus_Any_At_Equal (Container1, Index, Container2)
   --#        and then
   --#        (for all Pos in Cursor =>
   --#          (To_Index (Container2, Pos) = Index
   --#          -> Element (Container2, Pos) = New_Item));

   procedure Insert
     (Container : in out List;
      Before    : Cursor;
      New_Item  : Element_Type);
   --# derives Container from Container, Before, New_Item;
   --# pre  Has_Element (Container, Before)
   --#      and then Length (Container) < Index_Type'Last;
   --# post Plus_At_Equal (Container~,
   --#        To_Index (Container~, Before), New_Item, Container);

   procedure Delete
     (Container : in out List;
      Position  : Cursor);
   --# derives Container from Container, Position;
   --# pre  Has_Element (Container, Position);
   --# post Plus_Any_At_Equal (Container,
   --#        To_Index (Container~, Position), Container~);

private

   type Node_Array is array (Index_Type) of Element_Type;

   type List is record
      Nodes  : Node_Array;
      Free   : Symmetric_Index;
      First  : Count_Type;
      Last   : Count_Type;
      Length : Count_Type;
   end record;

   No_Element : constant Cursor := Cursor'(0);

end Doubly_Linked_Lists;
