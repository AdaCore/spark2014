--  Unbounded lists of unconstrained elements.
--  Cursors are indexes into an array, to be able to write post-conditions
--  and for added safety

generic
   type Element_Type (<>) is private;
   --  Element_Type must not be a controlled type that needs to be
   --  Adjusted when it is moved in memory, since the list will use the
   --  realloc() system call.

   Enable_Asserts : Boolean := False;

package Conts.Lists.Indefinite_Unbounded_SPARK with SPARK_Mode is

   package Elements is new Indefinite_Elements_Traits_SPARK (Element_Type);
   package Nodes is new SPARK_Unbounded_List_Nodes_Traits
      (Elements              => Elements.Elements,
       Controlled_Or_Limited => Limited_Base_List);
   package Lists is new Generic_Lists
      (Nodes          => Nodes.Nodes,
       Enable_Asserts => Enable_Asserts);

   subtype Cursor is Lists.Cursor;
   type List is new Lists.List with null record
      with Iterable => (First       => First_Primitive,
                        Next        => Next_Primitive,
                        Has_Element => Has_Element_Primitive,
                        Element     => Element_Primitive);

   function Copy (Self : List'Class) return List'Class;
   --  Return a deep copy of Self
   --  Complexity: O(n)

   package Cursors is new List_Cursors (Lists, List);
end Conts.Lists.Indefinite_Unbounded_SPARK;
