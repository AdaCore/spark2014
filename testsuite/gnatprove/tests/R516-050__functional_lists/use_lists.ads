with Ada.Unchecked_Conversion; with Formal_Doubly_Linked_Lists;
pragma Elaborate_All (Formal_Doubly_Linked_Lists);

package Use_Lists with SPARK_Mode is
   package My_Lists is new Formal_Doubly_Linked_Lists
     (Element_Type => Integer,
      "="          => "=");
   use My_Lists;
   use My_Lists.Model;
   use My_Lists.Model.Cursor_Sequence;
   use My_Lists.Model.Element_Sequence;

   function Is_Incr (I1, I2 : Integer) return Boolean is
      (if I1 = Integer'Last then I2 = Integer'Last else I2 = I1 + 1);

   procedure Add_1 (L1 : List; L2 : out List) with
     Post => Length (L2) = Length (L1)
     and then (for all N in 0 .. Natural (Length (L1)) - 1 =>
                 Is_Incr (Get (Get_Element_Model (L1), N),
                          Get (Get_Element_Model (L2), N)));
end Use_Lists;
