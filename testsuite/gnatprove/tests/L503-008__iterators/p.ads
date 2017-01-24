with Ada.Containers.Formal_Doubly_Linked_Lists;

package P is

   type Ar is array (Integer range <>) of Integer;

   procedure Iter_Over_Array (A : Ar);

   procedure Quant_Over_Array(A : in out Ar)
   with Post => (for all X of A => X = 0);
   pragma SPARK_Mode (Off);  --  iteration "for of" on array

   function My_Eq (I1, I2 : Integer) return Boolean is (I1 = I2);

   package My_Lists is new Ada.Containers.Formal_Doubly_Linked_Lists (Integer);
   use My_Lists;

   procedure Iter_Over_Lists (X : My_Lists.List);

   procedure Quant_Over_Lists (X : My_Lists.List);

end P;
