generic
package Test.Child
with
  Abstract_State => State,
  Initializes    => State,
  Elaborate_Body
is

   type Elem_Array is array (Range_Type) of Elem_Type;

   -----------------------------------------------------------------------------

   function Used (Index : Range_Type) return Boolean
   with
      Global => (Input => State);

   function Kind (Index : Range_Type) return Boolean
   with
      Global => (Input => State);

private

   Elems : Elem_Array
     := (others => Elem_Type'(Kind => False))
   with
      Part_Of => State;

   Last_Allocated : Range_Type := Range_Type'First
   with
      Part_Of => State;

   -----------------------------------------------------------------------------

   function Used (Index : Range_Type) return Boolean
   is (Index <= Last_Allocated)
   with
      Refined_Global => (Input => Last_Allocated);

   -----------------------------------------------------------------------------

   function Kind (Index : Range_Type) return Boolean
   is (Elems (Index).Kind)
   with
      Refined_Global => (Input => Elems);

end Test.Child;
