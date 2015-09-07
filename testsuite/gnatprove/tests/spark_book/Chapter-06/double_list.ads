generic
   type Element_Type is private;
   Max_Size        : Natural;
   Default_Element : Element_Type;
package Double_List
  with
    Abstract_State    => Internal_List,
    Initializes       => Internal_List,
    Initial_Condition => Size = 0
is
   type Status_Type is (Success, Invalid_Step,
                        Bad_Iterator, Insufficient_Space);
   type Iterator is private;

   procedure Clear
     with
       Global  => (Output => Internal_List),
       Depends => (Internal_List => null),
       Post    => Size = 0;

   procedure Insert_Before (It     : in Iterator;
                            Item   : in Element_Type;
                            Status : out Status_Type)
     with
       Global  => (In_Out => Internal_List),
       Depends => (Internal_List => + (It, Item),
                   Status        => Internal_List);

   function Back return Iterator
     with
       Global => null;

   function Size return Natural
     with
       Global => (Input => Internal_List);

private
   -- Position zero is a sentinel node.
   type Iterator is new Natural range 0 .. Max_Size;
end Double_List;
