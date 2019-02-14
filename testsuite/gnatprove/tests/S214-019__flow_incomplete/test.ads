package Test
with
   Abstract_State => State
is
   procedure Is_Odd
      (Value  : Integer;
       Result : out Boolean)
   with
      Global  => (In_Out => State),
      Post    => Get_State = Result;

   function Get_State return Boolean
   with
      Ghost;

private

   Last : Boolean := False
   with
      Part_Of => State,
      Ghost;

   function Get_State return Boolean
   is (Last);

end Test;
