private with SXML.Stack;

generic
   Depth : Positive;
package SXML.Generic_Parser with
   Abstract_State => State,
   Initializes    => State
is
   procedure Parse;

private
   type Frame_Type is
      record
         First : Boolean;
      end record;

   package Call_Stack is new SXML.Stack (Frame_Type, (others => True), Depth) with Part_Of => State;

end SXML.Generic_Parser;
