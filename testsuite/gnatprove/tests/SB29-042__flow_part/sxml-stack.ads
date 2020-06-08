generic
   type Element_Type is private;
   Null_Element : Element_Type;
   Size         : Natural;
package SXML.Stack with
  Abstract_State => State,
  Initializes    => State
is
   procedure Init;
end SXML.Stack;
