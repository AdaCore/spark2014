with Values;

package Prop
is

   function Get_Val return Integer
   with
      Global => Values.Val;

end Prop;
