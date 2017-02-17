
package Pack is
   subtype Fixed_String is String (1 .. 15);

   type Rec is record
      Label : Fixed_String  := (others => ' ');
   end record;

end Pack;
