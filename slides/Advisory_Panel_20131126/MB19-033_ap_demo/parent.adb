pragma SPARK_Mode;
with System.Storage_Elements;
with Parent.Child;
package body Parent
is
   pragma Warnings (Off);
   package Child1 is new Parent.Child (System.Storage_Elements.Integer_Address (16#DEADBED0#));
   package Child2 is new Parent.Child (System.Storage_Elements.Integer_Address (16#DEADBEE0#));
   package Child3 is new Parent.Child (System.Storage_Elements.Integer_Address (16#DEADBEF0#));
   pragma Warnings (On);

   function Read_Switch return Switch_Pos
   is
      type On_Off_Count is range 0 .. 3;
      On_Count  : On_Off_Count := 0;
      Off_Count : On_Off_Count := 0;
   begin
      case Child1.Read_Switch is
         when On  => On_Count := On_Count + 1;
         when Off => On_Count := Off_Count + 1;
         when Unknown => null;
      end case;
      case Child2.Read_Switch is
         when On  => On_Count := On_Count + 1;
         when Off => On_Count := Off_Count + 1;
         when Unknown => null;
      end case;
      case Child3.Read_Switch is
         when On  => On_Count := On_Count + 1;
         when Off => On_Count := Off_Count + 1;
         when Unknown => null;
      end case;

      if On_Count = 3 then
         return On;
      elsif Off_Count = 3 then
         return Off;
      else
         return Unknown;
      end if;

   end Read_Switch;

end Parent;
