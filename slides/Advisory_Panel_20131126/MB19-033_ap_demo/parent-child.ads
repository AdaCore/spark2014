with System.Storage_Elements;
-- pragma SPARK_Mode; -- Note that SPARK_Mode is not allowed in generic
                      -- declarations, but instantations may have SPARK_Mode.
private generic
   In_Address : in System.Storage_Elements.Integer_Address;
package Parent.Child
is
   function Read_Switch return Parent.Switch_Pos;
end Parent.Child;
