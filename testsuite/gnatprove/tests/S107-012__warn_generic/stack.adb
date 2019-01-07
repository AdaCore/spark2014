

package body Stack with SPARK_Mode => On is

   ----------
   -- Size --
   ----------

   function Size (Stack : Stack_Type) return Index_Type is
   begin
      return Stack.Top;
   end Size;

   ---------------
   -- Construct --
   ---------------

   function Construct return Stack_Type is
      Stack : constant Stack_Type :=
                (Top => 0, Data => (others => Default_Value));
   begin
      return Stack;
   end Construct;

end Stack;

