pragma Partition_Elaboration_Policy (Sequential);
pragma Profile (Ravenscar);

with Ada.Interrupts.Names;

package GNAT_Bug
  with SPARK_Mode
is

   protected type Example_PT
   is
      procedure Test;

   private
      procedure IRQ_Handler
        with Attach_Handler => Ada.Interrupts.Names.SIGHUP;

   end Example_PT;

   PO : Example_PT;

end GNAT_Bug;
