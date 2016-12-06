pragma Profile (Ravenscar);
pragma Partition_Elaboration_Policy (Sequential);

package My_Types with SPARK_Mode is
   subtype My_Range is Integer range 1 .. 5;
   type Rec (X : My_Range) is null record;
   type Priv (X : My_Range) is private;
   protected type Prot (X : My_Range) is
   end Prot;
   task type T (X : My_Range);
private
   pragma SPARK_Mode (Off);
   type Priv (X : My_Range) is null record;
end My_Types;
