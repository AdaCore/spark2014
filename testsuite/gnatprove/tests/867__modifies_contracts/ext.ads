pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);

package Ext with SPARK_Mode is
   type R is record
      F, G : Integer;
   end record;

   protected type T_1 is
      procedure P (X : in out R) with
        Modifies => X.F;
   private
      C : Integer := 0;
   end T_1;

   protected P is
      procedure P (X : in out R) with
        Modifies => X.F;
   end P;

   Part_Of_V : Integer := 0 with Part_Of => P;
end Ext;
