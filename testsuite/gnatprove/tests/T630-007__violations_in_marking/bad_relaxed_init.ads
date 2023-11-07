pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);
package Bad_Relaxed_Init with SPARK_Mode is
   type My_Int is new Integer with Relaxed_Initialization;
   protected Prot is
      function Get return Integer;
   private
      Data    : My_Int := 1;
      Present : Boolean := True;
   end;

   X : My_Int := 1 with Part_Of => Prot;

   protected type Prot_Ty is
      function Get return Integer;
   private
      Data : Integer := 1;
   end;

   type Rel_Prot_Ty is new Prot_Ty with Relaxed_Initialization;

   type Root is tagged record
      F : My_Int; -- OK in roots of tagged hierarchy
   end record;

   type Child is new Root with record
      G : My_Int; -- Relaxed components are not allowed in derived types
   end record;

   type Root2 is tagged record
      F : Integer;
   end record with
     Relaxed_Initialization;

   type My_Acc is access My_Int;
   type My_Acc_2 is access Integer with Relaxed_Initialization;
   type My_Acc_3 is access function return Integer with Relaxed_Initialization;
   type My_Acc_4 is access Root with Relaxed_Initialization;

   protected type Prot_Ty2 is
      function Get return Integer;
   private
      Data : My_Acc;
   end;

   type Priv is private with Relaxed_Initialization;

private
   type Priv is record
      F, G : Integer := 0;
   end record with
     Invariant => F <= G;
end Bad_Relaxed_Init;
