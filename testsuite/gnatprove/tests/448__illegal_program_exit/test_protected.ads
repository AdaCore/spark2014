pragma Profile (Jorvik);
pragma Partition_Elaboration_Policy (Sequential);

package Test_Protected is

   --  Check that we reject self reference of protected operations in
   --  Program_Exit.

   protected type Prot is
      function Get return Integer;

      --  Both Set and Do_Nothing are considered to have the self reference as
      --  an implicit in out parameter.

      procedure Set (I : Integer) with
        Program_Exit => Get = I;

      procedure Do_Nothing (I : Integer) with
        Program_Exit => Get = I;
   private
      X : Integer := 0;
   end Prot;

end Test_Protected;
