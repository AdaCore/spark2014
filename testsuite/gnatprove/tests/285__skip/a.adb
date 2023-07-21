pragma SPARK_Mode;

package body A is
   procedure U is
      procedure UU is
         procedure UUU;
         pragma Annotate (GNATprove, Skip_Proof, UUU);

         procedure UUU is
            procedure UUUU is null;
         begin
            null;
         end UUU;

         procedure UUU2
           with Annotate => (GNATprove, Skip_Proof);

         procedure UUU2 is
            procedure UUUU2 is null;
         begin
            null;
         end UUU2;

         procedure UUU3
           with Annotate => (GNATprove, Skip_Proof)
         is
            procedure UUUU3 is null;
         begin
            null;
         end UUU3;
      begin
         UUU;
         UUU2;
         UUU3;
      end UU;

      procedure UU2 is
         procedure UUU;
         pragma Annotate (GNATprove, Skip_Flow_And_Proof, UUU);

         procedure UUU is
            procedure UUUU is null;
         begin
            null;
         end UUU;

         procedure UUU2
           with Annotate => (GNATprove, Skip_Flow_And_Proof);

         procedure UUU2 is
            procedure UUUU2 is null;
         begin
            null;
         end UUU2;

         procedure UUU3
           with Annotate => (GNATprove, Skip_Flow_And_Proof)
         is
            procedure UUUU3 is null;
         begin
            null;
         end UUU3;
      begin
         UUU;
         UUU2;
         UUU3;
      end UU2;
   begin
      null;
   end U;
end A;
