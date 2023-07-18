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
      begin
         null;
      end UU;
   begin
      null;
   end U;
end A;
