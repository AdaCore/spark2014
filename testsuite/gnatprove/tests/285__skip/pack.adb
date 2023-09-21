pragma SPARK_Mode;

package body Pack is
   procedure A is
      procedure AA is
         procedure AAA;
         pragma Annotate (GNATprove, Skip_Proof, AAA);

         procedure AAA is
            procedure AAAA is null;
         begin
            null;
         end AAA;

         procedure AAB
           with Annotate => (GNATprove, Skip_Proof);

         procedure AAB is
            procedure AABA is null;
         begin
            null;
         end AAB;

         procedure AAC
           with Annotate => (GNATprove, Skip_Proof)
         is
            procedure AACA is null;
         begin
            null;
         end AAC;
      begin
         AAA;
         AAB;
         AAC;
      end AA;

      procedure AB is
         procedure ABA;
         pragma Annotate (GNATprove, Skip_Flow_And_Proof, ABA);

         procedure ABA is
            procedure ABAA is null;
         begin
            null;
         end ABA;

         procedure ABB
           with Annotate => (GNATprove, Skip_Flow_And_Proof);

         procedure ABB is
            procedure ABBA is null;
         begin
            null;
         end ABB;

         procedure ABC
           with Annotate => (GNATprove, Skip_Flow_And_Proof)
         is
            procedure ABCA is null;
         begin
            null;
         end ABC;
      begin
         ABA;
         ABB;
         ABC;
      end AB;
   begin
      null;
   end A;
end Pack;
