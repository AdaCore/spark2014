package body Loop_Related_Legal is
   type Array_T is array (Natural range 1 .. 10) of Natural;


   procedure Loop_Entry_And_Quantified_Expressions (Arr : in out Array_T) is
   begin
      for N in Array_T'Range loop
         if Arr (N) < Natural'Last then
            Arr (N) := Arr (N) + 1;
         end if;
         pragma Loop_Invariant
           (for all I in Array_T'Range => Arr (I) >= Arr'Loop_Entry (I));
      end loop;
   end Loop_Entry_And_Quantified_Expressions;


   procedure Loop_Invariant_In_Block_Statement (Par : in out Natural)
     with Pre => Par > 0
   is
   begin
      loop
         declare
            X : Natural;
         begin
            X := 0;
            pragma Loop_Invariant (Par > X);
            pragma Loop_Variant (Decreases => Par);
         end;
         Par := Par - 1;
         exit when Par <= 0;
      end loop;
   end Loop_Invariant_In_Block_Statement;
end Loop_Related_Legal;
