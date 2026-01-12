with Ada.Unchecked_Conversion;

package Bad_UC with SPARK_Mode is

   protected type Prot is  --<<<<<<  The error is located here
      function F return Integer;
   private
      X : Integer := 0;
   end Prot;
   function Prot_To_Int is new Ada.Unchecked_Conversion (Prot, Integer);

   function Int_To_Prot is new Ada.Unchecked_Conversion (Integer, Prot);
end Bad_UC;
