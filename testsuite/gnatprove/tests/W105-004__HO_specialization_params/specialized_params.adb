procedure Specialized_Params
  with
    SPARK_Mode => On
is

   function Call_Proc (F : not null access function return Integer;
                       P : not null access procedure (X : in out Integer)) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization);

   function Call_Proc (F : not null access function return Integer;
                       P : not null access procedure (X : in out Integer)) return Integer is
      X : Integer := F.all;
   begin
      P (X);
      return X;
   end Call_Proc;

   type Fun_Acc is access function return Integer;

   function Call_Named (F1 : not null access function return Integer; F2 : not null Fun_Acc) return Integer with
     Annotate => (GNATprove, Higher_Order_Specialization);

   function Call_Named (F1 : not null access function return Integer; F2 : not null Fun_Acc) return Integer is
   begin
      return F2.all + F1.all;
   end Call_Named;

   V : Integer := 0;

   function Read_V return Integer is (V) with Pre => V >= 0;
   function Cst_1 return Integer is (1);

   procedure Swap_V (X : in out Integer) is
      Tmp : constant Integer := X;
   begin
      X := V;
      V := Tmp;
   end Swap_V;

   I : Integer;
begin
   --  Access-to-procedure parameters cannot be specialized
   I := Call_Proc (Cst_1'Access, Swap_V'Access);
   --  Named access-to-function parameters cannot be specialized
   I := Call_Named (Cst_1'Access, Read_V'Access);
end Specialized_Params;
