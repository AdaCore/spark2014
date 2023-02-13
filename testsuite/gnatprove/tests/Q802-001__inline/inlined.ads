package Inlined with SPARK_Mode is
   function F_2 (X : Integer) return Integer with
     Post => F_2'Result = F_1 (X);
   pragma Annotate (GNATprove, Inline_For_Proof, F_2);

   function F_1 (X : Integer) return Integer is (X);
   pragma Annotate (GNATprove, Inline_For_Proof, F_1);

   function F_3 (X : Integer) return Integer with
     Post => F_3'Result = F_1 (X);
   pragma Annotate (GNATprove, Inline_For_Proof, F_3);

   type T is new Integer;

   function "=" (I1, I2 : T) return Boolean is
     (Integer (I1) = Integer (I2));
   pragma Annotate (GNATprove, Inline_For_Proof, "=");

   function F_4 (X : T) return T with
     Post => F_4'Result = X;
   pragma Annotate (GNATprove, Inline_For_Proof, F_4);

end Inlined;
