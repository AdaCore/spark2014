
procedure Test_Annotate with SPARK_Mode is

   function F_2 (X : Integer) return Integer with
     Post => F_2'Result = F_1 (X);
   pragma Annotate (GNATprove, Inline_For_Proof, F_2);

   function F_1 (X : Integer) return Integer is (X);
   pragma Annotate (GNATprove, Inline_For_Proof, F_1);

   function F_2 (X : Integer) return Integer is
   begin
      return X;
   end F_2;

   function F_3 (X : Integer) return Integer with
     Post => F_3'Result = F_1 (X);
   pragma Annotate (GNATprove, Inline_For_Proof, F_3);

   function F_3 (X : Integer) return Integer is
   begin
      return 0;
   end F_3;

   type T is new Integer;

   function "=" (I1, I2 : T) return Boolean is
     (Integer (I1) = Integer (I2));
   pragma Annotate (GNATprove, Inline_For_Proof, "=");

   function F_4 (X : T) return T with
     Post => F_4'Result = X;
   pragma Annotate (GNATprove, Inline_For_Proof, F_4);

   function F_4 (X : T) return T is
   begin
      return X;
   end F_4;

begin
   pragma Assert (F_1 (1) = 1);
   pragma Assert (F_2 (2) = 2);
   pragma Assert (F_4 (4) = 4);
end Test_Annotate;
