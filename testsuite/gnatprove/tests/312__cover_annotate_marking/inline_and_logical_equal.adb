procedure Inline_And_Logical_Equal with SPARK_Mode is

   --  Logical_Equal/Inline_For_Proof are incompatible
   
   function Log_Eq (X : Integer; Y : Integer) return Boolean is (X = Y);
   pragma Annotate (GNATprove, Inline_For_Proof, Log_Eq);
   pragma Annotate (GNATprove, Logical_Equal, Log_Eq);

   function Log_Eq_Alt (X : Integer; Y : Integer) return Boolean is (X = Y);
   pragma Annotate (GNATprove, Logical_Equal, Log_Eq_Alt);
   pragma Annotate (GNATprove, Inline_For_Proof, Log_Eq_Alt);

   --  Inline_For_Proof requires body to be in SPARK.
   
   package A is
      function F (X : Integer) return Integer
        with Annotate => (GNATprove, Inline_For_Proof);
   private
      pragma SPARK_Mode (Off);
      function F (X : Integer) return Integer is (X);
   end A;
   
begin
   null;
end Inline_And_Logical_Equal;
