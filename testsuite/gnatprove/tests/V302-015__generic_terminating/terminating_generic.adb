pragma SPARK_Mode(On);

procedure Terminating_Generic is
   package Variant_1 is
      package A with Annotate => (GNATprove, Terminating) is
         generic
         package B is
            function Inconsistent return Integer
              with Post => False;
         end B;
      end A;
   end Variant_1;
   package body Variant_1 is
      package body A with SPARK_Mode => Off is
         package body B with SPARK_Mode => Off is
            function Inconsistent return Integer is (0);
         end B;
      end A;
      package C is new A.B;
      function Consistency return Integer is (0)
        with Pre => C.Inconsistent = 0,
        Post => False;
   end Variant_1;

   package Variant_2 is
      package A is
         generic
         package B with Annotate => (GNATprove, Terminating) is
            function Inconsistent return Integer
              with Post => False;
         end B;
      end A;
   end Variant_2;
   package body Variant_2 is
      package body A with SPARK_Mode => Off is
         package body B with SPARK_Mode => Off is
            function Inconsistent return Integer is (0);
         end B;
      end A;
      package C is new A.B;
      function Consistency return Integer is (0)
        with Pre => C.Inconsistent = 0,
        Post => False;
   end Variant_2;
begin
   null;
end;
