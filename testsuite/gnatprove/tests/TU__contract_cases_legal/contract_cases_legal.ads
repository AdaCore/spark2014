pragma Assertion_Policy (Contract_Cases => Ignore);

package Contract_Cases_Legal
  with SPARK_Mode
is
   --  TU: 3. A Contract_Cases aspect is an assertion (as defined in RM
   --  11.4.2(1.1/3)); its assertion expressions are as described below.
   --  Contract_Cases may be specified as an ``assertion_aspect_mark`` in an
   --  Assertion_Policy pragma.

   Threshold : Integer := 1000;

   procedure Incr_Threshold1 (X : in out Integer)
     with Pre  => X >= 0,
          Post => X = Integer'Min (X'Old + 1, Threshold);

   procedure Incr_Threshold2 (X : in out Integer)
     with Contract_Cases => (X < Threshold  => X = X'Old + 1,
                             X >= Threshold => X = X'Old);

   procedure Incr_Threshold3 (X : in out Integer)
     with Pre            => X >= 0,
          Post           => X >= X'Old,
          Contract_Cases => (X < Threshold  => X = X'Old + 1,
                             X >= Threshold => X = X'Old);

   procedure Incr_Threshold4 (X : in out Integer)
     with Pre  => (X < Threshold and not (X >= Threshold))
                   or else (not (X < Threshold) and X >= Threshold),
          Post => (if X'Old < Threshold'Old then X = X'Old + 1
                   elsif X'Old >= Threshold'Old then X = X'Old);
end Contract_Cases_Legal;